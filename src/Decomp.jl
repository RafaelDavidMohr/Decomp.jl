module Decomp

include("oscar_util.jl")
using AbstractTrees

export decomp

mutable struct DecompNode
    ideal::POLI
    nonzero::Vector{POL}
    remaining::Vector{POL}
    parent::Union{Nothing, DecompNode}
    parentnonzero::Bool
    ann_cashe::Dict{POL, Vector{POL}}
    nonzero_children::Vector{DecompNode}
    zero_children::Vector{DecompNode}
end

AbstractTrees.childtype(::DecompNode) = DecompNode

function AbstractTrees.children(node::DecompNode)
    vcat(node.nonzero_children, node.zero_children)
end

AbstractTrees.ParentLinks(::Type{DecompNode}) = StoredParents()
AbstractTrees.parent(node::DecompNode) = node.parent

AbstractTrees.NodeType(::Type{DecompNode}) = HasNodeType()
AbstractTrees.nodetype(::Type{DecompNode}) = DecompNode

function inter!(node::DecompNode)

    f = popfirst!(node.remaining)
    println("intersecting with $f over component with $(length(node.nonzero)) nz conditions")
    G = anncashed!(node, f, onlyneedone = true)

    if isempty(G)
        # f regular
        println("is regular")
        return [zero!(node, [f])]
    elseif iszero(total_degree(first(G)))
        # f vanishes
        println("vanishes")
        return [node]
    else # we split
        for g in G
            H = anncashed!(node, g)
            iszero(total_degree(first(H))) && continue
            println("splitting along $(g)")
            reduce_generators_size!(node.ideal, H)

            println("$(length(H)) zero divisors")
            new_nodes = nonzero_presplit!(node, H, f)
            high_dim = zero!(node, H)
            res = vcat([high_dim], new_nodes)
            println("$(length(res)) new components")
            return res
        end
    end
    return DecompNode[]
end

function decomp(sys::Vector{POL})

    isempty(sys) && error("system is empty")
    
    R = parent(first(sys))
    sat_ring, vars = PolynomialRing(base_ring(R),
                                    pushfirst!(["y$(i)" for i in 1:ngens(R)], "t"))
    F = hom(R, sat_ring, vars[2:end])
    F_inv = hom(sat_ring, R, [zero(R), gens(R)...])
    
    initial_node = DecompNode(ideal(sat_ring, F(first(sys))),
                              POL[], [F(p) for p in sys[2:end]],
                              nothing, true, Dict{POL, Vector{POL}}(),
                              DecompNode[], DecompNode[])

    all_processed = all(nd -> isempty(nd.remaining), Leaves(initial_node))
    while !all_processed 
        for node in Leaves(initial_node)
            isempty(node.remaining) && continue
            if sat_ring(1) in node.ideal
                empty!(node.remaining)
                continue
            end
            inter!(node)
            all_processed = all(nd -> isempty(nd.remaining),
                                Leaves(initial_node))
            break
        end
    end

    @assert all(nd -> isempty(nd.remaining), Leaves(initial_node))
    
    res = POLI[]
    println("-----------")
    println("final components:")
    for lv in Leaves(initial_node)
        sat_ring(1) in lv.ideal && continue
        idl = ideal(R, [F_inv(p) for p in gens(lv.ideal)])
        gb = f4(idl, complete_reduction = true)
        println("number of terms in gb: $(sum([length(monomials(p)) for p in gb]))")
        println("codimension: $(ngens(R) - dim(idl))")
        push!(res, idl)
    end
        
    return res
end

function zero!(node::DecompNode, P::Vector{POL})
    R = base_ring(node.ideal)
    new_idl = node.ideal + ideal(R, P)
    for h in node.nonzero
        new_idl = msolve_saturate(new_idl, h)
    end
    new_node = DecompNode(new_idl, copy(node.nonzero), copy(node.remaining),
                          node, false, Dict{POL, Vector{POL}}(), DecompNode[],
                          DecompNode[])
    push!(node.zero_children, new_node)
    return new_node
end

function nonzero!(node::DecompNode, p::POL)
    R = base_ring(node.ideal)
    new_pols = anncashed!(node, p)
    new_idl = node.ideal + ideal(R, new_pols)
    new_node = DecompNode(new_idl, vcat(node.nonzero, [p]), copy(node.remaining),
                          node, true, Dict{POL, Vector{POL}}(), DecompNode[],
                          DecompNode[])
    push!(node.nonzero_children, new_node)
    return new_node
end

function nonzero_presplit!(node::DecompNode, P::Vector{POL}, f::POL)

    isempty(P) && return DecompNode[]
    new_nodes = [begin
                     println("setting $(p) nonzero")
                     nonzero!(node, p)
                 end for p in P]
    res = DecompNode[]
    println("presplitting")
    annis = Dict([(P[i], anncashed!(node, P[i])) for i in 1:length(P)])
    for (i, p) in enumerate(P)
        println("presplitting along $(i)th p")
        P1 = POL[]
        P2 = POL[]
        for (j, q) in enumerate(P[1:i-1])
            if all(f -> iszero(f), normal_form(annis[q], new_nodes[i].ideal))
                println("regular intersection with $(j)th q detected")
                push!(P1, q)
            else
                push!(P2, q)
            end
        end
        new_nd = zero!(new_nodes[i], P1)
        push!(res, new_nd)
        pushfirst!(new_nd.remaining, f)
        prepend!(new_nd.remaining, P2)
    end
    return res
end

function findpreviousann(node::DecompNode, f::POL)
    if haskey(node.ann_cashe, f)
        return true, node.ann_cashe[f], node
    elseif isnothing(AbstractTrees.parent(node))
        return true, nothing, nothing
    elseif haskey(AbstractTrees.parent(node).ann_cashe, f)
        return node.parentnonzero, AbstractTrees.parent(node).ann_cashe[f], node.parent
    else
        onlynz, res, nd = findpreviousann(AbstractTrees.parent(node), f)
        return onlynz && node.parentnonzero, res, nd
    end
end

function anncashed!(node::DecompNode, f::POL; onlyneedone = false)
    onlynz, prev, nd = findpreviousann(node, f)
    res = POL[]
    if isnothing(prev)
        # compute ann and cache the result
        res = ann!(node.ideal, node.ideal, f)
    elseif nd == node
        return prev
    elseif onlynz && onlyneedone
        # only normal form if we just need any zero divisor
        dynamicgb!(node.ideal)
        res = normal_form(prev, node.ideal)
        filter!(p -> !iszero(p), res)
    else
        R = base_ring(node.ideal)
        res = ann!(node.ideal, node.ideal + ideal(R, prev), f)
    end
    sort!(res, by = p -> total_degree(p))
    node.ann_cashe[f] = res
    return res
end

# compute nontrivial zero divisors of powers of f over idl
# base is an ideal known to be contained in (I : f^infty)
function ann!(idl::POLI, base::POLI, f::POL)

    sat_ideal = msolve_saturate(base, f)
    dynamicgb!(idl)
    res = normal_form[gens(sat_ideal), idl]
    return filter!(p -> !iszero(p), res)
end

function msolve_saturate(idl::POLI, f::POL)
    R = base_ring(idl)
    vars = gens(R)
    J = ideal(R, [gens(idl)..., vars[1]*f - 1])
    gb = f4(J, eliminate = 1, complete_reduction = true)
    return ideal(R, gb)
end
    
function dynamicgb!(I::POLI)
    if isempty(I.gb)
        f4(I, eliminate = 1, complete_reduction = true)
    else
        nothing
    end
    return
end

function reduce_generators_size!(I::POLI,
                                 gens_over_I::Vector{POL})

    R = base_ring(I)
    println("reducing size of generating set...")
    sort!(gens_over_I, by = p -> total_degree(p))
    indices_redundant_elements = Int[]
    J = I
    for (i, p) in enumerate(gens_over_I)
        i in indices_redundant_elements && continue
        J = J + ideal(R, [p])
        f4(J)
        for (j, q) in enumerate(gens_over_I[i+1:end])
            j in indices_redundant_elements && continue
            q in J && push!(indices_redundant_elements, j + i)
        end
    end
    deleteat!(gens_over_I, sort(unique(indices_redundant_elements)))
    return
end

end # module Decomp
