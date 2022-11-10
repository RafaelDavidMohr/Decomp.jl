module Decomp

using Reexport
@reexport using Oscar
@reexport using AbstractTrees

include("oscar_util.jl")

export decomp, extract_ideals

mutable struct DecompNode
    reg_seq::Vector{POL}
    ideal::POLI
    nonzero::Vector{POL}
    remaining::Vector{POL}
    parent::Union{Nothing, DecompNode}
    parentnonzero::Bool
    ann_cashe::Dict{POL, Vector{POL}}
    nonzero_children::Vector{DecompNode}
    zero_children::Vector{DecompNode}
end

function Base.show(io::IO, node::DecompNode)
    R = base_ring(node.ideal)
    if R(1) in node.ideal
        print(io, "empty component")
    else
        print(io, """codim $(length(node.reg_seq)),
                     reg seq lms $([leading_monomial(p) for p in node.reg_seq]),
                     nonzero lms: $([leading_monomial(h) for h in node.nonzero])""")
    end
end


AbstractTrees.childtype(::DecompNode) = DecompNode

function AbstractTrees.children(node::DecompNode)
    vcat(node.nonzero_children, node.zero_children)
end

AbstractTrees.ParentLinks(::Type{DecompNode}) = StoredParents()
AbstractTrees.parent(node::DecompNode) = node.parent

AbstractTrees.NodeType(::Type{DecompNode}) = HasNodeType()
AbstractTrees.nodetype(::Type{DecompNode}) = DecompNode

function inter!(node::DecompNode;
                version = "probabilistic")

    f = popfirst!(node.remaining)
    println("intersecting with $f over component with $(length(node.nonzero)) nz conditions")
    G = anncashed!(node, f, onlyneedone = true)

    if isempty(G)
        # f regular
        println("is regular")
        return [zero!(node, [f], [f])]
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
            if version == "probabilistic"
                new_nodes = nonzero_presplit!(node, H, f)
            else
                new_nodes = nonzero_presplit_deterministic!(node, H, f)
            end
            high_dim = zero!(node, H)
            res = vcat([high_dim], new_nodes)
            println("$(length(res)) new components")
            return res
        end
    end
    error("we have run into a case that I am currently unsure how to handle.")
    return DecompNode[]
end

function decomp(sys::Vector{POL};
                version = "probabilistic")

    isempty(sys) && error("system is empty")
    
    R = parent(first(sys))
    sat_ring, vars = PolynomialRing(base_ring(R),
                                    pushfirst!(["y$(i)" for i in 1:ngens(R)], "t"))
    F = hom(R, sat_ring, vars[2:end])
    F_inv = hom(sat_ring, R, [zero(R), gens(R)...])
    
    initial_node = DecompNode([F(first(sys))], ideal(sat_ring, F(first(sys))),
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
            inter!(node, version = version)
            all_processed = all(nd -> isempty(nd.remaining),
                                Leaves(initial_node))
            break
        end
    end
        
    res = POLI[]
    println("-----------")
    println("final components:")
    for lv in Leaves(initial_node)
        sat_ring(1) in lv.ideal && continue
        idl = ideal(R, [F_inv(p) for p in gens(lv.ideal)])
        gb = f4(idl, complete_reduction = true)
        println("number of terms in gb: $(sum([length(monomials(p)) for p in gb]))")
        println("codimension: $(length(lv.reg_seq))")
        push!(res, idl)
    end
        
    return initial_node, F_inv
end

function zero!(node::DecompNode, P::Vector{POL},
               append_to_req_seq::Vector{POL} = POL[])
    R = base_ring(node.ideal)
    new_idl = node.ideal + ideal(R, P)
    for h in node.nonzero
        new_idl = msolve_saturate(new_idl, h)
    end
    new_node = DecompNode(vcat(node.reg_seq, append_to_req_seq), new_idl,
                          copy(node.nonzero), copy(node.remaining),
                          node, false, Dict{POL, Vector{POL}}(), DecompNode[],
                          DecompNode[])
    push!(node.zero_children, new_node)
    return new_node
end

function nonzero!(node::DecompNode, p::POL)
    R = base_ring(node.ideal)
    new_pols = anncashed!(node, p)
    new_idl = node.ideal + ideal(R, new_pols)
    new_node = DecompNode(copy(node.reg_seq), new_idl, vcat(node.nonzero, [p]), copy(node.remaining),
                          node, true, Dict{POL, Vector{POL}}(), DecompNode[],
                          DecompNode[])
    push!(node.nonzero_children, new_node)
    return new_node
end

function nonzero_presplit!(node::DecompNode, P::Vector{POL}, f::POL)

    isempty(P) && return DecompNode[]
    new_nodes = [node for p in P]
    R = base_ring(node.ideal)
    d = dim(node.ideal) - 1
    println("presplitting")
    for (i, p) in enumerate(P)
        println("computing sample points for $(i)th p")
        sample_points_p_nonzero = sample_points(node.ideal, vcat(node.nonzero, [p]), d)
        if R(1) in sample_points_p_nonzero
            println("component is empty, going to next equation")
            break
        end
        P1 = POL[]
        P2 = POL[]
        curr_dim = d
        rem = vcat(P[1:i-1], [f], node.remaining) 
        for (j, q) in enumerate(rem)
            println("treating $(j)th remaining equation")
            if R(1) in (sample_points_p_nonzero + ideal(R, q))
                println("regular intersection detected, recomputing sample points...")
                push!(P1, q)
                curr_dim -= 1
                sample_points_p_nonzero = sample_points(node.ideal + ideal(R, P1),
                                                        vcat(node.nonzero, [p]),
                                                        curr_dim)
                if R(1) in sample_points_p_nonzero
                    println("component is empty, going to next equation")
                    break
                end
            else
                if j > i-1
                    append!(P2, rem[j:end])
                    break
                else
                    push!(P2, q)
                end
            end
        end
        println("setting nonzero")
        new_nodes[i] = nonzero!(zero!(node, P1, P1), p)
        new_nodes[i].remaining = copy(P2)
    end
    return new_nodes
end

function nonzero_presplit_deterministic!(node::DecompNode, P::Vector{POL}, f::POL)

    isempty(P) && return DecompNode[]
    new_nodes = [begin
                     println("setting $(p) nonzero")
                     nonzero!(node, p)
                 end for p in P]
    println("presplitting")
    for (i, p) in enumerate(P)
        println("presplitting along $(i)th p")
        P1 = POL[]
        P2 = POL[]
        for (j, q) in enumerate(P[1:i-1])
            anni = anncashed!(new_nodes[i], q)
            if isempty(anni)
                println("regular intersection with $(j)th q detected")
                new_nodes[i] = zero!(new_nodes[i], [q], [q])
            else
                push!(P2, q)
            end
        end
        pushfirst!(new_nodes[i].remaining, f)
        prepend!(new_nodes[i].remaining, P2)
    end
    return new_nodes
end

function sample_points(I::POLI, nonzero::Vector{POL}, d::Int)
    R = base_ring(I)
    # do not incorporate the eliminating variable
    result = I + ideal(R, [random_lin_comb(R, [gens(R)[2:end]..., R(1)]) for _ in 1:d])
    for h in nonzero
        result = msolve_saturate(result, h)
    end
    return result
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
    sort!(res, lt = (p1, p2) -> total_degree(p1) < total_degree(p2) || total_degree(p1) == total_degree(p2) && length(monomials(p1)) < length(monomials(p2)))
    node.ann_cashe[f] = res
    return res
end

# compute nontrivial zero divisors of powers of f over idl
# base is an ideal known to be contained in (I : f^infty)
function ann!(idl::POLI, base::POLI, f::POL)

    sat_ideal = msolve_saturate(base, f)
    dynamicgb!(idl)
    res = normal_form(gens(sat_ideal), idl)
    return filter!(p -> !iszero(p), res)
end

function msolve_saturate(idl::POLI, f::POL)
    R = base_ring(idl)
    vars = gens(R)
    J = ideal(R, [gens(idl)..., vars[1]*f - 1])
    gb = f4(J, eliminate = 1, complete_reduction = true, la_option = 42)
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

#--- User utility functions ---#

function extract_ideals(node::DecompNode, hom)
    R = codomain(hom)
    S = domain(hom)
    filter!(idl -> !(R(1) in idl), [ideal(R, (p->hom(p)).(gens(nd.ideal))) for nd in Leaves(node)])
end

end
