module Decomp

using Reexport
@reexport using Oscar
@reexport using AbstractTrees

include("oscar_util.jl")

export decomp, extract_ideals, kalk_decomp


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

dimension(node::DecompNode) = ngens(base_ring(node.ideal)) - 1 - length(node.reg_seq)

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

    # here check regularity with hyperplane cuts
    sp_and_f = sample_points(node.ideal, node.nonzero, dimension(node)) + ideal(base_ring(node.ideal), f)
    gb = f4(sp_and_f, complete_reduction = true)
    if one(base_ring(node.ideal)) in gens(gb)
        println("is regular (hyperplane check)")
        return [zero!(node, [f], [f])]
    end
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

            println("$(length(H)) zero divisors:")
            println(H)
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
        all_processed = all(nd -> isempty(nd.remaining), Leaves(initial_node))
        for node in Leaves(initial_node)
            isempty(node.remaining) && continue
            # sp = sample_points(node.ideal, node.nonzero, dimension(node))
            # gb = f4(sp, complete_reduction = true)
            # if sat_ring(1) in gens(gb) 
            #     empty!(node.remaining)
            #     continue
            # end
            inter!(node, version = version)
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
    d = dimension(node)
    println("presplitting")
    for (i, p) in enumerate(P)
        println("nonzero condition: $(p)")
        println("computing sample points for $(i)th p")
        sample_points_p_nonzero = sample_points(node.ideal, vcat(node.nonzero, [p]), d)
        if R(1) in sample_points_p_nonzero
            println("component is empty, going to next equation")
            break
        end
        P1 = POL[]
        P2 = POL[]
        curr_dim = d
        rem = vcat(P[1:i-1]) 
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
                push!(P2, q)
            end
        end
        println("setting nonzero")
        new_nodes[i] = nonzero!(zero!(node, P1, P1), p)
        prepend!(new_nodes[i].remaining, [P2..., f])
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
    # return ann!(node.ideal, node.ideal, f)
end

# compute nontrivial zero divisors of powers of f over idl
# base is an ideal known to be contained in (I : f^infty)
function ann!(idl::POLI, base::POLI, f::POL)

    sat_ideal = msolve_saturate(base, f)
#    dynamicgb!(idl)
    res = normal_form(gens(sat_ideal), idl)
    return filter!(p -> !iszero(p), res)
end

function msolve_saturate(idl::POLI, f::POL)
    R = base_ring(idl)
    vars = gens(R)
    J = ideal(R, [gens(idl)..., vars[1]*f - 1])
    gb = f4(J, eliminate = 1, complete_reduction = true)
    return ideal(R, gens(gb))
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

#--- Kalkbrener Decomposition ---#

struct NzCond
    p::POL
    order::Int
end

mutable struct KalkComp
    eqns::Vector{POL}
    nz_cond::Vector{NzCond}
    nz_cond_queue::Vector{NzCond}
    ideal::POLI
    remaining::Vector{POL}
end

function Base.show(io::IO, comp::KalkComp)
    R = base_ring(comp.ideal)
    if R(1) in comp.ideal
        print(io, "empty component")
    else
        print(io, """codim $(ngens(base_ring(comp.ideal)) - 1 - dimension(comp.ideal)),
                     eqns $(comp.eqns),
                     nonzero $([P.p for P in comp.nz_cond])""")
    end
end

function copycomp(comp::KalkComp)
    return KalkComp(copy(comp.eqns), copy(comp.nz_cond),
                    copy(comp.nz_cond_queue),
                    comp.ideal, copy(comp.remaining))
end

function kalk_decomp(sys::Vector{POL})

    isempty(sys) && error("system is empty")
    
    R = parent(first(sys))
    
    initial_component = KalkComp([first(sys)], NzCond[], Int[],
                                 ideal(R, first(sys)),
                                 sys[2:end])

    comp_queue = [initial_component]
    done = KalkComp[]

    while !isempty(comp_queue)
        component = popfirst!(comp_queue)
        if any(p -> isone(p.order), union(component.nz_cond, component.nz_cond_queue))
            println("WARNING: splitting component with nz condition of order 1")
        end
        comps = process_nonzero(component)
        println("obtained $(length(comps)) components")
        for comp in comps
            if R(1) in comp.ideal
                println("is empty")
                println("----")
                continue
            end
            if isempty(comp.remaining)
                println("done.")
                println("----")
                push!(done, comp)
                continue
            end
            components = kalk_split!(comp)
            println("adding $(length(components)) to queue")
            println("----")
            comp_queue = vcat(comp_queue, components)
        end
    end
        
    res = POLI[]
    println("final components:")
    for comp in done
        gb = f4(comp.ideal, complete_reduction = true)
        println("number of terms in gb: $(sum([length(monomials(p)) for p in gb]))")
        println("codimension: $(ngens(R) - dimension(comp.ideal))")
    end
        
    return done
end

function process_nonzero(comp::KalkComp)
    todo = [comp]
    done = KalkComp[]
    while !isempty(todo)
        component = popfirst!(todo)
        while !isempty(component.nz_cond_queue)
            p = popfirst!(component.nz_cond_queue)
            new_base_comp = copycomp(component)
            component.ideal = msolve_saturate_elim(component.ideal, p.p)
            push!(component.nz_cond, p)
            !isone(p.order) && continue
            H = filter(h -> !(h in new_base_comp.ideal), gens(component.ideal))
            R = base_ring(p.p)
            if one(R) in H
                println("WARNING: component became empty")
            end
            if isempty(H)
                continue
            end
            println("nontrivial presplit with $(length(H)) elements")
            reduce_generators_size!(new_base_comp.ideal, H)
            new_comps = kalk_nonzero(new_base_comp, H, p.p)
            todo = vcat(todo, new_comps)
        end
        push!(done, component)
    end
    return done
end

function kalk_split!(comp::KalkComp)

    R = base_ring(comp.ideal)
    g = zero(R)
    H = POL[]
    comp1 = copycomp(comp)
    f = popfirst!(comp.remaining)
    println("checking regularity of $(f)")
    sat_by_f = msolve_saturate_elim(comp.ideal, f)
    for p in gens(sat_by_f)
        if !(p in comp.ideal)
            if isone(p)
                println("vanishes entirely")
                empty!(comp.nz_cond)
                empty!(comp.nz_cond_queue)
                return [comp]
            end
            println("trying to split along element of degree $(total_degree(p))")
            comp1 = copycomp(comp)
            #kalk_nonzero!(comp1, p, 1)
            comp1.ideal = msolve_saturate_elim(comp1.ideal, p)
            H = filter(h -> !(h in comp.ideal), gens(comp1.ideal))
            R(1) in H && continue
            g = p
            break
        end
    end
    if iszero(g)
        println("is regular")
        push!(comp.eqns, f)
        comp.ideal = comp.ideal + ideal(base_ring(comp.ideal), f)
        # comp.nz_cond_queue = copy(comp.nz_cond)
        for h in comp.nz_cond
            comp.ideal = msolve_saturate_elim(comp.ideal, h.p)
        end
        empty!(comp.nz_cond_queue)
        empty!(comp.nz_cond)

        return [comp]
    end

    reduce_generators_size!(comp.ideal, H)
    println("setting $(length(H)) elements nonzero")
    new_comps = kalk_nonzero(comp, H, g)
    for new_comp in new_comps
        pushfirst!(new_comp.remaining, f)
    end
    return vcat(new_comps, [comp1])
end

function kalk_nonzero!(comp::KalkComp, h::POL, order::Int)
    push!(comp.nz_cond, NzCond(h, order))
    comp.ideal = msolve_saturate_elim(comp.ideal, h)
end
    
function kalk_nonzero(comp::KalkComp, H::Vector{POL}, known_zd::POL)
    R = base_ring(comp.ideal)
    res = [copycomp(comp) for _ in H]
    P = POL[]
    for (i, h) in enumerate(H)
        println("saturating by $(i)th h")
        res[i].ideal += ideal(R, H[1:i-1])
        kalk_nonzero!(res[i], h, 2)
        for (j, p) in enumerate(P)
            println("saturating by $(j)th p")
            kalk_nonzero!(res[i], p, 1)
            # res[i].ideal = msolve_saturate_elim(res[i].ideal, p)
        end
        push!(P, random_lin_comb(R, gens(res[i].ideal)))
    end
    println("----")
    return res
end


#--- User utility functions ---#

function extract_ideals(node::DecompNode, hom)
    R = codomain(hom)
    S = domain(hom)
    filter!(idl -> !(R(1) in idl), [ideal(R, (p->hom(p)).(gens(nd.ideal))) for nd in Leaves(node)])
end

end
