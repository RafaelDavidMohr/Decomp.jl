module Decomp

using Reexport
@reexport using Oscar
@reexport using AbstractTrees

include("oscar_util.jl")

export decomp, extract_ideals, print_info

mutable struct DecompNode
    seq::Vector{POL}
    added_by_sat::Vector{Vector{POL}}
    nonzero::Vector{POL}
    gb::Vector{POL}
    gb_known::Bool
    witness_set::Vector{POL}

    remaining::Vector{POL}

    # tree data structure related for caching
    parent::Union{Nothing, DecompNode}
    ann_cashe::Dict{POL, Vector{POL}}
    children::Vector{DecompNode}
end

ring(node::DecompNode) = parent(first(node.seq))
dimension(node::DecompNode) = ngens(ring(node)) - length(node.seq) - 1
equations(node::DecompNode) = vcat(node.seq, node.added_by_sat..., node.gb)

function compute_gb!(node::DecompNode)

    if !node.gb_known
        R = ring(node)
        res = equations(node)
        for h in node.nonzero
            res = msolve_saturate(res, h) 
        end
        node.gb_known = true
        node.gb = gens(f4(ideal(ring(node), res), complete_reduction = true))
    end
    return node.gb
end

function reduce(f::Union{POL, Vector{POL}}, node::DecompNode)

    gb = compute_gb!(node)
    return Oscar.reduce(f, gb)
end

function Base.show(io::IO, node::DecompNode)
    print(io, """codim $(length(node.seq)),
                 reg seq lms $([leading_monomial(p) for p in node.seq]),
                 nonzero lms: $([leading_monomial(h) for h in node.nonzero])""")
end

AbstractTrees.childtype(::DecompNode) = DecompNode

function AbstractTrees.children(node::DecompNode)
    node.children
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
    if version == "probabilistic"
        R = ring(node)
        gb = f4(ideal(R, node.witness_set) + ideal(R, f), complete_reduction = true)
        if one(R) in gens(gb)
            println("is regular (hyperplane check)")
            return [zero!(node, POL[], [f])]
        end
        gb = f4(ideal(R, node.witness_set) + ideal(R, gens(R)[1] * f - 1), complete_reduction = true)
        if one(R) in gens(gb)
            println("vanishes (hyperplane check)")
            return [node]
        end 
    end
    G = anncashed!(node, f, onlyneedone = true)
    if isempty(G)
        # f regular
        println("is regular")
        return [zero!(node, POL[], [f])]
    elseif iszero(total_degree(first(G)))
        # f vanishes
        println("vanishes")
        return [node]
    else # we split
        for g in G
            H = anncashed!(node, g)
            iszero(total_degree(first(H))) && continue
            println("splitting along $(g)")
            reduce_generators_size!(node.gb, H)

            println("$(length(H)) zero divisors")
            if version == "probabilistic"
                new_nodes = nonzero_presplit!(node, H, f)
            else
                new_nodes = nonzero_presplit_deterministic!(node, H, f)
            end
            high_dim = zero!(node, H, POL[])
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
    
    first_eqns = [F(first(sys))]
    initial_node = DecompNode(first_eqns, Vector{POL}[],
                              POL[], first_eqns, true,
                              compute_witness_set(first_eqns, POL[], ngens(R) - 1), (F).(sys[2:end]),
                              nothing,
                              Dict{POL, Vector{POL}}(),
                              DecompNode[])

    all_processed = all(nd -> isempty(nd.remaining), Leaves(initial_node))
    while !all_processed 
        all_processed = all(nd -> isempty(nd.remaining), Leaves(initial_node))
        for node in Leaves(initial_node)
            isempty(node.remaining) && continue
            inter!(node, version = version)
            break
        end
    end
        
    # res = POLI[]
    # println("-----------")
    # println("final components:")
    # for lv in Leaves(initial_node)
    #     sat_ring(1) in lv.ideal && continue
    #     idl = ideal(R, [F_inv(p) for p in gens(lv.ideal)])
    #     gb = f4(idl, complete_reduction = true)
    #     println("number of terms in gb: $(sum([length(monomials(p)) for p in gb]))")
    #     println("codimension: $(length(lv.reg_seq))")
    #     push!(res, idl)
    # end
        
    return initial_node, F_inv
end

function zero!(node::DecompNode, 
               append_to_sat::Vector{POL},
               append_to_req_seq::Vector{POL})

    R = ring(node)
    idl_gens = vcat(equations(node), append_to_req_seq, append_to_sat)
    new_dim = dimension(node) - length(append_to_req_seq)
    new_node = DecompNode(vcat(node.seq, append_to_req_seq),
                          vcat(node.added_by_sat, [append_to_sat]),
                          copy(node.nonzero),
                          node.gb,
                          false,
                          compute_witness_set(idl_gens, node.nonzero, new_dim),
                          copy(node.remaining),
                          node,
                          Dict{POL, Vector{POL}}(),
                          DecompNode[])
    push!(node.children, new_node)
    return new_node
end

function nonzero!(node::DecompNode, p::POL; version = "probabilistic")
    R = ring(node)
    new_pols = POL[]
    gb_known = false
    new_gb = copy(node.gb)
    if version != "probabilistic"
        new_pols = anncashed!(node, p)
        gb_known = true
        new_gb = vcat(node.gb, new_pols)
    end
    node_id_gens = vcat(node.gb, node.seq, node.added_by_sat...)
    new_node = DecompNode(copy(node.seq), copy(node.added_by_sat),
                          vcat(node.nonzero, [p]), new_gb, gb_known,
                          compute_witness_set(node_id_gens,
                                              vcat(node.nonzero, [p]), dimension(node)),
                          copy(node.remaining), node, Dict{POL, Vector{POL}}(),
                          DecompNode[])
    push!(node.children, new_node)
    return new_node
end

function nonzero_presplit!(node::DecompNode, P::Vector{POL}, f::POL)

    isempty(P) && return DecompNode[]
    new_nodes = [node for p in P]
    R = ring(node)
    d = dimension(node)
    println("presplitting")
    for (i, p) in enumerate(P)
        println("nonzero condition: $(p)")
        println("computing sample points for $(i)th p")
        witness_set_p_nz = node.witness_set
        if R(1) in witness_set_p_nz
            println("component is empty, going to next equation")
            break
        end
        P1 = POL[]
        P2 = POL[]
        curr_dim = d
        rem = vcat(P[1:i-1]) 
        for (j, q) in enumerate(rem)
            println("treating $(j)th remaining equation")
            if R(1) in f4(ideal(ring(node), vcat(witness_set_p_nz, [q])), complete_reduction = true)
                println("regular intersection detected, recomputing sample points...")
                push!(P1, q)
                curr_dim -= 1
                witness_set_p_nz = compute_witness_set(vcat(equations(node), P1),
                                                       vcat(node.nonzero, [p]),
                                                       curr_dim)
                if R(1) in witness_set_p_nz
                    println("component is empty, going to next equation")
                    break
                end
            else
                push!(P2, q)
            end
        end
        println("setting nonzero")
        new_nodes[i] = nonzero!(zero!(node, POL[], P1), p)
        prepend!(new_nodes[i].remaining, [P2..., f])
    end
    return new_nodes
end

function nonzero_presplit_deterministic!(node::DecompNode, P::Vector{POL}, f::POL)

    isempty(P) && return DecompNode[]
    new_nodes = [begin
                     println("setting $(p) nonzero")
                     # TODO: need a deterministic nonzero version
                     nonzero!(node, p, version = "deter")
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
                new_nodes[i] = zero!(new_nodes[i], POL[], [q])
            else
                push!(P2, q)
            end
        end
        pushfirst!(new_nodes[i].remaining, f)
        prepend!(new_nodes[i].remaining, P2)
    end
    return new_nodes
end

function compute_witness_set(id_gens::Vector{POL}, nonzero::Vector{POL}, d::Int)
    R = parent(first(id_gens))
    # do not incorporate the eliminating variable
    result = vcat(id_gens, [random_lin_comb(R, [gens(R)[2:end]..., R(1)]) for _ in 1:d])
    for h in nonzero
        result = msolve_saturate(result, h)
    end
    return result
end

function findpreviousann(node::DecompNode, f::POL)
    if haskey(node.ann_cashe, f)
        return node.ann_cashe[f], node
    elseif isnothing(AbstractTrees.parent(node))
        return nothing, nothing
    elseif haskey(AbstractTrees.parent(node).ann_cashe, f)
        return AbstractTrees.parent(node).ann_cashe[f], node.parent
    else
        res, nd = findpreviousann(AbstractTrees.parent(node), f)
        return res, nd
    end
end

function anncashed!(node::DecompNode, f::POL; onlyneedone = false)
    prev, nd = findpreviousann(node, f)
    # res = POL[]
    # if isnothing(prev)
    #     # compute ann and cache the result
    #     res = ann(node, POL[], f)
    # elseif nd == node
    #     return prev
    # elseif onlyneedone
    #     # only normal form if we just need any zero divisor
    #     compute_gb!(node)
    #     res = reduce(prev, node)
    #     filter!(p -> !iszero(p), res)
    # else
    #     res = ann(node, prev, f)
    # end
    res = ann(node, POL[], f)
    sort!(res, lt = (p1, p2) -> total_degree(p1) < total_degree(p2) || total_degree(p1) == total_degree(p2) && length(monomials(p1)) < length(monomials(p2)))
    node.ann_cashe[f] = res
    return res
end

function ann(node::DecompNode, base::Vector{POL}, f::POL)

    compute_gb!(node)
    gb = msolve_saturate(vcat(node.gb, base), f)
    res = reduce(gb, node)
    return filter!(p -> !iszero(p), res)
end

function msolve_saturate(idl_gens::Vector{POL}, f::POL)
    R = parent(first(idl_gens))
    vars = gens(R)
    J = ideal(R, [idl_gens..., vars[1]*f - 1])
    gb = f4(J, eliminate = 1, complete_reduction = true)
    return gens(gb)
end

function reduce_generators_size!(gb::Vector{POL},
                                 gens_over_I::Vector{POL})

    R = parent(first(gb))
    println("reducing size of generating set...")
    sort!(gens_over_I, by = p -> total_degree(p))
    indices_redundant_elements = Int[]
    J = ideal(R, gb)
    for (i, p) in enumerate(gens_over_I)
        i in indices_redundant_elements && continue
        J = J + ideal(R, [p])
        gb = f4(J)
        for (j, q) in enumerate(gens_over_I[i+1:end])
            j in indices_redundant_elements && continue
            iszero(Oscar.reduce(q, gens(gb))) && push!(indices_redundant_elements, j + i)
        end
    end
    deleteat!(gens_over_I, sort(unique(indices_redundant_elements)))
    return
end

#--- Kalkbrener Decomposition ---#

# struct NzCond
#     p::POL
#     order::Int
# end

# mutable struct KalkComp
#     eqns::Vector{POL}
#     nz_cond::Vector{NzCond}
#     nz_cond_queue::Vector{NzCond}
#     ideal::POLI
#     remaining::Vector{POL}
# end

# function Base.show(io::IO, comp::KalkComp)
#     R = base_ring(comp.ideal)
#     if R(1) in comp.ideal
#         print(io, "empty component")
#     else
#         print(io, """codim $(ngens(base_ring(comp.ideal)) - 1 - dimension(comp.ideal)),
#                      eqns $(comp.eqns),
#                      nonzero $([P.p for P in comp.nz_cond])""")
#     end
# end

# function copycomp(comp::KalkComp)
#     return KalkComp(copy(comp.eqns), copy(comp.nz_cond),
#                     copy(comp.nz_cond_queue),
#                     comp.ideal, copy(comp.remaining))
# end

# function kalk_decomp(sys::Vector{POL})

#     isempty(sys) && error("system is empty")
    
#     R = parent(first(sys))
    
#     initial_component = KalkComp([first(sys)], NzCond[], Int[],
#                                  ideal(R, first(sys)),
#                                  sys[2:end])

#     comp_queue = [initial_component]
#     done = KalkComp[]

#     while !isempty(comp_queue)
#         component = popfirst!(comp_queue)
#         if any(p -> isone(p.order), union(component.nz_cond, component.nz_cond_queue))
#             println("WARNING: splitting component with nz condition of order 1")
#         end
#         comps = process_nonzero(component)
#         println("obtained $(length(comps)) components")
#         for comp in comps
#             if R(1) in comp.ideal
#                 println("is empty")
#                 println("----")
#                 continue
#             end
#             if isempty(comp.remaining)
#                 println("done.")
#                 println("----")
#                 push!(done, comp)
#                 continue
#             end
#             components = kalk_split!(comp)
#             println("adding $(length(components)) to queue")
#             println("----")
#             comp_queue = vcat(comp_queue, components)
#         end
#     end
        
#     res = POLI[]
#     println("final components:")
#     for comp in done
#         gb = f4(comp.ideal, complete_reduction = true)
#         println("number of terms in gb: $(sum([length(monomials(p)) for p in gb]))")
#         println("codimension: $(ngens(R) - dimension(comp.ideal))")
#     end
        
#     return done
# end

# function process_nonzero(comp::KalkComp)
#     todo = [comp]
#     done = KalkComp[]
#     while !isempty(todo)
#         component = popfirst!(todo)
#         while !isempty(component.nz_cond_queue)
#             p = popfirst!(component.nz_cond_queue)
#             new_base_comp = copycomp(component)
#             component.ideal = msolve_saturate_elim(component.ideal, p.p)
#             push!(component.nz_cond, p)
#             !isone(p.order) && continue
#             H = filter(h -> !(h in new_base_comp.ideal), gens(component.ideal))
#             R = base_ring(p.p)
#             if one(R) in H
#                 println("WARNING: component became empty")
#             end
#             if isempty(H)
#                 continue
#             end
#             println("nontrivial presplit with $(length(H)) elements")
#             reduce_generators_size!(new_base_comp.ideal, H)
#             new_comps = kalk_nonzero(new_base_comp, H, p.p)
#             todo = vcat(todo, new_comps)
#         end
#         push!(done, component)
#     end
#     return done
# end

# function kalk_split!(comp::KalkComp)

#     R = base_ring(comp.ideal)
#     g = zero(R)
#     H = POL[]
#     comp1 = copycomp(comp)
#     f = popfirst!(comp.remaining)
#     println("checking regularity of $(f)")
#     sat_by_f = msolve_saturate_elim(comp.ideal, f)
#     for p in gens(sat_by_f)
#         if !(p in comp.ideal)
#             if isone(p)
#                 println("vanishes entirely")
#                 empty!(comp.nz_cond)
#                 empty!(comp.nz_cond_queue)
#                 return [comp]
#             end
#             println("trying to split along element of degree $(total_degree(p))")
#             comp1 = copycomp(comp)
#             #kalk_nonzero!(comp1, p, 1)
#             comp1.ideal = msolve_saturate_elim(comp1.ideal, p)
#             H = filter(h -> !(h in comp.ideal), gens(comp1.ideal))
#             R(1) in H && continue
#             g = p
#             break
#         end
#     end
#     if iszero(g)
#         println("is regular")
#         push!(comp.eqns, f)
#         comp.ideal = comp.ideal + ideal(base_ring(comp.ideal), f)
#         # comp.nz_cond_queue = copy(comp.nz_cond)
#         for h in comp.nz_cond
#             comp.ideal = msolve_saturate_elim(comp.ideal, h.p)
#         end
#         empty!(comp.nz_cond_queue)
#         empty!(comp.nz_cond)

#         return [comp]
#     end

#     reduce_generators_size!(comp.ideal, H)
#     println("setting $(length(H)) elements nonzero")
#     new_comps = kalk_nonzero(comp, H, g)
#     for new_comp in new_comps
#         pushfirst!(new_comp.remaining, f)
#     end
#     return vcat(new_comps, [comp1])
# end

# function kalk_nonzero!(comp::KalkComp, h::POL, order::Int)
#     push!(comp.nz_cond, NzCond(h, order))
#     comp.ideal = msolve_saturate_elim(comp.ideal, h)
# end
    
# function kalk_nonzero(comp::KalkComp, H::Vector{POL}, known_zd::POL)
#     R = base_ring(comp.ideal)
#     res = [copycomp(comp) for _ in H]
#     P = POL[]
#     for (i, h) in enumerate(H)
#         println("saturating by $(i)th h")
#         res[i].ideal += ideal(R, H[1:i-1])
#         kalk_nonzero!(res[i], h, 2)
#         for (j, p) in enumerate(P)
#             println("saturating by $(j)th p")
#             kalk_nonzero!(res[i], p, 1)
#             # res[i].ideal = msolve_saturate_elim(res[i].ideal, p)
#         end
#         push!(P, random_lin_comb(R, gens(res[i].ideal)))
#     end
#     println("----")
#     return res
# end


#--- User utility functions ---#

function extract_ideals(node::DecompNode, hom)
    R = codomain(hom)
    S = domain(hom)
    for nd in Leaves(node)
        compute_gb!(nd)
    end
    filter!(idl -> !(R(1) in idl), [ideal(R, (p->hom(p)).(nd.gb)) for nd in Leaves(node)])
end

function print_info(node::DecompNode)
    for nd in Leaves(node)
        R = ring(nd)
        R(1) in nd.witness_set && continue
        A, _ = quo(R, ideal(R, vcat(node.witness_set, [gens(R)[1]])))
        vd = vdim(A)
        println("component of dimension $(dimension(nd)), degree $(vd)")
    end
end

end
