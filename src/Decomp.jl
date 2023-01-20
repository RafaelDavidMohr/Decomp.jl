module Decomp

using Reexport
@reexport using Oscar
@reexport using AbstractTrees

include("oscar_util.jl")

export decomp, extract_ideals, print_info

# helpers
function delete_and_return!(d::Dict{K, V}, k::K) where {K, V}
    v = d[k]
    delete!(d, k)
    return v
end

mutable struct DecompNode
    seq::Vector{POL}
    added_by_sat::Vector{Vector{POL}}
    nonzero::Vector{POL}
    gb::Vector{POL}
    gb_known::Bool
    witness_set::Vector{POL}

    remaining::Vector{POL}
    hyperplanes::Vector{POL}

    # tree data structure related for caching
    parent::Union{Nothing, DecompNode}
    zd_cache::Dict{POL, Vector{POL}}
    children::Vector{DecompNode}
end

function Base.show(io::IO, node::DecompNode)
    print(io, """codim $(length(node.seq)),
                 reg seq lms $([leading_monomial(p) for p in node.seq]),
                 nonzero lms: $([leading_monomial(h) for h in node.nonzero])""")
end

# tree stuff
AbstractTrees.childtype(::DecompNode) = DecompNode

function AbstractTrees.children(node::DecompNode)
    node.children
end

AbstractTrees.ParentLinks(::Type{DecompNode}) = StoredParents()
AbstractTrees.parent(node::DecompNode) = node.parent

AbstractTrees.NodeType(::Type{DecompNode}) = HasNodeType()
AbstractTrees.nodetype(::Type{DecompNode}) = DecompNode

ring(node::DecompNode) = parent(first(node.seq))
dimension(node::DecompNode) = ngens(ring(node)) - length(node.seq) - 1
equations(node::DecompNode) = vcat(node.seq, node.added_by_sat..., node.gb)

# compute info about node
function compute_gb!(node::DecompNode)

    if !node.gb_known
        sort!(node.nonzero, by = p -> total_degree(p))
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

function is_empty_set!(node::DecompNode; version = "probabilistic")
    if version == "probabilistic"
        return one(ring(node)) in node.witness_set
    else
        compute_gb!(node)
        return one(ring(node)) in node.gb
    end
end

# operations

function reduce(f::Union{POL, Vector{POL}}, node::DecompNode)

    gb = compute_gb!(node)
    return Oscar.reduce(f, gb)
end

function does_vanish(node::DecompNode, f::POL;
                     version = "probabilistic")

    if version == "probabilistic"
        return iszero(Oscar.reduce(f, node.witness_set))
    else
        return iszero(reduce(f, node))
    end
end

function is_regular_int(node::DecompNode, f::POL)

    does_vanish(node, f) && return "vanishes"
    R = ring(node)
    gb = f4(ideal(R, node.witness_set) + ideal(R, f),
            complete_reduction = true)
    R(1) in gb && return "regular"
    return "undecided"
end

function find_previous_zds!(node::DecompNode, f::POL)
    if haskey(node.zd_cache, f) 
        return delete_and_return!(node.zd_cache[f])
    elseif isnothing(AbstractTrees.parent(node))
        return POL[]
    else
        return find_previous_zds!(AbstractTrees.parent(node), f)
    end
end

function find_nontrivial_zero_divisor!(node::DecompNode, f::POL)
    G = find_previous_zds!(node, f)
    node.zd_cache[f] = G
    while !isempty(node.zd_cache[f])
        g = popfirst!(node.zd_cache[f])
        does_vanish(node, g) && continue
        return g    
    end
    compute_gb!(node)
    G = msolve_colon_elim(node.gb, f)
    node.zd_cache[f] = G
    while !isempty(node.zd_cache[f])
        g = popfirst!(node.zd_cache[f])
        does_vanish(node, g) && continue
        return g    
    end
    return zero(f)
end
        
function zero!(node::DecompNode, 
               append_to_sat::Vector{POL},
               append_to_req_seq::Vector{POL};
               version = "probabilistic")

    R = ring(node)
    idl_gens = vcat(equations(node), append_to_req_seq, append_to_sat)
    new_dim = dimension(node) - length(append_to_req_seq)
    new_witness = version == "probabilistic" ? compute_witness_set(idl_gens, node.nonzero, new_dim, node.hyperplanes) : node.witness_set
    new_node = DecompNode(vcat(node.seq, append_to_req_seq),
                          vcat(node.added_by_sat, [append_to_sat]),
                          copy(node.nonzero),
                          node.gb,
                          false,
                          new_witness,
                          copy(node.remaining),
                          node.hyperplanes,
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
        new_pols = ann(node, p)
        gb_known = true
        new_gb = vcat(node.gb, new_pols)
    end
    new_witness = version == "probabilistic" ? compute_witness_set(equations(node), vcat(node.nonzero, [p]), dimension(node), node.hyperplanes) : node.witness_set
    new_node = DecompNode(copy(node.seq), copy(node.added_by_sat),
                          vcat(node.nonzero, [p]), new_gb, gb_known,
                          new_witness,
                          copy(node.remaining), node.hyperplanes, node, Dict{POL, Vector{POL}}(),
                          DecompNode[])
    push!(node.children, new_node)
    return new_node
end

function remove!(node::DecompNode, P::Vector{POL}, f::POL, zd::POL)

    isempty(P) && return DecompNode[]
    new_nodes = DecompNode[]
    R = ring(node)
    println("presplitting")
    for (i, p) in enumerate(P)
        println("computing sample points for $(i)th p")
        new_node = nonzero!(node, p)
        push!(new_node.gb, zd)
        new_node.witness_set = compute_witness_set(equations(new_node),
                                                   new_node.nonzero,
                                                   dimension(new_node),
                                                   new_node.hyperplanes)
        if is_empty_set!(new_node)
            println("component is empty, going to next equation")
            pop!(node.children)
            continue
        end
        P2 = POL[]
        for (j, q) in enumerate(P[1:i-1])
            println("treating $(j)th remaining equation")
            int_type = is_regular_int(new_node, q)
            if int_type == "regular"
                println("regular intersection detected, recomputing sample points...")
                new_node = zero!(new_node, POL[], [q])
                if is_empty_set!(new_node)
                    println("component is empty, going to next equation")
                    break
                end
            elseif int_type == "vanishes"
                continue
            else
                push!(P2, q)
            end
        end
        prepend!(new_node.remaining, [P2..., f])
        push!(new_nodes, new_node)
    end
    return new_nodes
end

function remove_deterministic!(node::DecompNode, P::Vector{POL}, f::POL)

    isempty(P) && return DecompNode[]
    new_nodes = [begin
                     println("setting $(i)th p nonzero")
                     nonzero!(node, p, version = "deter")
                 end for (i, p) in enumerate(P)]
    println("presplitting")
    for (i, p) in enumerate(P)
        println("presplitting along $(i)th p")
        P1 = POL[]
        P2 = POL[]
        for (j, q) in enumerate(P[1:i-1])
            anni = ann(new_nodes[i], q)
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

function inter!(node::DecompNode;
                version = "probabilistic")

    f = popfirst!(node.remaining)
    println("intersecting with equation of degree $(total_degree(f)) over component with $(length(node.nonzero)) nz conditions")

    # here check regularity with hyperplane cuts
    if version == "probabilistic"
        int_test = is_regular_int(node, f)
        if int_test == "regular"
            println("is regular (witness set)")
            return zero!(node, POL[], [f])
        elseif int_test == "vanishes"
            println("vanishes (witness set)")
            return node
        end
    end
    g = find_nontrivial_zero_divisor!(node, f)
    if iszero(g)
        # f regular
        println("is regular")
        return [zero!(node, POL[], [f])]
    else # we split
        println("splitting along equation of degree $(total_degree(g))")
        H = ann(node, g)
        println("$(length(H)) zero divisors")
        if version == "probabilistic"
            new_nodes = remove!(node, H, f, g)
        else
            new_nodes = remove_deterministic!(node, H, f)
        end
        high_dim = zero!(node, H, POL[])
        res = vcat([high_dim], new_nodes)
        println("$(length(res)) new components")
        return res
    end
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
    hyperplanes = [random_lin_comb(sat_ring, [gens(sat_ring)[2:end]..., sat_ring(1)]) for _ in 1:ngens(R)]
    initial_witness = version == "probabilistic" ? compute_witness_set(first_eqns, POL[], ngens(R) - 1, hyperplanes) : first_eqns
    initial_node = DecompNode(first_eqns, Vector{POL}[],
                              POL[], first_eqns, true,
                              initial_witness,
                              (F).(sys[2:end]),
                              hyperplanes,
                              nothing,
                              Dict{POL, Vector{POL}}(),
                              DecompNode[])

    all_processed = all(nd -> isempty(nd.remaining), Leaves(initial_node))
    while !all_processed 
        all_processed = all(nd -> isempty(nd.remaining), Leaves(initial_node))
        for node in Leaves(initial_node)
            isempty(node.remaining) && continue
            if is_empty_set!(node) 
                empty!(node.remaining)
                continue
            end
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

function ann(node::DecompNode, f::POL)

    compute_gb!(node)
    gb = msolve_saturate(node.gb, f)
    res = reduce(gb, node)
    return filter!(p -> !iszero(p), res)
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
    println("extracting degree/dimension info, this may take a while...")
    Rr = ring(node)
    comps = filter(nd -> !(Rr(1) in nd.witness_set), collect(Leaves(node)))
    println("$(length(collect(Leaves(node))) - length(comps)) empty components")
    number_emb_comps = 0
    dim_degree = Dict{Int, Int}([(i, 0) for i in 0:(ngens(Rr) - 1)])
    sort!(comps, by = nd -> dimension(nd), rev = true)
    for (i, nd) in enumerate(comps)
        ws_gens = copy(nd.witness_set)
        for lower_dim in comps[1:i-1]
            compute_gb!(lower_dim)
            if dimension(lower_dim) > dimension(nd) 
                p = random_lin_comb(Rr, lower_dim.gb)
                ws_gens = msolve_saturate(ws_gens, p)
            end
        end
        push!(ws_gens, first(gens(Rr)))
        J = radical(ideal(Rr, ws_gens))
        A, _ = quo(Rr, J)
        vd = vdim(A)
        if vd > 0
            println("component of dimension $(dimension(nd)), degree $(vd)")
            dim_degree[dimension(nd)] += 1
        else
            number_emb_comps += 1
        end
    end
    println("---")
    for (k, v) in pairs(dim_degree)
        v > 0 && println("dimension $k, degree $v")
    end
    println("$(number_emb_comps) embedded components")
end

end
