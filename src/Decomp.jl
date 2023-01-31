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
    nonzero_processed_until::Int
    gb::Vector{POL}
    gb_known::Bool
    witness_set::Vector{POL}

    remaining::Vector{POL}
    hyperplanes::Vector{POL}

    # tree data structure used for caching
    parent::Union{Nothing, DecompNode}
    zd_cache::Dict{POL, Vector{POL}}
    children::Vector{DecompNode}
end

# function Base.show(io::IO, node::DecompNode)
#     print(io, """codim $(length(node.seq)),
#                  reg seq lms $([leading_monomial(p) for p in node.seq]),
#                  nonzero lms: $([leading_monomial(h) for h in node.nonzero])""")
# end

function new_child(node::DecompNode)

    new_node = DecompNode(copy(node.seq),
                          copy(node.added_by_sat),
                          copy(node.nonzero),
                          node.nonzero_processed_until,
                          copy(node.gb),
                          node.gb_known,
                          copy(node.witness_set),
                          copy(node.remaining),
                          node.hyperplanes,
                          node,
                          Dict{POL, Vector{POL}}(),
                          DecompNode[])
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
dimension(node::DecompNode) = ngens(ring(node)) - length(node.seq)
equations(node::DecompNode) = vcat(node.seq, node.added_by_sat..., node.gb)

# compute info about node
function compute_gb!(node::DecompNode)

    if !node.gb_known
        R = ring(node)
        node.gb = equations(node)
        node.nonzero_processed_until = 0
        for h in node.nonzero
            node.gb = msolve_saturate(node.gb, h) 
        end
        # ???????????????????????????????????????????????????????????????
        # ?? WHY DO I HAVE TO DO THIS HERE EVEN IF NONZERO IS NONEMPTY ??
        # ??? AND EVEN IF OSCAR SAIS THAT NODE.GB IS A GRÖBNER BASIS ????
        # ???????????????????????????????????????????????????????????????
        node.gb = gens(f4(ideal(R, node.gb), complete_reduction = true))
        node.gb_known = true
        node.nonzero_processed_until = length(node.nonzero)
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

function reduce(f::POL, node::DecompNode)

    gb = compute_gb!(node)
    return Oscar.normal_form(f, gb)
end

function reduce(f::Vector{POL}, node::DecompNode)
    return [reduce(p, node) for p in f]
end

function does_vanish(node::DecompNode, f::POL;
                     version = "probabilistic")

    if version == "probabilistic"
        gb = msolve_saturate(node.witness_set, f)
        return one(ring(node)) in gb
        # return iszero(Oscar.normal_form(f, node.witness_set))
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
        return delete_and_return!(node.zd_cache, f)
    elseif isnothing(AbstractTrees.parent(node))
        return POL[]
    else
        return find_previous_zds!(AbstractTrees.parent(node), f)
    end
end

function find_nontrivial_zero_divisor!(node::DecompNode, f::POL;
                                       version = "probabilistic")
    G = find_previous_zds!(node, f)
    node.zd_cache[f] = G
    println("trying to find non-trivial zero divisor...")
    while !isempty(node.zd_cache[f])
        println("$(length(node.zd_cache[f])) equations left...")
        g = popfirst!(node.zd_cache[f])
        does_vanish(node, g, version = version) && continue
        return g    
    end
    println("recomputing potential zero divisors...")
    compute_gb!(node)
    G = msolve_saturate(node.gb, f)
    node.zd_cache[f] = G
    println("trying to find non-trivial zero divisor...")
    while !isempty(node.zd_cache[f])
        g = popfirst!(node.zd_cache[f])
        does_vanish(node, g, version = version) && continue
        return g    
    end
    return zero(f)
end

function ann(node::DecompNode, f::POL)

    compute_gb!(node)
    gb = msolve_saturate(node.gb, f)
    res = reduce(gb, node)
    return filter!(p -> !iszero(p), res)
    # return gb
end
        
function zero!(node::DecompNode, 
               append_to_sat::Vector{POL},
               append_to_seq::Vector{POL};
               version = "probabilistic")

    R = ring(node)
    idl_gens = vcat(equations(node), append_to_seq, append_to_sat)
    new_dim = dimension(node) - length(append_to_seq)
    new_witness = version == "probabilistic" ? compute_witness_set(idl_gens, node.nonzero, new_dim, node.hyperplanes) : node.witness_set
    new_node = new_child(node)
    if !isempty(append_to_seq)
        new_node.nonzero_processed_until = 0
    end 
    push!(new_node.added_by_sat, append_to_sat)
    append!(new_node.seq, append_to_seq)
    new_node.witness_set = new_witness
    new_node.gb_known = false
    push!(node.children, new_node)
    return new_node
end

function nonzero!(node::DecompNode, p::POL, known_zd = POL[]; version = "probabilistic")
    R = ring(node)
    new_node = new_child(node)
    push!(new_node.nonzero, p)
    append!(new_node.gb, known_zd)
    new_node.gb_known = false
    new_node.witness_set = version == "probabilistic" ? msolve_saturate(vcat(node.witness_set, known_zd), p) : node.witness_set
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
        new_node = nonzero!(node, p, POL[])
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

function remove_deterministic!(node::DecompNode, P::Vector{POL}, f::POL, zd::POL)

    isempty(P) && return DecompNode[]
    new_nodes = [begin
                     println("setting $(i)th p nonzero: $(p)")
                     new_nd = nonzero!(node, p, version = "deter")
                     push!(new_nd.gb, zd)
                     new_nd
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
                new_nodes[i] = zero!(new_nodes[i], POL[], [q],
                                     version = "determ")
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
    g = find_nontrivial_zero_divisor!(node, f, version = version)
    if iszero(g)
        # f regular
        println("is regular")
        return [zero!(node, POL[], [f], version = version)]
    else # we split
        println("splitting along equation of degree $(total_degree(g)), $(g)")
        H = ann(node, g)
        println("$(length(H)) zero divisors")
        if version == "probabilistic"
            new_nodes = remove!(node, H, f, g)
        else
            new_nodes = remove_deterministic!(node, H, f, g)
        end
        high_dim = zero!(node, H, POL[], version = version)
        res = vcat([high_dim], new_nodes)
        println("$(length(res)) new components")
        return res
    end
end

function decomp(sys::Vector{POL};
                version = "probabilistic")

    isempty(sys) && error("system is empty")
    
    first_eqns = [first(sys)]
    R = parent(first(sys))
    hyperplanes = [random_lin_comb(R, [gens(R)[1:end]..., R(1)]) for _ in 1:ngens(R)]
    initial_witness = version == "probabilistic" ? compute_witness_set(first_eqns, POL[], ngens(R) - 1, hyperplanes) : first_eqns
    initial_node = DecompNode(first_eqns, Vector{POL}[],
                              POL[], 0, first_eqns, true,
                              initial_witness,
                              sys[2:end],
                              hyperplanes,
                              nothing,
                              Dict{POL, Vector{POL}}(),
                              DecompNode[])

    all_processed = all(nd -> isempty(nd.remaining), Leaves(initial_node))
    while !all_processed 
        all_processed = all(nd -> isempty(nd.remaining), Leaves(initial_node))
        for node in Leaves(initial_node)
            isempty(node.remaining) && continue
            if is_empty_set!(node, version = version) 
                empty!(node.remaining)
                continue
            end
            inter!(node, version = version)
            break
        end
    end
    return initial_node
end

#--- User utility functions ---#

function extract_ideals(node::DecompNode)
    R = ring(node)
    for nd in Leaves(node)
        compute_gb!(nd)
    end
    filter!(idl -> !(R(1) in idl), [ideal(R, nd.gb) for nd in Leaves(node)])
end

function print_info(node::DecompNode)
    println("extracting degree/dimension info, this may take a while...")
    R = ring(node)
    comps = filter(nd -> !(R(1) in nd.witness_set), collect(Leaves(node)))
    println("$(length(collect(Leaves(node))) - length(comps)) empty components")
    println("$(length(comps)) non-empty components")
    number_emb_comps = 0
    dim_degree = Dict{Int, Int}([(i, 0) for i in 0:(ngens(R) - 1)])
    sort!(comps, by = nd -> dimension(nd), rev = true)
    for (i, nd) in enumerate(comps)
        ws_gens = copy(nd.witness_set)
        for lower_dim in comps[1:i-1]
            compute_gb!(lower_dim)
            if dimension(lower_dim) > dimension(nd) 
                p = random_lin_comb(R, lower_dim.gb)
                ws_gens = msolve_saturate(ws_gens, p)
            end
        end
        J = radical(ideal(R, ws_gens))
        A, _ = quo(R, J)
        vd = vdim(A)
        if vd > 0
            println("component of dimension $(dimension(nd)), degree $(vd)")
            dim_degree[dimension(nd)] += vd
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
