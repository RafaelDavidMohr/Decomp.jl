const POL = gfp_mpoly
const POLR = GFPMPolyRing
const POLI = MPolyIdeal{POL}

function msolve_saturate_no_elim(idl_gens::Vector{POL}, f::POL)
    R = parent(first(idl_gens))
    vars = gens(R)
    J = ideal(R, [idl_gens..., vars[1]*f - 1])
    gb = f4(J, eliminate = 1, complete_reduction = true, la_option = 42)
    return gens(gb)
end

function msolve_saturate(idl_gens::Vector{POL}, f::POL;
                         infolevel = 0)

    R = parent(f)
    S, vars = PolynomialRing(base_ring(R), pushfirst!(["y$(i)" for i in 1:ngens(R)], "s"))
    F = hom(R, S, vars[2:end])
    elim_hom = hom(S, R, pushfirst!(gens(R), R(0)))
    J = ideal(S, push!([F(p) for p in idl_gens], vars[1]*F(f) - 1))
    gb = f4(J, eliminate = 1, info_level = infolevel, complete_reduction = true, la_option = 42)
    return (elim_hom).(gens(gb))
end

# for some reason this function doesn't work
function msolve_colon_no_elim(idl_gens::Vector{POL}, f::POL)
    R = parent(first(idl_gens))
    vars = gens(R)
    J = ideal(R, [[vars[1]*p for p in idl_gens]..., (vars[1]-1)*f])
    gb = f4(J, eliminate = 1, complete_reduction = true, la_option = 42)
    @assert all(p -> divides(p, f)[1], gb)
    return filter(p -> !iszero(p), [divides(p, f)[2] for p in gens(gb)])
end

function msolve_colon(idl_gens::Vector{POL}, f::POL;
                      infolevel = 0)

    I = ideal(parent(f), idl_gens)
    R = base_ring(I)
    S, vars = PolynomialRing(base_ring(R), pushfirst!(["y$(i)" for i in 1:ngens(R)], "t"))
    F = hom(R, S, vars[2:end])
    elim_hom = hom(S, R, pushfirst!(gens(R), R(0)))
    J = ideal(S, push!([vars[1]*F(p) for p in gens(I)], (vars[1]-1)*F(f)))
    gb = f4(J, eliminate = 1, info_level = infolevel, complete_reduction = true)
    return [divides(elim_hom(p), f)[2] for p in gb]
end

function compute_witness_set(id_gens::Vector{POL}, nonzero::Vector{POL}, d::Int,
                             hyperplanes::Vector{POL})
    R = parent(first(id_gens))
    # do not incorporate the eliminating variable
    result = vcat(id_gens, hyperplanes[1:d])
    for h in nonzero
        result = msolve_saturate(result, h)
    end
    return result
end

function random_lin_comb(R, P, upper_bound)

    sum([rand(1:upper_bound)*p for p in P])
end

function random_lin_comb(R::POLR, P::Vector{POL})

    random_lin_comb(R, P, characteristic(R) - 1)
end

function random_lin_forms(R::POLR, n::Int)
    return [random_lin_comb(R, vcat(gens(R), [one(R)])) for _ in 1:n]
end

function cyclic(vars)
    n = length(vars)
    pols = [sum(prod(vars[j%n+1] for j in k:k+i) for k in 1:n) for i in 0:n-2]
    push!(pols, prod(vars[i] for i in 1:n)-1)
    return pols
end

function check_decomp(I::POLI,
                      comps::Vector{POLI})

    R = base_ring(I)
    if isempty(comps)
        res = R(1) in I
        println("I is empty: $res")
        return res
    end
    println("checking result, this may take a while...")
    println("checking if I is contained in the intersection:")
    res1 = all(comp -> radical_contained_in(comp, I), comps)
    println(res1)
    println("checking if the intersection is contained in I:")
    sort!(comps, by = J -> dim(J), rev = true)
    J = gens(I)
    for idl in comps
        J = msolve_saturate(J, random_lin_comb(R, gens(idl)))
    end
    res2 = R(1) in J
    println(res2)
    res = res1 && res2
    return res
end

function radical_contained_in(I1::POLI, I2::POLI)

    R = base_ring(I1)
    f = random_lin_comb(R, gens(I2))
    tes = msolve_saturate(gens(I1), f)
    return R(1) in ideal(R, tes)
end

function radical_eq(I1::POLI, I2::POLI)
    radical_contained_in(I1, I2) && radical_contained_in(I2, I1)
end

