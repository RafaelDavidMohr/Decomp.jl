const POL = gfp_mpoly
const POLR = GFPMPolyRing
const POLI = MPolyIdeal{POL}

function msolve_saturate_elim(I::POLI, f::POL;
                              infolevel = 0)

    R = base_ring(I)
    S, vars = PolynomialRing(base_ring(R), pushfirst!(["y$(i)" for i in 1:ngens(R)], "s"))
    F = hom(R, S, vars[2:end])
    elim_hom = hom(S, R, pushfirst!(gens(R), R(0)))
    J = ideal(S, push!([F(p) for p in gens(I)], vars[1]*F(f) - 1))
    gb = f4(J, eliminate = 1, info_level = infolevel, complete_reduction = true)
    return ideal(R, [elim_hom(p) for p in gb])
end

function msolve_colon_elim(I::POLI, f::POL;
                           infolevel = 0)

    R = base_ring(I)
    S, vars = PolynomialRing(base_ring(R), pushfirst!(["y$(i)" for i in 1:ngens(R)], "t"))
    F = hom(R, S, vars[2:end])
    elim_hom = hom(S, R, pushfirst!(gens(R), R(0)))
    J = ideal(S, push!([vars[1]*F(p) for p in gens(I)], (vars[1]-1)*F(f)))
    gb = f4(J, eliminate = 1, info_level = infolevel, complete_reduction = true)
    return ideal(R, [divides(elim_hom(p), f)[2] for p in gb])
end

function random_lin_comb(R, P, upper_bound)

    sum([rand(1:upper_bound)*p for p in P])
end

function random_lin_comb(R::POLR, P::Vector{POL})

    random_lin_comb(R, P, characteristic(R) - 1)
end

function cyclic(vars)
    n = length(vars)
    pols = [sum(prod(vars[j%n+1] for j in k:k+i) for k in 1:n) for i in 0:n-2]
    push!(pols, prod(vars[i] for i in 1:n)-1)
    return pols
end

function test_other_split(I::POLI, H::Vector{POL})
    R = base_ring(I)
    res = POLI[]
    P = POL[]
    sizehint!(res, length(H))
    sizehint!(res, length(H))
    curr_ideal = I
    for (i, h) in enumerate(H)
        println("saturating by $(i)th h")
        component = msolve_saturate_elim(curr_ideal, h)
        for (j, p) in enumerate(P)
            println("saturating by $(j)th p")
            println(p)
            component = msolve_saturate_elim(component, p)
        end
        push!(res, component)
        curr_ideal = curr_ideal + ideal(R, h)
        println(curr_ideal)
        push!(P, random_lin_comb(R, gens(component)))
        println("-------")
    end
    return res
end

function check_decomp(I::POLI,
                      comps::Vector{POLI})

    R = base_ring(I)
    println("checking result, this may take a while...")
    println("checking if I is contained in the intersection:")
    res1 = all(comp -> radical_contained_in(comp, I), comps)
    println(res1)
    println("checking if the intersection is contained in I:")
    sort!(comps, by = J -> dim(J), rev = true)
    J = I
    for idl in comps
        J = msolve_saturate_elim(J, q, random_lin_comb(R, gens(idl)))
    end
    res2 = R(1) in J
    println(res2)
    res = res1 && res2
    return res
end

function radical_contained_in(I1::POLI, I2::POLI)

    R = base_ring(I1)
    f = random_lin_comb(R, gens(I2))
    tes = msolve_saturate_elim(I1, f)
    Base.iszero(normal_form(R(1), tes))
end

function radical_eq(I1::POLI, I2::POLI)
    radical_contained_in(I1, I2) && radical_contained_in(I2, I1)
end

