const POL = gfp_mpoly
const POLR = GFPMPolyRing
const POLI = MPolyIdeal{POL}

function msolve_saturate_elim(I::POLI, f::POL;
                              infolevel = 0)

    R = base_ring(I)
    S, vars = PolynomialRing(base_ring(R), pushfirst!(["y$(i)" for i in 1:ngens(R)], "t"))
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
