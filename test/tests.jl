using Decomp
using Oscar
using Test

const DP = Decomp
const POL = gfp_mpoly
const POLR = GFPMPolyRing
const POLI = MPolyIdeal{POL}

function radical_contained_in(I1::POLI, I2::POLI)

    R = base_ring(I1)
    f = DP.random_lin_comb(R, gens(I2))
    tes = DP.msolve_saturate_elim(I1, f)
    Base.iszero(normal_form(R(1), tes))
end

function check_decomp(I::POLI,
                      decomp::Vector{POLI})

    R = base_ring(I)
    println("checking result, this may take a while...")
    println("checking if I is contained in the intersection:")
    res1 = all(comp -> radical_contained_in(J, I), decomp)
    println(res1)
    println("checking if the intersection is contained in I:")
    sort!(decomp, by = J -> dim(J), rev = true)
    for idl in decomp
        J = DP.msolve_saturate_elim(J, random_lin_comb(R, gens(idl)))
    end
    res2 = R(1) in J
    println(res2)
    res = res1 && res2
    return res
end
