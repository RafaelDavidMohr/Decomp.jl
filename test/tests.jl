using Decomp
using Test
using Decomp

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

function radical_eq(I1::POLI, I2::POLI)
    radical_contained_in(I1, I2) && radical_contained_in(I2, I1)
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
        J = DP.msolve_saturate_elim(J, DP.random_lin_comb(R, gens(idl)))
    end
    res2 = R(1) in J
    println(res2)
    res = res1 && res2
    return res
end

@testset "example1" begin
    R, (z1, z2, z3, z4, z5) = PolynomialRing(GF(65521), "z" => 1:5)
    I = [10*z1*z2^2 + z2,
         z4^2*z5 + 10*z4*z5^2,
         z1^2*z2 + z1*z2^2,
         z1^2*z2 + z1*z2^2 + z1*z2*z4 + z2^2*z4 + z1^2*z5 + z1*z2*z5,
         z1^2*z2 + z1*z2^2 + z1*z2*z4 + z2^2*z4 + z2*z4^2 + z1^2*z5 + z1*z2*z5 + z1*z4*z5 + z2*z4*z5 + z1*z5^2,
         z1^2*z2 + z1*z2^2 + z1*z2*z4 + z2^2*z4 + z2*z4^2 + z1^2*z5 + z1*z2*z5 + z1*z4*z5 + z2*z4*z5 + z4^2*z5 + z1*z5^2 + z4*z5^2]
    nd, F = decomp(I)
    comps = extract_ideals(nd, F)
    @test all(idl -> radical_eq(idl, equidimensional_hull(idl)), comps)
    @test check_decomp(ideal(R, I), comps)
end

@testset "cyclic6" begin
    R, vars = PolynomialRing(GF(65521), "x" => 1:6)
    I = DP.cyclic(gens(R))[1:5]
    nd, F = decomp(I)
    comps = extract_ideals(nd, F)
    @test all(idl -> radical_eq(idl, equidimensional_hull(idl)), comps)
    @test check_decomp(ideal(R, I), comps)
end

@testset "example2" begin
    R, (b, c, d, e, f, g, h, i, j, z) = PolynomialRing(GF(65521), "x" => 1:10)
    I = [c*d*j*z,
         3*d*e*f*i*z + 4*b*c*e*i + 4*d*e*f*z,
         4*c*e*g*h*i*z + b*c*e*j*z,
         c*e*f*h*j*z + 2*b*c*f*i*z + 4*g*i*z,
         4*b*c*e*f*i*z + 6*d*f*h*j*z,
         b*c*d*g*i*j + 4*c*d*h*j*z + e*g*j*z,
         4*b*c*e*f*h*z + c*f*g*i*j*z,
         2*b*f*g*h*i*j*z + 3*f*h*j*z,
         4*b*d*e*f*g*h*j + 9*c*d*f*g*h*z + 8*b*d*e*h*j*z,
         c*d*e*f*g*h*i*z + c*d*e*f*h*j*z + b*c*d*e*i*j*z]
    nd, F = decomp(I)
    comps = extract_ideals(nd, F)
    @test all(idl -> radical_eq(idl, equidimensional_hull(idl)), comps)
    @test check_decomp(ideal(R, I), comps)
end
