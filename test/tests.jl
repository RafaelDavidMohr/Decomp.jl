using Decomp
using Test
using Decomp

const DP = Decomp
const POL = gfp_mpoly
const POLR = GFPMPolyRing
const POLI = MPolyIdeal{POL}

@testset "example1" begin
    R, (z1, z2, z3, z4, z5) = PolynomialRing(GF(65521), "z" => 1:5)
    I = [10*z1*z2^2 + z2,
         z4^2*z5 + 10*z4*z5^2,
         z1^2*z2 + z1*z2^2,
         z1^2*z2 + z1*z2^2 + z1*z2*z4 + z2^2*z4 + z1^2*z5 + z1*z2*z5,
         z1^2*z2 + z1*z2^2 + z1*z2*z4 + z2^2*z4 + z2*z4^2 + z1^2*z5 + z1*z2*z5 + z1*z4*z5 + z2*z4*z5 + z1*z5^2,
         z1^2*z2 + z1*z2^2 + z1*z2*z4 + z2^2*z4 + z2*z4^2 + z1^2*z5 + z1*z2*z5 + z1*z4*z5 + z2*z4*z5 + z4^2*z5 + z1*z5^2 + z4*z5^2]
    nd = decomp(I)
    comps = extract_ideals(nd)
    @test all(idl -> DP.radical_eq(idl, equidimensional_hull(idl)), comps)
    @test DP.check_decomp(ideal(R, I), comps)
    nd1 = decomp(I, version = "determ")
    comps1 = extract_ideals(nd1)
    @test all(idl -> DP.radical_eq(idl, equidimensional_hull(idl)), comps1)
    @test DP.check_decomp(ideal(R, I), comps1)
end

@testset "cyclic6" begin
    R, vars = PolynomialRing(GF(65521), "x" => 1:6)
    I = DP.cyclic(gens(R))[1:5]
    nd = decomp(I)
    comps = extract_ideals(nd)
    @test all(idl -> DP.radical_eq(idl, equidimensional_hull(idl)), comps)
    @test DP.check_decomp(ideal(R, I), comps)
    nd1 = decomp(I, version = "determ")
    comps1 = extract_ideals(nd1)
    @test all(idl -> DP.radical_eq(idl, equidimensional_hull(idl)), comps1)
    @test DP.check_decomp(ideal(R, I), comps1)
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
    nd = decomp(I)
    comps = extract_ideals(nd)
    @test all(idl -> DP.radical_eq(idl, equidimensional_hull(idl)), comps)
    @test DP.check_decomp(ideal(R, I), comps)
    nd1 = decomp(I, version = "determ")
    comps1 = extract_ideals(nd1)
    @test all(idl -> DP.radical_eq(idl, equidimensional_hull(idl)), comps1)
    @test DP.check_decomp(ideal(R, I), comps1)
end
