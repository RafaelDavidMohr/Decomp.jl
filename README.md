



This is an implementation of an algorithm to decompose algebraic sets
into equidimensional locally closed sets based on the computer algebra
system [Oscar](https://oscar.computeralgebra.de/). To install, clone this repository into a directory of your
choice and add it to your Julia environment:

    git clone https://github.com/RafaelDavidMohr/Decomp.jl.git 

Then inside your Julia REPL run

```julia
julia> using Pkg; Pkg.add("/path/to/clone/of/this/repo/Decomp.jl/")
```


The main function of this package is called `decomp` which takes as
input a `Vector{gfp_mpoly}` of multivariate Oscar polynomials defined
over a finite field of positive characteristic and decomposes the
algebraic set defined by this `Vector` into equidimensional locally
closed sets. We refer to [the Oscar
documentation](https://docs.oscar-system.org/stable/) for more
information about how to define polynomials in Oscar. In addition
`decomp` has the keyword argument `version`. This keyword determines
if a probabilistic (and usually faster) version of the algorithm or a
deterministic version is run. By default it is set to
`"probabilistic"`, for any other value the implementation runs the
deterministic version.

The implementation stores its output in a tree data structure whose
root `decomp` returns. The leaves of this tree represent the decomposition
of the algebraic set defined by the input vector of polynomials. The
ideals associated to these leaves can be extracted with the function
`extract_ideals`: 

```julia
    using Decomp
    R, (x, y, z) = PolynomialRing(GF(11), ["x", "y", "z"]);
    F = [x*y, y*z];
    root = decomp(F);
    extract_ideals(root)
```

returns

```julia
    2-element Vector{MPolyIdeal{gfp_mpoly}}:
     ideal(z, x*y)
     ideal(y)
```

**NOTE**: The behaviour of the algorithm may vary wildly depending on the
order of the elements in the input Vector of polynomials.

