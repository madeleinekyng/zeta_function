load "count_plane_model.m";
load "compute_corrections.m";
load "compute_zeta_function.m";

SetGPU(true);

A<x,y> := AffineSpace(GF(2),2);
curve_polynomials := [*
    x + 1,
    x^2*y + x^2 + x*y + x + y^3 + y^2 + y,
    x^3 + x^2*y + x*y^3 + x*y^2 + x + y^2 + y,
    x^4 + x^3*y + x^2*y^2 + x*y + y^4 + y + 1,
    x^5 + x^4*y + x^4 + x^3*y + x^2*y^2 + x*y^4 + x*y^3 + x*y^2 + x + y^5 + y^4 
        + 1,
    x^5*y + x^5 + x^4*y + x^4 + x^3*y + x^2*y + x*y^4 + x*y^3 + x*y + x + y^6 + 
        y^5 + y^3 + y + 1,
    x^5*y + x^5 + x^4*y^2 + x^3*y^3 + x^2*y + x^2 + x*y^5 + x*y^3 + x*y + x + 
        y^4 + y^2,
    x^6 + x^5*y^2 + x^5 + x^4*y + x^4 + x^3*y^4 + x^3*y^3 + x^2*y^5 + x^2*y^4 + 
        x^2*y^3 + x^2*y + x*y^6 + x*y^5 + x*y^4 + x + y^6 + y^5 + y^4 + y^3 + 
        y^2 + 1,
    x^7*y + x^7 + x^6*y + x^6 + x^5*y + x^5 + x^4*y^3 + x^4*y^2 + x^4*y + x^4 + 
        x^3*y^5 + x^3*y^3 + x^2*y^4 + x^2*y^3 + x^2*y + x*y^7 + x*y^5 + x + y^8 
        + y^7 + y^6 + y^4 + y^3 + y,
    x^8 + x^6*y + x^5*y^3 + x^5 + x^4*y^4 + x^4*y^2 + x^4 + x^3*y^5 + x^3*y^3 + 
        x^3*y^2 + x^3 + x^2*y^4 + x^2*y^2 + x^2*y + x^2 + x*y^7 + x*y^5 + x*y^4 
        + x*y^2 + x + y^8 + y^5 + y^4 + y^2 + 1,
    x^9 + x^8*y + x^8 + x^6 + x^5*y^4 + x^5*y^3 + x^5*y^2 + x^4*y^3 + x^4*y + 
        x^3*y^5 + x^3*y^4 + x^3*y^3 + x^3*y^2 + x^3*y + x^2*y^7 + x^2*y^3 + 
        x^2*y + x^2 + x*y^6 + x*y^4 + x*y^2 + x*y + x + y^9 + y^8 + y^2,
    x^9*y + x^9 + x^8*y^2 + x^8 + x^7*y^2 + x^7*y + x^6*y^2 + x^6 + x^5*y + x^4*y^6 
    + x^4*y^2 + x^4*y + x^4 + x^3*y^7 + x^3*y^5 + x^3 + x^2*y^8 + x^2*y^6 + 
    x^2*y^5 + x^2 + x*y^9 + x*y^7 + x*y^2 + y^10 + y^9 + y^6 + y^2,
    x^9*y + x^8*y^2 + x^7*y^3 + x^7*y^2 + x^7*y + x^7 + x^6*y^4 + x^6*y^3 + x^6*y^2 
    + x^6*y + x^6 + x^5*y^2 + x^5 + x^4*y^4 + x^4*y^2 + x^4 + x^3*y^7 + x^3*y^6 
    + x^3 + x^2*y^7 + x^2*y^6 + x^2*y^3 + x^2*y^2 + x*y^9 + x*y^4 + x*y^3 + x + 
    y^9 + y^6 + y^2 + y,
    x^11 + x^9*y^2 + x^8*y^3 + x^8 + x^7*y + x^7 + x^6*y^3 + x^6*y + x^6 + x^5*y^5 +
    x^5*y^4 + x^5*y^2 + x^5*y + x^5 + x^4*y^7 + x^4*y^5 + x^4*y^4 + x^4*y^3 + 
    x^4*y^2 + x^3*y^7 + x^3*y^5 + x^3*y^4 + x^3*y^3 + x^3*y + x^2*y^7 + x^2*y^4 
    + x^2*y^2 + x^2*y + x^2 + x*y^10 + x*y^8 + x*y^7 + x*y^3 + x*y + x + y^10 + 
    y^9 + y^8 + y^5 + y^3 + 1,
    x^11*y + x^10 + x^9*y + x^8*y^4 + x^8*y^2 + x^8 + x^7*y^3 + x^6*y^6 + x^6*y^5 + 
    x^6*y^4 + x^5*y^7 + x^5*y^3 + x^5*y^2 + x^5 + x^4*y^5 + x^4*y^2 + x^4*y + 
    x^4 + x^3*y^9 + x^3*y^8 + x^3*y^7 + x^3*y^4 + x^2*y^10 + x^2*y^9 + x^2*y^4 +
    x^2*y^3 + x^2*y^2 + x^2*y + x*y^11 + x*y^9 + x*y^8 + x*y^7 + x*y^2 + y^7 + 
    y^4 + y^2 + y + 1,
    x^11*y + x^10*y^2 + x^10*y + x^9*y^3 + x^9*y^2 + x^9*y + x^9 + x^8*y^4 + x^8*y^3
    + x^7*y^3 + x^7*y + x^7 + x^6*y^6 + x^6*y^5 + x^6*y^4 + x^6*y^3 + x^6*y + 
    x^6 + x^5*y^7 + x^5*y^3 + x^5*y^2 + x^5*y + x^4*y^7 + x^4*y^6 + x^4*y^5 + 
    x^4*y^3 + x^4*y + x^4 + x^3*y^6 + x^3*y^3 + x^3*y^2 + x^3*y + x^3 + x^2*y^5 
    + x^2*y^4 + x^2*y^2 + x^2*y + x*y^10 + x*y^9 + x*y^7 + x*y^4 + x*y^3 + x*y^2
    + x*y + x + y^12 + y^10 + y^9 + y^7 + y^6 + y^5 + y^3 + 1,
    x^13 + x^12 + x^11*y + x^10*y^3 + x^10 + x^9*y + x^9 + x^8*y^5 + x^8*y + x^8 + 
    x^7*y^3 + x^7 + x^6*y^4 + x^6*y + x^6 + x^5*y^8 + x^5*y^5 + x^5*y^4 + 
    x^5*y^2 + x^5*y + x^5 + x^4*y^9 + x^4*y^8 + x^4*y^7 + x^4*y^6 + x^4*y + x^4 
    + x^3*y^10 + x^3*y^9 + x^3*y^6 + x^3*y^4 + x^3*y^3 + x^3*y + x^3 + x^2*y^10 
    + x^2*y^9 + x^2*y^7 + x^2*y^6 + x^2*y^5 + x^2*y + x*y^10 + x*y^5 + x*y^4 + 
    x*y^3 + x*y^2 + x + y^13 + y^12 + y^10 + y^8 + y^6 + y^5 + y^4 + 1,
    x^12 + x^11*y^2 + x^11 + x^10*y^4 + x^10*y^2 + x^9*y^5 + x^9*y^4 + x^9*y^3 + 
    x^9*y^2 + x^9*y + x^9 + x^8*y^4 + x^8*y^3 + x^8*y^2 + x^8 + x^7*y^6 + 
    x^7*y^4 + x^7*y^2 + x^7 + x^6*y^8 + x^6*y^7 + x^6*y^3 + x^6*y^2 + x^5*y^8 + 
    x^5*y^4 + x^5*y^2 + x^5*y + x^4*y^9 + x^4*y^6 + x^4*y^3 + x^4*y^2 + x^4*y + 
    x^4 + x^3*y^9 + x^3*y^7 + x^3*y^6 + x^3*y^4 + x^2*y^11 + x^2*y^9 + x^2*y^5 +
    x^2*y^3 + x*y^13 + x*y^12 + x*y^10 + x*y^8 + x*y^7 + x*y^6 + x*y^5 + x*y^3 +
    x*y + x + y^14 + y^13 + y^11 + y^7 + y^3 + y^2 + y,
    x^14 + x^12*y^2 + x^12*y + x^12 + x^11*y^3 + x^11*y^2 + x^10*y^4 + x^10*y^3 + 
    x^10 + x^9*y^5 + x^9*y^4 + x^9*y^3 + x^9 + x^8*y^6 + x^8*y^5 + x^8*y^4 + 
    x^8*y^2 + x^8*y + x^7*y^7 + x^7*y^5 + x^7*y^4 + x^7*y + x^6*y^7 + x^6*y^6 + 
    x^6*y^5 + x^6*y^4 + x^6*y + x^6 + x^5*y^9 + x^5*y^4 + x^4*y^10 + x^4*y^9 + 
    x^4*y^7 + x^4*y^6 + x^4*y^4 + x^4 + x^3*y^9 + x^3*y^7 + x^3*y^6 + x^3*y^3 + 
    x^2*y^5 + x^2*y^4 + x^2*y^3 + x^2*y^2 + x^2 + x*y^12 + x*y^10 + x*y^8 + 
    x*y^3 + x*y + x + y^14 + y^10 + y^8 + y^6 + 1
*];

C := Curve(A, curve_polynomials[g+1]);
Genus(C);
"Version 2";
b := ComputeZetaFunctionNumerator(C : Version := 2);