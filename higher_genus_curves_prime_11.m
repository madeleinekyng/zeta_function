load "count_plane_model.m";
load "compute_corrections.m";
load "compute_zeta_function.m";

SetGPU(true);

A<x,y> := AffineSpace(GF(11),2);
curve_polynomials := [*
    x^2 + x*y + x + y^2 + y + 1,
    x^3 + x^2*y + x^2 + x*y^2 + x*y + x + y^3 + y^2 + y + 1,
    x^4 + x^3*y + 5*x^3 + 4*x^2*y^2 + 2*x^2*y + x^2 + x*y^3 + 10*x*y^2 + 10*x*y 
        + x + 6*y^4 + 3*y^3 + 7*y^2 + 9*y + 10,
    x^4 + x^3*y + x^3 + x^2*y^2 + x^2*y + x^2 + x*y^3 + x*y^2 + x*y + x + y^4 + 
        y^3 + y^2 + y + 1,
    x^5 + x^4*y + x^4 + x^3*y^2 + 5*x^3*y + 5*x^3 + 10*x^2*y^3 + 10*x^2*y^2 + 
        4*x^2*y + 4*x^2 + x*y^4 + 5*x*y^3 + 7*x*y^2 + 4*x*y + 2*x + 2*y^5 + y^4 
        + 10*y^3 + 7*y^2 + 2*y + 5,
    2*x^6 + 6*x^5*y + x^5 + 4*x^4*y^2 + 3*x^4*y + 4*x^4 + 4*x^3*y^3 + 2*x^3*y^2 
        + 6*x^3*y + x^3 + 9*x^2*y^4 + 5*x^2*y^3 + x^2*y^2 + 10*x^2*y + 9*x^2 + 
        4*x*y^5 + 2*x*y^4 + 2*x*y^2 + 9*x*y + 8*x + y^6 + 3*y^5 + 10*y^4 + 2*y^3
        + 2*y^2 + 6*y + 7,
    x^6 + x^5*y + x^5 + 7*x^4*y^2 + 10*x^4*y + 2*x^3*y^3 + x^3*y^2 + 9*x^3*y + 
        8*x^3 + 3*x^2*y^4 + 2*x^2*y^3 + 4*x^2*y^2 + x^2*y + x^2 + x*y^5 + 
        3*x*y^4 + 6*x*y^3 + x*y + 6*x + 9*y^6 + 4*y^5 + y^4 + 9*y^3 + 2*y^2 + 
        3*y + 7,
    x^7 + 9*x^6*y + 8*x^6 + 8*x^5*y^2 + 10*x^5*y + 3*x^5 + 7*x^4*y^3 + x^4*y^2 +
        4*x^4*y + 9*x^4 + 5*x^3*y^4 + 10*x^3*y^3 + 4*x^3*y^2 + 2*x^3*y + x^3 + 
        8*x^2*y^5 + 3*x^2*y^4 + 5*x^2*y^3 + 2*x^2*y^2 + 4*x^2*y + 8*x^2 + 
        10*x*y^6 + 9*x*y^5 + 3*x*y^4 + 4*x*y^2 + 8*x*y + 10*x + 6*y^6 + y^5 + 
        5*y^4 + 7*y^3 + 8*y^2 + y + 6,
    6*x^8 + 3*x^7*y + 6*x^7 + 2*x^6*y^2 + 6*x^6*y + 4*x^5*y^3 + 9*x^5*y^2 + 
        10*x^5*y + 10*x^5 + 8*x^4*y^4 + 2*x^4*y^3 + 3*x^4*y^2 + 9*x^4 + 
        9*x^3*y^5 + 4*x^3*y^4 + 7*x^3*y^2 + 5*x^3*y + 9*x^3 + 7*x^2*y^6 + 
        7*x^2*y^5 + 4*x^2*y^4 + 4*x^2*y^3 + 10*x^2*y^2 + 10*x^2*y + 6*x^2 + 
        9*x*y^7 + 4*x*y^6 + x*y^5 + 7*x*y^4 + 4*x*y^3 + 3*x*y^2 + 2*x*y + 9*x + 
        7*y^8 + 9*y^7 + 2*y^6 + 8*y^5 + 4*y^4 + 6*y^3 + 6*y^2 + 2*y + 10,
    x^8 + 10*x^7*y + 2*x^6*y^2 + 6*x^6*y + 8*x^6 + 6*x^5*y^3 + 3*x^5*y^2 + 
        2*x^5*y + 6*x^5 + 3*x^4*y^4 + 6*x^4*y^3 + 5*x^4*y + 7*x^4 + 6*x^3*y^5 + 
        2*x^3*y^4 + 6*x^3*y^3 + 5*x^3*y^2 + x^3*y + 5*x^3 + 9*x^2*y^6 + 
        6*x^2*y^5 + 8*x^2*y^4 + 3*x^2*y^3 + 9*x^2*y^2 + x^2*y + 7*x^2 + 6*x*y^7 
        + 6*x*y^6 + 6*x*y^5 + 10*x*y^4 + 6*x*y^3 + 2*x*y^2 + x + 7*y^8 + 8*y^7 +
        2*y^6 + 2*y^5 + 10*y^4 + 4*y^2 + 6,
    x^9 + 8*x^8*y + 2*x^8 + 7*x^7*y^2 + x^7*y + 2*x^7 + 4*x^6*y^2 + 5*x^6*y + 
        x^5*y^4 + 6*x^5*y^2 + 2*x^5*y + 4*x^5 + 5*x^4*y^5 + 9*x^4*y^4 + 
        8*x^4*y^3 + 6*x^4*y^2 + 2*x^4*y + 2*x^4 + 8*x^3*y^6 + 5*x^3*y^5 + 
        6*x^3*y^4 + 7*x^3*y^3 + 4*x^3*y^2 + 5*x^3*y + x^3 + 10*x^2*y^7 + x^2*y^5
        + 5*x^2*y^4 + 6*x^2*y^3 + 9*x^2*y^2 + 5*x^2*y + 9*x^2 + 3*x*y^7 + 
        10*x*y^6 + 6*x*y^4 + 10*x*y^3 + x*y^2 + 8*x*y + 5*x + 8*y^8 + 7*y^7 + 
        4*y^6 + 3*y^5 + y^4 + 3*y^3 + 5*y^2 + 4*y + 6,
    5*x^10 + 9*x^9*y + 8*x^9 + 6*x^8*y^2 + 7*x^8*y + 6*x^8 + 10*x^7*y^3 + 
        4*x^7*y^2 + 10*x^7*y + 9*x^7 + 3*x^6*y^4 + 5*x^6*y^3 + 10*x^6*y^2 + 
        4*x^6*y + 9*x^6 + 8*x^5*y^5 + 5*x^5*y^4 + 6*x^5*y^3 + 6*x^5*y^2 + 
        6*x^5*y + 4*x^4*y^6 + 6*x^4*y^5 + 7*x^4*y^4 + 9*x^4*y^3 + 9*x^4*y^2 + 
        x^4*y + 4*x^4 + 10*x^3*y^7 + 8*x^3*y^6 + 5*x^3*y^5 + 7*x^3*y^3 + 
        4*x^3*y^2 + x^3*y + 4*x^3 + 3*x^2*y^8 + 4*x^2*y^7 + 6*x^2*y^6 + 
        2*x^2*y^5 + 5*x^2*y^4 + 4*x^2*y^3 + 10*x^2*y^2 + 4*x^2*y + 6*x^2 + 
        6*x*y^9 + 7*x*y^8 + 9*x*y^7 + 3*x*y^6 + 5*x*y^5 + 9*x*y^4 + 4*x*y^3 + 
        7*x*y^2 + 10*x*y + 10*x + 6*y^10 + 10*y^9 + y^7 + 5*y^6 + 10*y^5 + 9*y^4
        + y^3 + 5*y^2 + 2*y + 7,
    x^10 + 3*x^9*y + 10*x^9 + 3*x^8*y^2 + 6*x^8*y + 10*x^8 + 9*x^7*y^3 + 
        4*x^7*y^2 + x^7*y + 9*x^7 + 4*x^6*y^4 + 7*x^6*y^3 + 8*x^6*y^2 + 10*x^6*y
        + 3*x^6 + x^5*y^5 + 4*x^5*y^4 + x^5*y^3 + 5*x^5*y^2 + x^5*y + 6*x^5 + 
        5*x^4*y^6 + 2*x^4*y^5 + 8*x^4*y^4 + 10*x^4*y^3 + 2*x^4*y^2 + 9*x^4*y + 
        x^4 + 6*x^3*y^7 + 9*x^3*y^6 + 2*x^3*y^5 + 4*x^3*y^3 + 7*x^3*y^2 + 
        4*x^3*y + 5*x^3 + 2*x^2*y^7 + 3*x^2*y^6 + 9*x^2*y^5 + 7*x^2*y^4 + 
        2*x^2*y^3 + 8*x^2 + 5*x*y^9 + 10*x*y^8 + 4*x*y^7 + x*y^6 + 2*x*y^5 + 
        6*x*y^4 + 6*x*y^3 + 7*x*y^2 + 5*x*y + x + 10*y^10 + 7*y^9 + 10*y^8 + 
        5*y^6 + 7*y^5 + 8*y^4 + 8*y^3 + 6*y,
    3*x^11 + x^10*y + 4*x^10 + 7*x^9*y^2 + 8*x^9*y + 2*x^9 + 5*x^8*y^3 + 
        2*x^8*y^2 + 10*x^8 + 5*x^7*y^4 + 2*x^7*y^3 + 5*x^7*y^2 + 8*x^7*y + 2*x^7
        + 4*x^6*y^5 + 8*x^6*y^4 + 4*x^6*y^3 + 6*x^6*y^2 + 4*x^6*y + 4*x^6 + 
        x^5*y^5 + 6*x^5*y^4 + 10*x^5*y^3 + x^5*y^2 + 4*x^5*y + 6*x^5 + x^4*y^7 +
        4*x^4*y^5 + 3*x^4*y^4 + x^4*y^3 + 6*x^4*y + 4*x^4 + 2*x^3*y^8 + 
        10*x^3*y^7 + x^3*y^6 + 8*x^3*y^5 + 6*x^3*y^4 + 9*x^3*y^3 + 10*x^3*y^2 + 
        9*x^3*y + 6*x^3 + 10*x^2*y^9 + 9*x^2*y^8 + 6*x^2*y^7 + 7*x^2*y^6 + 
        9*x^2*y^5 + 2*x^2*y^4 + 9*x^2*y^3 + x^2*y + 9*x^2 + 2*x*y^10 + 2*x*y^9 +
        x*y^8 + 7*x*y^7 + 3*x*y^6 + 10*x*y^4 + 10*x*y^3 + 3*x*y^2 + 3*x*y + 9*x 
        + 10*y^10 + 8*y^9 + 8*y^7 + 7*y^6 + 10*y^5 + 5*y^4 + 2*y^3 + 2*y^2 + 5*y
        + 1,
    3*x^12 + 4*x^11*y + 2*x^11 + 10*x^10*y^2 + 9*x^10*y + 10*x^10 + 2*x^9*y^3 + 
        4*x^9*y^2 + 2*x^9*y + 6*x^9 + 7*x^8*y^4 + 7*x^8*y^3 + x^8*y^2 + 8*x^8*y 
        + 10*x^8 + 2*x^7*y^5 + 6*x^7*y^4 + 9*x^7*y^3 + 7*x^7*y^2 + 8*x^7*y + 
        3*x^7 + 2*x^6*y^5 + x^6*y^3 + x^6*y^2 + 9*x^6*y + 10*x^6 + 8*x^5*y^7 + 
        2*x^5*y^6 + 6*x^5*y^5 + 5*x^5*y^4 + 3*x^5*y^3 + 8*x^5*y^2 + 8*x^5*y + 
        7*x^5 + 5*x^4*y^8 + 4*x^4*y^7 + 3*x^4*y^6 + 2*x^4*y^5 + 9*x^4*y^4 + 
        6*x^4*y^3 + 9*x^4*y^2 + 8*x^4*y + 2*x^4 + 7*x^3*y^9 + 4*x^3*y^8 + 
        x^3*y^7 + x^3*y^6 + x^3*y^5 + 10*x^3*y^4 + 3*x^3*y^3 + 3*x^3*y^2 + 
        10*x^3*y + 6*x^3 + 8*x^2*y^10 + 8*x^2*y^9 + 7*x^2*y^8 + 6*x^2*y^7 + 
        4*x^2*y^6 + 2*x^2*y^5 + 4*x^2*y^4 + x^2*y^3 + 10*x^2*y^2 + 5*x^2*y + 
        4*x^2 + 6*x*y^11 + 6*x*y^10 + 9*x*y^9 + 8*x*y^8 + 9*x*y^7 + 3*x*y^5 + 
        4*x*y^4 + 8*x*y^3 + x*y^2 + 2*x*y + 4*x + 3*y^11 + 7*y^10 + 6*y^9 + 
        7*y^8 + 3*y^7 + 2*y^5 + 8*y^4 + 8*y^3 + 4*y^2 + 9*y + 1,
    6*x^12 + 9*x^11*y + 8*x^11 + 4*x^10*y^2 + 5*x^10*y + 7*x^9*y^3 + 3*x^9*y^2 +
        2*x^9*y + 9*x^9 + x^8*y^4 + 5*x^8*y^3 + 3*x^8*y^2 + 5*x^8*y + 2*x^8 + 
        10*x^7*y^5 + 10*x^7*y^4 + 10*x^7*y^3 + 9*x^7*y^2 + 3*x^7*y + 6*x^7 + 
        10*x^6*y^6 + x^6*y^5 + 10*x^6*y^4 + 6*x^6*y^3 + 10*x^6*y^2 + 3*x^6*y + 
        8*x^6 + 9*x^5*y^7 + 4*x^5*y^6 + 5*x^5*y^5 + 10*x^5*y^4 + 4*x^5*y^3 + 
        5*x^5*y^2 + 8*x^5*y + 2*x^5 + 9*x^4*y^8 + 4*x^4*y^7 + 7*x^4*y^6 + 
        4*x^4*y^5 + x^4*y^4 + 8*x^4*y^3 + 3*x^4*y^2 + 3*x^4*y + 10*x^4 + 
        7*x^3*y^9 + x^3*y^8 + 7*x^3*y^7 + x^3*y^6 + 5*x^3*y^5 + x^3*y^4 + 
        3*x^3*y^3 + 6*x^3*y^2 + 3*x^3*y + 3*x^3 + 6*x^2*y^10 + 9*x^2*y^9 + 
        2*x^2*y^8 + 6*x^2*y^7 + 6*x^2*y^6 + 2*x^2*y^4 + 4*x^2*y^3 + 6*x^2*y^2 + 
        8*x^2*y + 6*x^2 + 8*x*y^11 + 4*x*y^10 + x*y^9 + 3*x*y^8 + 10*x*y^7 + 
        2*x*y^6 + x*y^5 + x*y^4 + 6*x*y^3 + 10*x*y^2 + 6*x + 5*y^12 + y^11 + 
        4*y^10 + y^8 + 3*y^6 + 2*y^5 + 3*y^4 + y^3 + 7*y^2 + 5*y + 3,
    3*x^13 + 8*x^12*y + 9*x^11*y^2 + 8*x^11*y + 3*x^10*y^3 + 9*x^10*y^2 + x^10*y
        + 2*x^10 + 9*x^9*y^4 + 8*x^9*y^3 + 5*x^9*y^2 + 10*x^9*y + x^9 + 
        8*x^8*y^5 + 9*x^8*y^4 + x^8*y^3 + 10*x^8*y^2 + 4*x^8*y + 8*x^8 + 
        2*x^7*y^6 + 9*x^7*y^5 + 2*x^7*y^4 + 6*x^7*y^3 + 2*x^7*y^2 + 10*x^7*y + 
        6*x^6*y^7 + 4*x^6*y^6 + 2*x^6*y^5 + 2*x^6*y^4 + 6*x^6*y^3 + 5*x^6*y^2 + 
        10*x^6*y + 9*x^6 + 5*x^5*y^8 + 10*x^5*y^7 + 2*x^5*y^6 + 3*x^5*y^5 + 
        8*x^5*y^4 + 7*x^5*y^3 + 6*x^5*y^2 + 3*x^5*y + 3*x^5 + x^4*y^9 + 
        5*x^4*y^7 + 2*x^4*y^6 + 2*x^4*y^5 + 10*x^4*y^4 + 9*x^4*y^3 + 5*x^4*y^2 +
        3*x^4*y + 6*x^4 + 8*x^3*y^10 + 5*x^3*y^9 + 2*x^3*y^8 + 7*x^3*y^7 + 
        8*x^3*y^6 + 10*x^3*y^5 + 3*x^3*y^3 + 10*x^3*y^2 + 3*x^3*y + 6*x^3 + 
        9*x^2*y^11 + 8*x^2*y^10 + 3*x^2*y^9 + 6*x^2*y^8 + 3*x^2*y^7 + x^2*y^6 + 
        3*x^2*y^5 + 10*x^2*y^4 + 5*x^2*y^3 + 10*x^2*y + 5*x^2 + 2*x*y^12 + 
        2*x*y^11 + 4*x*y^9 + 2*x*y^8 + 8*x*y^7 + 9*x*y^6 + 8*x*y^5 + 9*x*y^4 + 
        4*x*y^3 + 5*x*y^2 + 3*x*y + 9*x + 5*y^13 + 2*y^12 + 3*y^11 + y^10 + 
        3*y^9 + y^8 + 4*y^6 + 10*y^5 + y^3 + 3*y^2 + 10*y + 9,
    x^14 + 7*x^13*y + 3*x^13 + 2*x^12*y + 8*x^11*y^3 + 6*x^11*y^2 + 5*x^11*y + 
        x^11 + 9*x^10*y^4 + 2*x^10*y^3 + 7*x^10*y^2 + 9*x^10*y + 5*x^10 + 
        8*x^9*y^5 + 2*x^9*y^4 + 3*x^9*y^3 + 3*x^9*y^2 + 3*x^9*y + 7*x^9 + 
        3*x^8*y^6 + 5*x^8*y^4 + 7*x^8*y^3 + 2*x^8*y^2 + 5*x^8*y + 2*x^8 + 
        7*x^7*y^7 + 4*x^7*y^6 + 6*x^7*y^5 + 9*x^7*y^4 + x^7*y^3 + 5*x^7*y^2 + 
        6*x^7*y + 8*x^7 + 5*x^6*y^8 + 9*x^6*y^7 + 3*x^6*y^5 + 4*x^6*y^4 + 
        2*x^6*y^3 + x^6*y^2 + x^6*y + 6*x^6 + 4*x^5*y^9 + 5*x^5*y^8 + 6*x^5*y^7 
        + 5*x^5*y^6 + 2*x^5*y^5 + 6*x^5*y^3 + 8*x^5*y^2 + 3*x^5*y + 5*x^5 + 
        2*x^4*y^10 + 7*x^4*y^9 + 6*x^4*y^8 + 6*x^4*y^7 + 4*x^4*y^6 + 10*x^4*y^4 
        + 3*x^4*y^2 + 2*x^4*y + 3*x^4 + 8*x^3*y^11 + 6*x^3*y^10 + 5*x^3*y^9 + 
        x^3*y^8 + 2*x^3*y^7 + 2*x^3*y^6 + 5*x^3*y^5 + 4*x^3*y^4 + 8*x^3*y^3 + 
        x^3*y^2 + 10*x^3*y + 9*x^2*y^12 + 5*x^2*y^11 + 9*x^2*y^10 + 4*x^2*y^9 + 
        8*x^2*y^8 + 7*x^2*y^7 + 8*x^2*y^6 + 10*x^2*y^5 + 4*x^2*y^4 + 2*x^2*y^3 +
        x^2*y^2 + 3*x^2*y + 7*x^2 + 5*x*y^13 + x*y^12 + 9*x*y^11 + 6*x*y^10 + 
        8*x*y^8 + x*y^7 + x*y^6 + 2*x*y^5 + 3*x*y^4 + 3*x*y^2 + 4*x + 6*y^14 + 
        y^13 + 10*y^11 + 8*y^9 + 5*y^8 + 5*y^7 + y^6 + y^5 + 2*y^3 + 4*y^2 + 1,
    4*x^14 + 9*x^13*y + 8*x^13 + 8*x^12*y^2 + 3*x^12*y + 7*x^12 + x^11*y^3 + 
        x^11*y^2 + 10*x^11*y + 8*x^11 + 2*x^10*y^3 + 2*x^10*y^2 + 8*x^10*y + 
        9*x^10 + 7*x^9*y^5 + 8*x^9*y^4 + 7*x^9*y^3 + 8*x^9*y + 7*x^9 + 
        10*x^8*y^6 + 7*x^8*y^5 + 2*x^8*y^3 + x^8*y^2 + 9*x^8*y + 8*x^8 + 
        5*x^7*y^7 + 10*x^7*y^6 + 4*x^7*y^5 + 3*x^7*y^4 + 7*x^7*y^3 + 6*x^7*y^2 +
        9*x^7*y + 8*x^7 + 7*x^6*y^8 + 6*x^6*y^7 + 7*x^6*y^6 + 8*x^6*y^5 + 
        8*x^6*y^3 + 2*x^6*y^2 + 4*x^6*y + 6*x^6 + 3*x^5*y^9 + 9*x^5*y^8 + 
        6*x^5*y^7 + x^5*y^6 + 8*x^5*y^5 + 9*x^5*y^3 + 7*x^5*y^2 + 6*x^5*y + 
        10*x^5 + x^4*y^10 + 4*x^4*y^9 + 6*x^4*y^8 + 8*x^4*y^7 + 9*x^4*y^6 + 
        6*x^4*y^5 + 8*x^4*y^4 + 10*x^4*y^2 + 9*x^4*y + 10*x^4 + x^3*y^11 + 
        6*x^3*y^10 + 7*x^3*y^9 + 8*x^3*y^8 + 9*x^3*y^6 + 5*x^3*y^5 + 8*x^3*y^4 +
        5*x^3*y^2 + 10*x^3 + 6*x^2*y^12 + 8*x^2*y^11 + 5*x^2*y^9 + 6*x^2*y^8 + 
        9*x^2*y^7 + 4*x^2*y^6 + 6*x^2*y^5 + 5*x^2*y^4 + 2*x^2*y^3 + 7*x^2*y^2 + 
        5*x^2*y + 2*x^2 + 10*x*y^13 + 9*x*y^12 + 7*x*y^11 + 6*x*y^10 + 7*x*y^9 +
        3*x*y^8 + 4*x*y^7 + 7*x*y^5 + 3*x*y^4 + 5*x*y^3 + 5*x*y^2 + 5*x*y + 5*x 
        + 3*y^14 + y^13 + 7*y^12 + 5*y^11 + 7*y^10 + 2*y^9 + 6*y^8 + 10*y^7 + 
        2*y^6 + 5*y^3 + 10*y^2 + 9*y + 10,
    10*x^15 + 7*x^14*y + 8*x^14 + 6*x^13*y^2 + 5*x^13*y + 5*x^13 + 8*x^12*y^3 + 
        3*x^12*y^2 + 10*x^12*y + 2*x^12 + 9*x^11*y^4 + 8*x^11*y^3 + 3*x^11*y^2 +
        2*x^11*y + 4*x^11 + 6*x^10*y^5 + 5*x^10*y^4 + 5*x^10*y^3 + 7*x^10*y^2 + 
        8*x^10*y + x^10 + 4*x^9*y^6 + x^9*y^5 + 6*x^9*y^4 + 6*x^9*y^3 + 
        3*x^9*y^2 + 7*x^9*y + 2*x^9 + 5*x^8*y^7 + 7*x^8*y^6 + 5*x^8*y^4 + 
        8*x^8*y^3 + x^8*y^2 + 6*x^8*y + 6*x^8 + 7*x^7*y^8 + 7*x^7*y^7 + 
        9*x^7*y^5 + 9*x^7*y^4 + 3*x^7*y^3 + 8*x^7*y^2 + 4*x^7*y + 5*x^7 + 
        6*x^6*y^9 + 4*x^6*y^8 + 10*x^6*y^7 + 9*x^6*y^5 + 7*x^6*y^4 + 2*x^6*y^3 +
        2*x^6*y^2 + 8*x^6*y + x^6 + x^5*y^10 + 8*x^5*y^9 + 9*x^5*y^8 + 9*x^5*y^7
        + 10*x^5*y^6 + 10*x^5*y^5 + x^5*y^4 + 2*x^5*y^3 + 3*x^5*y^2 + x^5*y + 
        8*x^5 + 5*x^4*y^11 + 4*x^4*y^10 + 8*x^4*y^9 + 3*x^4*y^8 + 10*x^4*y^7 + 
        10*x^4*y^6 + 8*x^4*y^5 + 6*x^4*y^4 + 3*x^4*y^3 + 2*x^4*y^2 + 3*x^4*y + 
        9*x^4 + 4*x^3*y^12 + 9*x^3*y^11 + 9*x^3*y^10 + 6*x^3*y^9 + 2*x^3*y^8 + 
        x^3*y^7 + 10*x^3*y^6 + 9*x^3*y^5 + 4*x^3*y^3 + 3*x^3*y + 2*x^3 + 
        8*x^2*y^13 + x^2*y^12 + x^2*y^11 + 7*x^2*y^10 + 3*x^2*y^9 + 9*x^2*y^7 + 
        6*x^2*y^6 + x^2*y^5 + 4*x^2*y^4 + 3*x^2*y^3 + 4*x^2*y^2 + 10*x^2*y + x^2
        + x*y^14 + 3*x*y^13 + 4*x*y^12 + 3*x*y^11 + 9*x*y^10 + 7*x*y^9 + 3*x*y^8
        + 3*x*y^7 + 2*x*y^6 + 8*x*y^5 + 3*x*y^4 + 6*x*y^3 + 2*x*y^2 + 4*x*y + 
        6*x + 5*y^15 + 6*y^14 + 4*y^13 + 10*y^12 + 7*y^11 + y^10 + 5*y^9 + 4*y^8
        + 7*y^7 + 8*y^6 + 8*y^5 + 4*y^4 + 2*y^2 + 2*y + 10,
    6*x^16 + x^15*y + 7*x^15 + 10*x^14*y^2 + 2*x^14*y + 7*x^14 + 8*x^13*y^3 + 
        3*x^13*y + 9*x^13 + x^12*y^4 + x^12*y^3 + 2*x^12*y^2 + 5*x^12*y + 5*x^12
        + 4*x^11*y^5 + x^11*y^4 + 6*x^11*y^3 + 9*x^11*y^2 + 7*x^11*y + 5*x^11 + 
        9*x^10*y^6 + x^10*y^5 + 2*x^10*y^4 + 4*x^10*y^3 + 4*x^10*y + 2*x^10 + 
        8*x^9*y^6 + 7*x^9*y^5 + 10*x^9*y^4 + 5*x^9*y^3 + 8*x^9*y^2 + 7*x^9*y + 
        2*x^9 + 3*x^8*y^8 + 6*x^8*y^7 + 5*x^8*y^6 + 7*x^8*y^5 + 5*x^8*y^4 + 
        x^8*y^2 + 3*x^8*y + 8*x^8 + x^7*y^9 + x^7*y^8 + 10*x^7*y^7 + 3*x^7*y^6 +
        6*x^7*y^5 + 5*x^7*y^4 + 9*x^7*y^3 + 10*x^7*y^2 + 5*x^7*y + 4*x^7 + 
        x^6*y^10 + 6*x^6*y^9 + 10*x^6*y^8 + x^6*y^7 + 2*x^6*y^6 + 5*x^6*y^5 + 
        7*x^6*y^4 + x^6*y^3 + 8*x^6*y^2 + 9*x^6*y + 9*x^5*y^11 + x^5*y^10 + 
        8*x^5*y^9 + 6*x^5*y^7 + x^5*y^6 + 7*x^5*y^5 + 5*x^5*y^4 + 5*x^5*y^3 + 
        2*x^5*y^2 + 6*x^5*y + 7*x^5 + 3*x^4*y^12 + 9*x^4*y^11 + 10*x^4*y^10 + 
        10*x^4*y^9 + 10*x^4*y^8 + 6*x^4*y^7 + 5*x^4*y^6 + 5*x^4*y^5 + 6*x^4*y^4 
        + 4*x^4*y^3 + 2*x^4*y^2 + 5*x^4*y + 7*x^4 + 7*x^3*y^13 + 8*x^3*y^11 + 
        9*x^3*y^9 + 5*x^3*y^8 + 5*x^3*y^7 + 9*x^3*y^6 + 8*x^3*y^5 + 8*x^3*y^4 + 
        8*x^3*y^3 + 5*x^3*y^2 + 6*x^3*y + 3*x^3 + 3*x^2*y^14 + 6*x^2*y^13 + 
        9*x^2*y^12 + 6*x^2*y^11 + 2*x^2*y^10 + 9*x^2*y^9 + 5*x^2*y^8 + 
        10*x^2*y^7 + 2*x^2*y^6 + 8*x^2*y^5 + 6*x^2*y^3 + 4*x^2*y^2 + 9*x*y^15 + 
        5*x*y^14 + 2*x*y^13 + 4*x*y^12 + 10*x*y^11 + 9*x*y^10 + 3*x*y^8 + 
        7*x*y^7 + 10*x*y^6 + x*y^5 + 9*x*y^4 + 8*x*y^3 + 8*x*y^2 + 2*x*y + 4*x +
        y^16 + 6*y^15 + 9*y^13 + 10*y^12 + 3*y^11 + 7*y^10 + 7*y^9 + 10*y^8 + 
        8*y^7 + y^5 + 2*y^4 + 3*y^3 + 7*y^2 + y + 1,
    6*x^16 + 3*x^15*y + 9*x^15 + x^14*y^2 + 4*x^14*y + 3*x^14 + 3*x^13*y^3 + 
        7*x^13*y^2 + 10*x^13*y + 8*x^13 + 5*x^12*y^4 + 8*x^12*y^3 + 9*x^12*y^2 +
        10*x^12*y + 5*x^12 + x^11*y^5 + 8*x^11*y^2 + x^11*y + 8*x^11 + x^10*y^6 
        + 3*x^10*y^5 + 4*x^10*y^4 + 7*x^10*y^3 + 7*x^10*y^2 + 7*x^10*y + 2*x^10 
        + 7*x^9*y^7 + 8*x^9*y^6 + 4*x^9*y^4 + 5*x^9*y^2 + x^9*y + 8*x^8*y^8 + 
        4*x^8*y^7 + 5*x^8*y^6 + 2*x^8*y^5 + 10*x^8*y^4 + 3*x^8*y^3 + 10*x^8*y^2 
        + 5*x^8*y + 3*x^7*y^9 + 7*x^7*y^8 + 2*x^7*y^7 + 5*x^7*y^6 + 5*x^7*y^5 + 
        4*x^7*y^4 + 3*x^7*y^3 + 4*x^7*y^2 + 5*x^7*y + 3*x^7 + 6*x^6*y^10 + 
        x^6*y^8 + 6*x^6*y^7 + 7*x^6*y^6 + 9*x^6*y^5 + 9*x^6*y^4 + 7*x^6*y^3 + 
        6*x^6*y^2 + 10*x^6*y + 10*x^6 + x^5*y^11 + 5*x^5*y^10 + 2*x^5*y^9 + 
        8*x^5*y^8 + 4*x^5*y^7 + 2*x^5*y^5 + 3*x^5*y^4 + 8*x^5*y^3 + 9*x^5*y^2 + 
        10*x^5*y + x^5 + x^4*y^12 + 2*x^4*y^11 + 2*x^4*y^10 + x^4*y^9 + 
        6*x^4*y^8 + 7*x^4*y^7 + 9*x^4*y^6 + x^4*y^5 + 2*x^4*y^3 + 3*x^4*y^2 + 
        6*x^4*y + 9*x^4 + 8*x^3*y^13 + 9*x^3*y^12 + 2*x^3*y^11 + x^3*y^10 + 
        10*x^3*y^9 + 4*x^3*y^8 + 10*x^3*y^7 + 2*x^3*y^5 + 9*x^3*y^4 + 4*x^3*y^2 
        + 6*x^3*y + 10*x^3 + 5*x^2*y^14 + 4*x^2*y^13 + 4*x^2*y^11 + x^2*y^10 + 
        2*x^2*y^9 + 8*x^2*y^8 + 10*x^2*y^7 + x^2*y^6 + 4*x^2*y^5 + 3*x^2*y^4 + 
        5*x^2*y^3 + 5*x^2*y^2 + 6*x^2*y + 8*x^2 + 5*x*y^15 + 9*x*y^14 + 8*x*y^13
        + 8*x*y^12 + 5*x*y^11 + 4*x*y^10 + 9*x*y^9 + 2*x*y^8 + 7*x*y^7 + 3*x*y^6
        + 2*x*y^5 + 7*x*y^4 + 8*x*y + 7*x + 5*y^16 + 6*y^15 + 8*y^12 + 10*y^11 +
        9*y^10 + 5*y^8 + 9*y^7 + 10*y^6 + y^5 + y^4 + 9*y^3 + 6*y^2 + 4*y + 5,
    3*x^17 + 3*x^16*y + 6*x^16 + 7*x^15*y^2 + 6*x^15*y + 6*x^15 + 7*x^14*y^3 + 
        10*x^14*y^2 + 2*x^14*y + 10*x^14 + 5*x^13*y^4 + 5*x^13*y^3 + 7*x^13*y^2 
        + 4*x^13 + 5*x^12*y^5 + 3*x^12*y^4 + 2*x^12*y^3 + 2*x^12*y^2 + x^12*y + 
        5*x^12 + 4*x^11*y^6 + 10*x^11*y^5 + 8*x^11*y^4 + 8*x^11*y^3 + 2*x^11*y^2
        + 7*x^11*y + 9*x^11 + 7*x^10*y^7 + 7*x^10*y^6 + 2*x^10*y^5 + 5*x^10*y^4 
        + 4*x^10*y^3 + 8*x^10*y^2 + 7*x^10*y + 7*x^10 + 5*x^9*y^8 + 8*x^9*y^7 + 
        3*x^9*y^6 + 6*x^9*y^5 + 5*x^9*y^4 + 9*x^9*y^3 + 4*x^9*y^2 + 2*x^9*y + 
        9*x^9 + 4*x^8*y^9 + 8*x^8*y^8 + 10*x^8*y^7 + 6*x^8*y^5 + 7*x^8*y^4 + 
        3*x^8*y^3 + 3*x^8*y^2 + x^8*y + 10*x^8 + 5*x^7*y^10 + 9*x^7*y^8 + 
        8*x^7*y^7 + 4*x^7*y^6 + 3*x^7*y^4 + 9*x^7*y^3 + 2*x^7*y^2 + 9*x^7*y + 
        7*x^7 + 4*x^6*y^11 + 9*x^6*y^10 + 3*x^6*y^9 + 6*x^6*y^8 + x^6*y^7 + 
        8*x^6*y^6 + 10*x^6*y^5 + 3*x^6*y^4 + 6*x^6*y^3 + 6*x^6*y^2 + 9*x^6*y + 
        3*x^6 + 9*x^5*y^12 + 10*x^5*y^11 + 2*x^5*y^10 + 7*x^5*y^9 + 5*x^5*y^8 + 
        9*x^5*y^7 + 7*x^5*y^6 + 6*x^5*y^5 + 9*x^5*y^4 + 8*x^5*y^3 + 10*x^5*y^2 +
        5*x^5 + x^4*y^13 + 6*x^4*y^12 + 3*x^4*y^11 + x^4*y^10 + 2*x^4*y^9 + 
        8*x^4*y^8 + 6*x^4*y^7 + 10*x^4*y^6 + 7*x^4*y^5 + x^4*y^4 + 9*x^4*y^2 + 
        9*x^4*y + 5*x^4 + 4*x^3*y^14 + 10*x^3*y^13 + 10*x^3*y^12 + 9*x^3*y^11 + 
        9*x^3*y^10 + 10*x^3*y^9 + 2*x^3*y^7 + 4*x^3*y^6 + 9*x^3*y^5 + 8*x^3*y^4 
        + 9*x^3*y^3 + 8*x^3*y^2 + 4*x^3*y + 9*x^3 + 4*x^2*y^15 + 7*x^2*y^14 + 
        6*x^2*y^13 + 2*x^2*y^12 + 8*x^2*y^11 + 10*x^2*y^10 + 8*x^2*y^9 + 
        2*x^2*y^8 + 5*x^2*y^7 + 4*x^2*y^6 + x^2*y^5 + 6*x^2*y^3 + 4*x^2*y^2 + 
        6*x^2*y + 5*x^2 + 4*x*y^16 + 6*x*y^15 + 8*x*y^14 + x*y^13 + 5*x*y^12 + 
        3*x*y^11 + 10*x*y^10 + 8*x*y^9 + 9*x*y^8 + 7*x*y^7 + 9*x*y^6 + x*y^5 + 
        8*x*y^4 + 5*x*y^3 + 10*x*y^2 + 8*x*y + 9*x + 9*y^17 + 7*y^15 + 3*y^14 + 
        9*y^13 + 10*y^12 + 4*y^11 + 10*y^10 + 3*y^9 + y^8 + 3*y^7 + 4*y^6 + 
        8*y^5 + 3*y^4 + y^3 + 8*y^2 + 9*y + 10,
    x^18 + 10*x^17*y + 8*x^17 + 9*x^16*y^2 + x^16 + 2*x^15*y^3 + 2*x^15*y^2 + 
        8*x^15*y + 6*x^15 + 2*x^14*y^4 + 10*x^14*y^3 + 6*x^14*y^2 + 8*x^14*y + 
        9*x^14 + 4*x^13*y^5 + 10*x^13*y^4 + 4*x^13*y^3 + 8*x^13*y^2 + x^13*y + 
        8*x^13 + 3*x^12*y^6 + 5*x^12*y^5 + 8*x^12*y^4 + 10*x^12*y^3 + 5*x^12*y^2
        + 2*x^12*y + 4*x^12 + 6*x^11*y^7 + 3*x^11*y^6 + x^11*y^5 + 7*x^11*y^4 + 
        8*x^11*y^3 + 9*x^11*y^2 + 2*x^11*y + 5*x^11 + 8*x^10*y^6 + 7*x^10*y^5 + 
        8*x^10*y^4 + 9*x^10*y^2 + 10*x^10*y + 8*x^10 + 7*x^9*y^9 + 4*x^9*y^8 + 
        3*x^9*y^6 + 10*x^9*y^5 + 10*x^9*y^4 + 5*x^9*y^3 + 4*x^9*y^2 + 4*x^9*y + 
        2*x^9 + x^8*y^10 + x^8*y^9 + 7*x^8*y^8 + 3*x^8*y^7 + 2*x^8*y^6 + 
        9*x^8*y^4 + x^8*y^3 + 4*x^8*y^2 + x^8*y + 9*x^7*y^11 + 9*x^7*y^9 + 
        7*x^7*y^8 + 5*x^7*y^7 + 9*x^7*y^6 + 10*x^7*y^5 + 6*x^7*y^4 + 4*x^7*y^3 +
        2*x^7*y + 2*x^7 + 6*x^6*y^12 + 6*x^6*y^11 + 6*x^6*y^10 + 8*x^6*y^9 + 
        9*x^6*y^7 + x^6*y^6 + 8*x^6*y^5 + 6*x^6*y^4 + 2*x^6*y^3 + 7*x^6*y^2 + 
        6*x^6*y + 5*x^6 + 3*x^5*y^13 + 6*x^5*y^12 + 3*x^5*y^10 + 4*x^5*y^9 + 
        9*x^5*y^8 + 7*x^5*y^7 + 7*x^5*y^6 + 4*x^5*y^5 + x^5*y^4 + 4*x^5*y^3 + 
        8*x^5*y^2 + 9*x^5 + x^4*y^14 + x^4*y^13 + 10*x^4*y^12 + x^4*y^11 + 
        3*x^4*y^10 + 4*x^4*y^9 + 2*x^4*y^8 + 3*x^4*y^7 + 3*x^4*y^6 + 6*x^4*y^5 +
        6*x^4*y^4 + 7*x^4*y^3 + 10*x^4*y^2 + 6*x^4*y + 3*x^4 + 8*x^3*y^15 + 
        6*x^3*y^14 + 9*x^3*y^12 + 3*x^3*y^11 + 4*x^3*y^10 + x^3*y^9 + 4*x^3*y^7 
        + 2*x^3*y^6 + 9*x^3*y^5 + 6*x^3*y^4 + 3*x^3*y^3 + 10*x^3*y^2 + 7*x^3*y +
        x^3 + x^2*y^16 + 3*x^2*y^15 + 5*x^2*y^14 + 2*x^2*y^13 + 10*x^2*y^12 + 
        10*x^2*y^11 + 9*x^2*y^10 + 4*x^2*y^9 + 5*x^2*y^8 + 4*x^2*y^7 + 
        10*x^2*y^6 + 2*x^2*y^5 + 6*x^2*y^4 + 7*x^2*y^3 + 5*x^2*y^2 + 9*x^2*y + 
        10*x^2 + 6*x*y^17 + x*y^16 + 10*x*y^15 + x*y^14 + 10*x*y^13 + 8*x*y^12 +
        8*x*y^11 + 10*x*y^10 + 10*x*y^9 + 4*x*y^7 + 4*x*y^6 + 5*x*y^5 + 5*x*y^4 
        + 10*x*y^3 + 7*x*y^2 + 7*x*y + 7*x + 9*y^18 + 4*y^17 + 9*y^16 + 3*y^15 +
        10*y^14 + 3*y^13 + 6*y^12 + 6*y^11 + 3*y^10 + 7*y^9 + 3*y^8 + 9*y^7 + 
        8*y^6 + 3*y^5 + 5*y^4 + 3*y^3 + 10*y^2 + 3*y + 4,
    4*x^18 + 4*x^17*y + 2*x^17 + 4*x^16*y^2 + 10*x^16*y + 5*x^16 + 6*x^15*y^3 + 
        8*x^15*y^2 + 7*x^15*y + 4*x^15 + 2*x^14*y^4 + 8*x^14*y^3 + 3*x^14*y^2 + 
        8*x^14*y + 3*x^14 + 2*x^13*y^5 + 7*x^13*y^4 + 3*x^13*y^3 + 7*x^13*y^2 + 
        10*x^13*y + 9*x^12*y^6 + 8*x^12*y^5 + 3*x^12*y^4 + 5*x^12*y^3 + x^12*y^2
        + 7*x^12*y + x^12 + 2*x^11*y^7 + 3*x^11*y^6 + 5*x^11*y^5 + 6*x^11*y^3 + 
        4*x^11*y^2 + x^11*y + 7*x^11 + 5*x^10*y^8 + 9*x^10*y^7 + 7*x^10*y^6 + 
        6*x^10*y^5 + 9*x^10*y^4 + 4*x^10*y^3 + 6*x^10*y + 10*x^10 + 6*x^9*y^9 + 
        3*x^9*y^8 + 2*x^9*y^7 + 10*x^9*y^6 + 5*x^9*y^5 + 2*x^9*y^4 + 8*x^9*y^3 +
        5*x^9*y^2 + x^9*y + 2*x^9 + 8*x^8*y^10 + 4*x^8*y^9 + 9*x^8*y^8 + 
        10*x^8*y^5 + 4*x^8*y^4 + 5*x^8*y^3 + 9*x^8*y^2 + 10*x^8*y + 2*x^8 + 
        6*x^7*y^11 + 8*x^7*y^10 + x^7*y^9 + 2*x^7*y^8 + 9*x^7*y^7 + 2*x^7*y^6 + 
        5*x^7*y^5 + 3*x^7*y^4 + 10*x^7*y^3 + 6*x^7*y^2 + 6*x^7*y + 10*x^7 + 
        10*x^6*y^12 + x^6*y^11 + 5*x^6*y^10 + x^6*y^9 + 5*x^6*y^8 + 4*x^6*y^7 + 
        9*x^6*y^6 + 6*x^6*y^5 + 7*x^6*y^4 + 6*x^6*y^3 + x^6*y^2 + x^6*y + 6*x^6 
        + 4*x^5*y^13 + 6*x^5*y^12 + 7*x^5*y^11 + 6*x^5*y^10 + 4*x^5*y^9 + 
        10*x^5*y^8 + 2*x^5*y^6 + 10*x^5*y^5 + 3*x^5*y^4 + 9*x^5*y^3 + 5*x^5*y^2 
        + 2*x^5*y + 2*x^5 + 6*x^4*y^14 + 7*x^4*y^13 + 2*x^4*y^12 + 7*x^4*y^11 + 
        3*x^4*y^10 + 6*x^4*y^9 + 10*x^4*y^8 + 8*x^4*y^7 + 2*x^4*y^6 + 6*x^4*y^5 
        + 2*x^4*y^4 + 7*x^4*y^3 + 9*x^4*y^2 + 10*x^4*y + x^4 + 9*x^3*y^15 + 
        x^3*y^13 + 4*x^3*y^12 + x^3*y^11 + 5*x^3*y^10 + 5*x^3*y^9 + 3*x^3*y^8 + 
        3*x^3*y^7 + 4*x^3*y^6 + 10*x^3*y^5 + 7*x^3*y^4 + 4*x^3*y^3 + 7*x^3*y^2 +
        10*x^3*y + 4*x^3 + 2*x^2*y^16 + 7*x^2*y^14 + 4*x^2*y^13 + 4*x^2*y^12 + 
        x^2*y^11 + 7*x^2*y^10 + 10*x^2*y^9 + 7*x^2*y^8 + 8*x^2*y^7 + 5*x^2*y^6 +
        4*x^2*y^5 + 5*x^2*y^4 + 5*x^2*y^3 + 4*x^2*y^2 + 8*x^2*y + 8*x^2 + 
        8*x*y^17 + 8*x*y^16 + 5*x*y^15 + 9*x*y^14 + x*y^13 + 3*x*y^11 + 2*x*y^10
        + 6*x*y^9 + 6*x*y^8 + 7*x*y^7 + 10*x*y^6 + 9*x*y^5 + 4*x*y^4 + 8*x*y^3 +
        2*x*y + 7*x + y^18 + 9*y^17 + 7*y^16 + 9*y^15 + 6*y^14 + y^13 + 10*y^12 
        + 5*y^11 + 2*y^10 + 6*y^9 + 4*y^8 + 2*y^7 + 5*y^6 + 3*y^5 + 6*y^4 + 
        9*y^3 + 8*y^2 + 9*y + 9,
    5*x^19 + x^18*y + 2*x^18 + 2*x^17*y^2 + 7*x^17*y + 4*x^17 + 3*x^16*y^3 + 
        3*x^16*y^2 + 10*x^16 + 9*x^15*y^4 + 10*x^15*y^3 + 5*x^15*y^2 + 8*x^15*y 
        + x^15 + 8*x^14*y^5 + 10*x^14*y^4 + 6*x^14*y^3 + 7*x^14*y^2 + 5*x^14*y +
        9*x^14 + 5*x^13*y^6 + 7*x^13*y^5 + 9*x^13*y^2 + x^13*y + 2*x^12*y^7 + 
        2*x^12*y^6 + 9*x^12*y^5 + 7*x^12*y^4 + 8*x^12*y^3 + 9*x^12*y^2 + x^12*y 
        + 7*x^12 + 3*x^11*y^8 + 3*x^11*y^7 + 3*x^11*y^6 + 4*x^11*y^5 + 
        9*x^11*y^4 + 3*x^11*y^2 + 9*x^11*y + 8*x^11 + 3*x^10*y^9 + 9*x^10*y^8 + 
        10*x^10*y^6 + 2*x^10*y^5 + x^10*y^4 + 3*x^10*y^3 + 9*x^10*y^2 + 7*x^10*y
        + 5*x^10 + 2*x^9*y^10 + 2*x^9*y^9 + 5*x^9*y^8 + 2*x^9*y^7 + 7*x^9*y^6 + 
        10*x^9*y^5 + x^9*y^4 + x^9*y + 3*x^9 + 5*x^8*y^11 + 4*x^8*y^9 + 
        8*x^8*y^8 + 4*x^8*y^7 + 4*x^8*y^6 + 2*x^8*y^5 + 4*x^8*y^4 + 9*x^8*y^3 + 
        6*x^8*y^2 + 4*x^8*y + 8*x^8 + 6*x^7*y^12 + 10*x^7*y^11 + 3*x^7*y^10 + 
        5*x^7*y^9 + 10*x^7*y^7 + 5*x^7*y^6 + 2*x^7*y^5 + 5*x^7*y^4 + 5*x^7*y^3 +
        8*x^7*y^2 + 5*x^7 + 10*x^6*y^13 + 6*x^6*y^12 + 6*x^6*y^10 + 6*x^6*y^9 + 
        6*x^6*y^7 + 10*x^6*y^6 + 5*x^6*y^5 + 4*x^6*y^4 + 4*x^6*y^3 + x^6*y^2 + 
        9*x^6*y + 9*x^6 + 9*x^5*y^13 + 4*x^5*y^12 + 4*x^5*y^11 + 10*x^5*y^10 + 
        2*x^5*y^9 + 10*x^5*y^8 + x^5*y^7 + 7*x^5*y^5 + 2*x^5*y^4 + 8*x^5*y^2 + 
        x^5*y + x^5 + 6*x^4*y^15 + 6*x^4*y^12 + 8*x^4*y^11 + 5*x^4*y^10 + 
        3*x^4*y^8 + 10*x^4*y^7 + 5*x^4*y^6 + 6*x^4*y^5 + 5*x^4*y^4 + 5*x^4*y^3 +
        3*x^4*y + 8*x^4 + 3*x^3*y^16 + 5*x^3*y^15 + x^3*y^14 + 2*x^3*y^13 + 
        3*x^3*y^12 + 3*x^3*y^11 + 6*x^3*y^10 + 3*x^3*y^9 + 5*x^3*y^7 + 8*x^3*y^6
        + 7*x^3*y^5 + 2*x^3*y^4 + 9*x^3*y^3 + 7*x^3*y + x^2*y^17 + 3*x^2*y^16 + 
        6*x^2*y^15 + 5*x^2*y^13 + 4*x^2*y^12 + 2*x^2*y^11 + 8*x^2*y^10 + x^2*y^9
        + 6*x^2*y^8 + 2*x^2*y^7 + 10*x^2*y^6 + 3*x^2*y^5 + 5*x^2*y^4 + x^2*y^3 +
        10*x^2*y^2 + 5*x^2 + 5*x*y^18 + 6*x*y^17 + 2*x*y^16 + 9*x*y^15 + 
        2*x*y^13 + 5*x*y^12 + 3*x*y^10 + 6*x*y^9 + 7*x*y^8 + 7*x*y^7 + 7*x*y^6 +
        9*x*y^5 + 9*x*y^4 + 9*x*y^3 + 3*x*y^2 + 2*x*y + 6*x + 4*y^19 + 10*y^18 +
        4*y^17 + 9*y^16 + 2*y^15 + 7*y^14 + 9*y^13 + 3*y^12 + 8*y^11 + 4*y^10 + 
        7*y^7 + 9*y^6 + y^5 + 7*y^4 + 5*y^3 + 10*y^2 + 7*y + 9,
    6*x^20 + 6*x^19*y + 8*x^18*y^2 + 8*x^18*y + 10*x^18 + x^17*y^3 + 5*x^17*y^2 
        + 5*x^17 + 3*x^16*y^4 + 6*x^16*y^3 + 7*x^16*y^2 + 10*x^16*y + 4*x^16 + 
        10*x^15*y^5 + 8*x^15*y^4 + 5*x^15*y^3 + 5*x^15*y^2 + 8*x^15*y + 2*x^15 +
        8*x^14*y^6 + 5*x^14*y^5 + x^14*y^4 + 5*x^14*y^2 + 7*x^14*y + 5*x^14 + 
        4*x^13*y^7 + 2*x^13*y^6 + 10*x^13*y^5 + 4*x^13*y^4 + 10*x^13*y^3 + 
        8*x^13*y^2 + x^13*y + 3*x^13 + 6*x^12*y^8 + 7*x^12*y^7 + 4*x^12*y^6 + 
        6*x^12*y^5 + 6*x^12*y^4 + 8*x^12*y^3 + 6*x^12*y^2 + 5*x^12*y + 5*x^12 + 
        4*x^11*y^8 + 3*x^11*y^7 + x^11*y^6 + 5*x^11*y^5 + 10*x^11*y^4 + 
        7*x^11*y^3 + 9*x^11*y^2 + 3*x^11*y + 4*x^11 + 10*x^10*y^10 + 10*x^10*y^9
        + 7*x^10*y^8 + 4*x^10*y^7 + 2*x^10*y^6 + x^10*y^5 + 8*x^10*y^4 + 
        7*x^10*y^3 + 5*x^10*y^2 + 8*x^10*y + 10*x^10 + 3*x^9*y^11 + 6*x^9*y^10 +
        x^9*y^9 + 6*x^9*y^8 + 4*x^9*y^6 + 7*x^9*y^5 + 2*x^9*y^4 + 10*x^9*y^3 + 
        10*x^9*y^2 + 2*x^9*y + 9*x^9 + 2*x^8*y^12 + 7*x^8*y^11 + 10*x^8*y^10 + 
        8*x^8*y^9 + 4*x^8*y^8 + 4*x^8*y^7 + 5*x^8*y^6 + x^8*y^4 + 10*x^8*y^3 + 
        4*x^8*y^2 + 4*x^8*y + 2*x^8 + 8*x^7*y^13 + 6*x^7*y^12 + 5*x^7*y^11 + 
        5*x^7*y^10 + 6*x^7*y^9 + x^7*y^8 + 2*x^7*y^7 + 4*x^7*y^6 + 2*x^7*y^5 + 
        7*x^7*y^4 + 3*x^7*y^3 + 7*x^7*y^2 + 3*x^7*y + 4*x^7 + 4*x^6*y^14 + 
        4*x^6*y^13 + 3*x^6*y^12 + 3*x^6*y^11 + 7*x^6*y^10 + 9*x^6*y^9 + 
        8*x^6*y^8 + 6*x^6*y^7 + x^6*y^6 + 9*x^6*y^5 + 10*x^6*y^3 + x^6*y^2 + 
        9*x^6*y + 6*x^6 + 6*x^5*y^15 + 3*x^5*y^13 + 5*x^5*y^12 + 6*x^5*y^10 + 
        8*x^5*y^9 + 2*x^5*y^8 + 6*x^5*y^7 + 10*x^5*y^6 + 4*x^5*y^5 + 10*x^5*y^3 
        + 2*x^5*y^2 + 2*x^5*y + 9*x^5 + 3*x^4*y^16 + 7*x^4*y^15 + 5*x^4*y^14 + 
        4*x^4*y^13 + 2*x^4*y^11 + x^4*y^10 + 9*x^4*y^9 + 4*x^4*y^8 + 2*x^4*y^7 +
        9*x^4*y^6 + 8*x^4*y^5 + 2*x^4*y^4 + 7*x^4*y^3 + 4*x^4*y^2 + 3*x^4*y + 
        x^4 + 4*x^3*y^17 + 5*x^3*y^16 + 6*x^3*y^15 + x^3*y^14 + 4*x^3*y^13 + 
        6*x^3*y^12 + 3*x^3*y^11 + 3*x^3*y^10 + 2*x^3*y^9 + 2*x^3*y^8 + 
        10*x^3*y^7 + 8*x^3*y^6 + 3*x^3*y^5 + 8*x^3*y^4 + 10*x^3*y^3 + 5*x^3*y^2 
        + x^3*y + 6*x^3 + x^2*y^18 + 8*x^2*y^17 + 8*x^2*y^16 + 9*x^2*y^15 + 
        3*x^2*y^14 + 3*x^2*y^13 + x^2*y^12 + 3*x^2*y^11 + 10*x^2*y^10 + 
        6*x^2*y^9 + 5*x^2*y^8 + 8*x^2*y^7 + 2*x^2*y^6 + 6*x^2*y^5 + 4*x^2*y^4 + 
        3*x^2*y^3 + 2*x^2*y^2 + x^2*y + 10*x^2 + 4*x*y^19 + 4*x*y^18 + 8*x*y^17 
        + 6*x*y^15 + 10*x*y^14 + 3*x*y^13 + x*y^12 + 6*x*y^11 + 9*x*y^10 + 
        10*x*y^9 + 9*x*y^8 + 4*x*y^7 + 6*x*y^6 + x*y^5 + 9*x*y^3 + x*y^2 + 7*x*y
        + 2*x + 5*y^20 + 9*y^19 + 3*y^18 + 5*y^17 + 7*y^15 + 3*y^14 + 4*y^13 + 
        3*y^12 + 8*y^11 + 6*y^10 + 9*y^8 + 7*y^7 + 9*y^6 + 2*y^5 + 2*y^4 + y^3 +
        7*y^2 + 6*y + 6,
    8*x^20 + x^19*y + x^19 + 4*x^18*y + x^18 + 5*x^17*y^3 + 6*x^17*y^2 + 
        10*x^17*y + 7*x^17 + 3*x^16*y^4 + 3*x^16*y^3 + 7*x^16*y^2 + 4*x^16*y + 
        6*x^16 + 9*x^15*y^5 + 9*x^15*y^4 + 7*x^15*y^2 + 7*x^15*y + 3*x^15 + 
        4*x^14*y^6 + 8*x^14*y^5 + 4*x^14*y^4 + 6*x^14*y^3 + 7*x^14*y^2 + 
        3*x^14*y + 9*x^14 + 4*x^13*y^7 + 10*x^13*y^6 + 2*x^13*y^5 + 8*x^13*y^4 +
        5*x^13*y^3 + 2*x^13*y^2 + 8*x^13*y + 3*x^13 + 4*x^12*y^8 + 6*x^12*y^7 + 
        2*x^12*y^6 + 4*x^12*y^4 + 4*x^12*y^3 + 9*x^12*y^2 + x^12*y + 8*x^12 + 
        4*x^11*y^9 + 9*x^11*y^8 + 4*x^11*y^7 + 5*x^11*y^6 + 3*x^11*y^5 + 
        4*x^11*y^4 + 3*x^11*y^3 + 9*x^11*y^2 + 9*x^11*y + x^11 + 9*x^10*y^10 + 
        8*x^10*y^8 + 10*x^10*y^7 + 10*x^10*y^6 + x^10*y^5 + x^10*y^4 + 
        7*x^10*y^3 + 4*x^10*y^2 + 6*x^10*y + 6*x^10 + 3*x^9*y^11 + 4*x^9*y^10 + 
        3*x^9*y^9 + x^9*y^8 + 3*x^9*y^7 + 10*x^9*y^6 + x^9*y^5 + 10*x^9*y^4 + 
        2*x^9*y^3 + 4*x^9*y^2 + 7*x^9*y + 9*x^9 + 8*x^8*y^12 + 2*x^8*y^11 + 
        5*x^8*y^10 + 10*x^8*y^9 + 2*x^8*y^8 + 2*x^8*y^7 + 3*x^8*y^6 + 7*x^8*y^5 
        + 9*x^8*y^4 + 6*x^8*y^3 + 3*x^8*y^2 + 6*x^8*y + x^8 + 7*x^7*y^13 + 
        5*x^7*y^12 + 9*x^7*y^11 + 6*x^7*y^9 + 7*x^7*y^8 + x^7*y^7 + x^7*y^6 + 
        10*x^7*y^5 + 8*x^7*y^4 + 6*x^7*y^3 + 9*x^7*y^2 + 5*x^7 + 10*x^6*y^14 + 
        6*x^6*y^13 + 5*x^6*y^12 + 5*x^6*y^11 + 5*x^6*y^8 + 2*x^6*y^6 + 8*x^6*y^5
        + 5*x^6*y^4 + 5*x^6*y^3 + 3*x^6*y^2 + 9*x^6*y + 9*x^6 + 8*x^5*y^15 + 
        5*x^5*y^14 + 8*x^5*y^13 + 7*x^5*y^12 + 6*x^5*y^11 + 3*x^5*y^10 + 
        3*x^5*y^9 + 9*x^5*y^8 + 6*x^5*y^7 + 5*x^5*y^6 + 2*x^5*y^5 + 5*x^5*y^3 + 
        10*x^5*y^2 + 10*x^5*y + x^5 + 7*x^4*y^16 + 5*x^4*y^15 + 4*x^4*y^14 + 
        10*x^4*y^13 + 3*x^4*y^12 + 2*x^4*y^11 + 9*x^4*y^10 + 9*x^4*y^9 + 
        5*x^4*y^8 + 9*x^4*y^7 + 9*x^4*y^6 + 10*x^4*y^5 + 9*x^4*y^4 + 2*x^4*y^3 +
        4*x^4*y^2 + 5*x^4*y + 10*x^4 + 8*x^3*y^17 + 8*x^3*y^16 + 4*x^3*y^15 + 
        8*x^3*y^14 + 5*x^3*y^13 + 10*x^3*y^12 + 9*x^3*y^11 + 5*x^3*y^9 + 
        7*x^3*y^7 + 7*x^3*y^5 + 9*x^3*y^4 + 8*x^3*y^3 + 3*x^3*y^2 + 5*x^3*y + 
        7*x^3 + 7*x^2*y^18 + 2*x^2*y^17 + 5*x^2*y^16 + 5*x^2*y^15 + 3*x^2*y^14 +
        4*x^2*y^13 + 2*x^2*y^12 + x^2*y^11 + 7*x^2*y^10 + 6*x^2*y^9 + 8*x^2*y^8 
        + 10*x^2*y^7 + 3*x^2*y^6 + x^2*y^5 + 2*x^2*y^4 + 3*x^2*y^3 + 9*x^2*y^2 +
        2*x^2*y + 6*x*y^19 + 9*x*y^18 + x*y^17 + x*y^16 + 4*x*y^15 + 10*x*y^14 +
        10*x*y^13 + x*y^12 + 7*x*y^11 + 10*x*y^10 + 4*x*y^9 + 7*x*y^8 + x*y^7 + 
        5*x*y^6 + 6*x*y^3 + 10*x*y^2 + 4*x*y + 8*x + 2*y^20 + 7*y^19 + y^18 + 
        8*y^17 + 6*y^16 + 10*y^15 + 2*y^14 + 3*y^13 + y^12 + 5*y^11 + 8*y^10 + 
        7*y^9 + 4*y^8 + 6*y^7 + 7*y^6 + 9*y^5 + 4*y^3 + 3*y^2 + 10*y + 9,
    7*x^21 + 2*x^20*y + 5*x^20 + 7*x^19*y^2 + 3*x^19*y + 8*x^19 + 10*x^18*y^3 + 
        9*x^18*y^2 + 2*x^18*y + 2*x^18 + x^17*y^4 + 6*x^17*y^2 + x^17*y + 
        10*x^17 + x^16*y^5 + 4*x^16*y^4 + 7*x^16*y^3 + 7*x^16*y^2 + 5*x^16*y + 
        9*x^16 + 10*x^15*y^6 + 3*x^15*y^4 + 10*x^15*y^3 + 5*x^15*y^2 + 2*x^15*y 
        + 5*x^15 + 3*x^14*y^7 + 7*x^14*y^6 + 5*x^14*y^5 + 9*x^14*y^4 + 
        6*x^14*y^3 + 6*x^14*y^2 + x^14*y + x^14 + 5*x^13*y^7 + 3*x^13*y^6 + 
        5*x^13*y^5 + 10*x^13*y^4 + 8*x^13*y^3 + x^13*y^2 + 7*x^13*y + 7*x^13 + 
        7*x^12*y^9 + 8*x^12*y^8 + 10*x^12*y^7 + x^12*y^6 + 5*x^12*y^5 + x^12*y^4
        + x^12*y^3 + x^12*y^2 + x^12*y + 5*x^12 + 9*x^11*y^10 + 10*x^11*y^9 + 
        x^11*y^8 + 3*x^11*y^7 + 7*x^11*y^6 + 7*x^11*y^5 + 3*x^11*y^4 + 
        7*x^11*y^3 + 5*x^11*y^2 + 8*x^11*y + 8*x^11 + 9*x^10*y^11 + x^10*y^8 + 
        2*x^10*y^6 + 4*x^10*y^5 + 7*x^10*y^4 + 2*x^10*y^3 + x^10*y^2 + 6*x^10*y 
        + 6*x^10 + 6*x^9*y^12 + 7*x^9*y^11 + 8*x^9*y^10 + 2*x^9*y^8 + 6*x^9*y^7 
        + x^9*y^6 + 6*x^9*y^5 + 8*x^9*y^4 + 4*x^9*y^3 + 10*x^9*y^2 + 8*x^9*y + 
        4*x^9 + 5*x^8*y^13 + 2*x^8*y^12 + 3*x^8*y^11 + 2*x^8*y^10 + 10*x^8*y^9 +
        6*x^8*y^8 + x^8*y^7 + 9*x^8*y^6 + x^8*y^4 + 5*x^8*y^3 + 4*x^8*y^2 + 
        9*x^8*y + 10*x^8 + 7*x^7*y^14 + 4*x^7*y^13 + 8*x^7*y^11 + x^7*y^10 + 
        7*x^7*y^9 + 8*x^7*y^8 + 4*x^7*y^7 + x^7*y^6 + 9*x^7*y^5 + 3*x^7*y^4 + 
        9*x^7*y^2 + 9*x^7*y + 9*x^7 + 5*x^6*y^14 + 2*x^6*y^13 + 8*x^6*y^12 + 
        3*x^6*y^11 + 8*x^6*y^10 + 7*x^6*y^9 + 8*x^6*y^8 + 6*x^6*y^7 + 6*x^6*y^6 
        + 8*x^6*y^5 + 9*x^6*y^4 + 3*x^6*y^3 + x^6*y^2 + 4*x^6*y + 10*x^6 + 
        6*x^5*y^16 + 7*x^5*y^15 + 10*x^5*y^14 + 10*x^5*y^13 + 5*x^5*y^12 + 
        7*x^5*y^11 + 9*x^5*y^10 + x^5*y^9 + x^5*y^8 + 3*x^5*y^7 + 6*x^5*y^6 + 
        5*x^5*y^4 + 8*x^5*y^3 + 2*x^5*y^2 + 10*x^5 + 5*x^4*y^17 + x^4*y^16 + 
        3*x^4*y^15 + 10*x^4*y^14 + 6*x^4*y^13 + 2*x^4*y^12 + 3*x^4*y^11 + 
        6*x^4*y^10 + x^4*y^9 + 10*x^4*y^8 + 7*x^4*y^7 + 9*x^4*y^6 + x^4*y^5 + 
        4*x^4*y^4 + 5*x^4*y^3 + 7*x^4*y^2 + 2*x^4*y + 5*x^4 + 9*x^3*y^18 + 
        9*x^3*y^17 + 4*x^3*y^16 + 6*x^3*y^15 + 3*x^3*y^14 + 7*x^3*y^13 + 
        10*x^3*y^12 + 8*x^3*y^10 + 10*x^3*y^9 + 6*x^3*y^8 + x^3*y^7 + 10*x^3*y^5
        + 10*x^3*y^4 + 8*x^3*y^3 + 6*x^3*y^2 + 7*x^3*y + 3*x^3 + 5*x^2*y^19 + 
        6*x^2*y^18 + 6*x^2*y^17 + 4*x^2*y^16 + x^2*y^15 + 5*x^2*y^14 + 
        5*x^2*y^13 + 8*x^2*y^12 + 2*x^2*y^11 + 2*x^2*y^10 + 9*x^2*y^9 + 
        5*x^2*y^8 + 10*x^2*y^7 + 2*x^2*y^6 + 8*x^2*y^5 + x^2*y^4 + 2*x^2*y^3 + 
        8*x^2*y^2 + x^2 + 10*x*y^20 + x*y^19 + 2*x*y^18 + 10*x*y^17 + 4*x*y^16 +
        7*x*y^15 + 5*x*y^14 + x*y^13 + 4*x*y^12 + 9*x*y^11 + 5*x*y^10 + 6*x*y^9 
        + 8*x*y^8 + 6*x*y^7 + 8*x*y^6 + 8*x*y^5 + 6*x*y^4 + 9*x*y^3 + 2*x*y^2 + 
        9*x*y + 5*x + 2*y^21 + 2*y^20 + y^19 + 5*y^18 + 7*y^17 + y^16 + 5*y^15 +
        4*y^14 + y^13 + y^12 + y^11 + 3*y^10 + 7*y^9 + 10*y^8 + 2*y^7 + 5*y^6 + 
        3*y^5 + 7*y^4 + 9*y^2 + 2*y + 6
*];

C := Curve(A, curve_polynomials[g+1]);
Genus(C);
"Version 2";
b := ComputeZetaFunctionNumerator(C : Version := 2);