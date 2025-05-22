load "compute_corrections.m";
load "count_plane_model.m";

//Given a polynomial that is reputed to be the LPolynomial of a curve over F_q, 
//return the number of F_{q^d}-rational points on the curve as predicted by the polynomial
function PointCountsFromLPolynomial(lpolynomial, q, d_range)
  coeff_sequence := Coefficients(lpolynomial) cat [0 : _ in [1..Maximum(d_range) - Degree(lpolynomial)]];
  hasse_weil_error_sequence := [coeff_sequence[2]];
  for i := 2 to Maximum(d_range) do 
    hasse_weil_error_sequence[i] := i*coeff_sequence[i+1];
    hasse_weil_error_sequence[i] -:= &+[hasse_weil_error_sequence[j] * coeff_sequence[i-j+1] : j in [1..(i-1)]];
  end for;
  return [hasse_weil_error_sequence[d] + q^d + 1 : d in d_range];
end function;

//Compute corrections for extensions of degree d for d in d_range
function ComputeGenusAndCorrectionsForChecking(C, d_range)
  assert IsPlaneCurve(C);
  assert IsAffine(C);
  //compute corrections code
  F, var_index := ComputeSeparableModel(C);
  n := Degree(F, var_index);
  
  if n le 1 then 
    //in this case, the curve is birational to P^1
    //i.e., it has genus 0
    return 0, [], 0;
  end if;

  //compute F_0 and F_infty that define C,
  //where F_0 is integral over F_q[x],
  //and F_infty is integral over F_q[1/x]
 
  a_n := UnivariatePolynomial(Coefficient(F, var_index, n));
  a_0 := UnivariatePolynomial(Coefficient(F, var_index, 0));
  
  k := Parent(a_n); 
  kx<y> := PolynomialRing(k);

  F_0 := y^n + kx![UnivariatePolynomial(Coefficient(F, var_index, i)) * a_n^(n-1-i) : i in [0..(n-1)] ];
  L_0 := FunctionField(F_0);
  L_0`MonicModel := F_0;

  E := Maximum([Ceiling(Degree( Coefficient(F_0, n-i))/i)  : i in [1..n] ]);
  L_0`Cf := E;
  F_infty := y^n + kx![k.1^(E*(n-i)- Degree(Coefficient(F_0, i))) * ReciprocalPolynomial(Coefficient(F_0, i)) : i in [0..(n-1)]  ];
  L_infty := FunctionField(F_infty);
  L_infty`MonicModel := F_infty;

  R := Discriminant(F_0);
  //discard simple root factors from R,
  //unless they are factors of a_0 or a_n
  R := GCD(R, Derivative(R)) * a_0 * a_n;
  //remove factors of x
  R := R div k.1^Valuation(R);  
  R_factorisation := Factorization(R);

  //find the bad x-coordinate polynomials,
  //i.e., find the x-coordinates where the fiber of
  //the x-coordinate map has less than n geometric points
  Y := [factor_pair[1] : factor_pair in R_factorisation];

  
  g := 1 - n + E * Binomial(n,2);
  degrees_1 := {**};
  degrees_2 := {**};
  for r_tuple in R_factorisation do 
    r := r_tuple[1];
    //run Montes to compute factorisation and index data
    Montes(L_0, r);
    g -:= L_0`LocalIndex[r]*Degree(r);
    //concatenate degrees_2 by residual degrees of valuations on L
    //extending the r-adic valuation
    degrees_2 := degrees_2 join {*Degree(q):q in L_0`PrimeIdeals[r]*};

    //factorise F mod r
    r_extension := ext<BaseField(C) | Degree(r)>;
    _, a := HasRoot(r, r_extension);
    eval_at := var_index eq 2 select [a, ChangeRing(k.1, r_extension)] else [ChangeRing(k.1, r_extension), a];
    F_mod_r := Evaluate(F, eval_at);
    F_mod_r_factors := Factorisation(F_mod_r);
    for s_tuple in F_mod_r_factors do 
      s := s_tuple[1];
      if Evaluate(s, 0) eq 0 then 
        continue;
      end if;
      //concatenate degrees_1 by degree of a closed point 
      //above r
      Include(~degrees_1, Degree(s)*Degree(r));
    end for;
  end for;
  Montes(L_0, k.1);
  g -:= L_0`LocalIndex[k.1];
  degrees_2 := degrees_2 join {*Degree(q):q in L_0`PrimeIdeals[k.1]*};
  Montes(L_infty, k.1);
  g -:= L_infty`LocalIndex[k.1];
  degrees_2 := degrees_2 join {*Degree(q):q in L_infty`PrimeIdeals[k.1]*};

  corrections := [0 : _ in d_range];
  for j := 1 to #d_range do
    d := d_range[j];
    divisors_of_d := Divisors(d);
    for r in divisors_of_d do 
      corrections[j] +:= r*(Multiplicity(degrees_2, r) - Multiplicity(degrees_1, r));
    end for;
  end for;

  return g, corrections, F;

end function;


//Given an affine plane curve C over a finite field F_q, a positive integer d, 
//and a positive integer lambda, use the trace formula and montes algorithm 
//to count F_{q^d}-rational points on the nonsingular projective curve birational to C
//to p-adic precision lambda
function CountPointsRangeViaTraceFormula(C, d_range, lambda : Version := 0)
  assert IsPlaneCurve(C);
  assert IsAffine(C);

  //compute correction 
  g, corrections, F := ComputeGenusAndCorrectionsForChecking(C, d_range);
  p := Characteristic(BaseRing(C));

  if Version eq 0 then 
    Version := 1;
  end if;

  precision_for_recovery := Floor(Maximum(d_range)/2 + Log(p, 4*g)) + 1;

  if lambda gt precision_for_recovery then 
    lambda := precision_for_recovery;
  end if;

  
  K := NewtonPolygon(F);

  //extra matrices required for small primes
  tau := Ceiling(lambda/((p-1)*Minimum(d_range)));
  S := lambda + tau - 1;

  if Version eq 1 then 
    F_lift := ChangeRing(F, Integers());
    F_lift := ChangeRing(F_lift, Integers(p^lambda));
    //convert to polynomial in ((Z/p^lambda Z)[x])[y]
    //seems faster to compute power and extract coeffs this way
    Rxy := Parent(F_lift);
    Rx1<x_1> := PolynomialRing(Integers(p^lambda));
    Rx2<x_2> := PolynomialRing(Rx1);
    x_coord_map := hom< Rxy-> Rx1 | [x_1, 1]>;
    F_lift := Rx2!(x_coord_map(Coefficients(F_lift, 2)));
    ComputeMatrix := func<s | ComputeMatrixNaive(F_lift, K, p, s, lambda)>;
  elif Version eq 2 then 
    F_lift := ChangeRing(F, Integers());
    F_lift := ChangeRing(F_lift, Integers(p^(lambda+2*S)));
    T := ComputeBoundingTriangle(K, p);
    ComputeMatrix := func<s | ComputeMatrixByDeformationRecurrence(F_lift, K, T, p, s, lambda)>;
  end if;




  trace_formula_weights := [(-1)^(s+tau-1) * Binomial(S, s) * Binomial(s-1, tau-1) : s in [0..S] ];
  trace_formula_weights := ChangeUniverse(trace_formula_weights, Integers(p^lambda));

  //compute matrices and their traces of powers
  matrix_traces := [[1] : _ in d_range];
  for s := 1 to S do 
    for j :=1 to #d_range do
      d := d_range[j];
      //if we actually need this trace, compute it
      if trace_formula_weights[s+1] ne 0 then 
        M_s := ComputeMatrix(s);
        matrix_traces[j, s+1] := Trace(M_s^d);
      end if;
    end for;
  end for;

  counts := [corrections[j] + (p^d_range[j]-1)^2*&+[trace_formula_weights[s]*matrix_traces[j,s] : s in [1..S+1]] : j in [1..#d_range]];
  return ChangeUniverse(counts, Integers());
end function;

//check that the computed LPolynomial predicts the ouputs
//from our code for evaluating the trace formula to p-adic precision
//lambda for extension degrees [2g+1, ..., 4g]
function CheckConsistency(C, lpoly, lambda, range)
  assert IsPlaneCurve(C);
  assert IsAffine(C);
  p := Characteristic(BaseRing(C));
  pt_cts_1 := PointCountsFromLPolynomial(lpoly, p, range);
  pt_cts_1 := [ct mod p^lambda : ct in pt_cts_1];
  pt_cts_2 := CountPointsRangeViaTraceFormula(C, range, lambda);
  // print pt_cts_1, pt_cts_2;
  return pt_cts_1 eq pt_cts_2;
end function;

//check that L(1) = order of the jacobian group
function CheckJacobian(C, lpoly)
  predicted_jacobian_order := Evaluate(lpoly, 1);
  p := Characteristic(BaseRing(C));
  //now we construct a divisor D = P_1 - P_0,
  //where P_1, P_0 are distinct places of equal degree
  pt_cts := PointCountsFromLPolynomial(lpoly, p, [1..Degree(lpoly)]);
  lowest_has_two_pts_deg := 1;
  while pt_cts[lowest_has_two_pts_deg] le 1 do
    lowest_has_two_pts_deg +:= 1;
  end while;

  K := AlgorithmicFunctionField(FunctionField(C));

  place_1 := RandomPlace(K, lowest_has_two_pts_deg);
  place_2 := RandomPlace(K, lowest_has_two_pts_deg);
  while place_2 eq place_1 do
    place_2 := RandomPlace(K, lowest_has_two_pts_deg);
  end while;

  D := Divisor(place_1)-Divisor(place_2);

  //check that predicted_jacobian_order*D is [0] in the Jacobian group
  isZero := IsPrincipal(predicted_jacobian_order*D);

  return isZero;
end function;