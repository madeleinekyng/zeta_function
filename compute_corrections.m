function ComputeSeparableModel(C)
  F := DefiningPolynomial(C);
  x := Parent(F).1; y := Parent(F).2;
  p := Characteristic(BaseRing(C));
  if Derivative(F, 2) eq 0 then 
    //F is not separable over F_q[x]
    n := Degree(F, 2);
    e := Valuation(n, p);
    for i := p to n by p do 
      if Coefficient(F, 2, i) ne 0 then 
        e := Minimum(Valuation(i, p), e);
      end if;
    end for;
    purely_inseparable_degree := p^e;
    separable_degree := n div purely_inseparable_degree;
    for i := 0 to separable_degree do 
      F +:= Coefficient(F, 2, purely_inseparable_degree*i)*(y^i - y^(purely_inseparable_degree*i));
    end for;
  elif Derivative(F, 1) eq 0 then 
    //F is not separable over F_q[y]
    m := Degree(F, 1);
    e := Valuation(m, p);
    for i := p to m by p do 
      if Coefficient(F, 1, i) ne 0 then 
        e := Minimum(Valuation(i, p), e);
      end if;
    end for;
    purely_inseparable_degree := p^e;
    separable_degree := m div purely_inseparable_degree;
    for i := 0 to separable_degree do 
      F +:= Coefficient(F, 1, purely_inseparable_degree*i)*(x^i - x^(purely_inseparable_degree*i));
    end for;
  end if;
  //return F that is separable over both F_q[x] and F_q[y]
  //and return index of variable that gives a lower degree map to P^1
  smaller_degree_variable := Degree(F, 2) le Degree(F,1) select 2 else 1;
  return F, smaller_degree_variable;
end function;


//assume input curve is geometrically irreducible affine curve
function ComputeGenusAndCorrections(C)
  //compute polynomial F(x,y) defining function field L/F_q
  //s.t. L/F_q(x) and L/F_q(y) are separable, and
  //s.t. F_q(C)/L is purely inseparable

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
  

  L_0`Genus:=g;

  corrections := [0 : _ in [1..g]];
  for d := 1 to g do 
    //we should have counted Multiplicity(degrees_2, d) - Multiplicity(degrees_1, d)
    //many more closed points of degree d
    error_in_degree_d_count := Multiplicity(degrees_2, d) - Multiplicity(degrees_1, d);
    for i := d to g by d do 
      corrections[i] +:= d*error_in_degree_d_count;
    end for;
  end for;

  return g, corrections, F;
end function;
  

