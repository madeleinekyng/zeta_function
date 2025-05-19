function ConvexHullMonomials(F)
  monomials := Monomials(F);
  points := [];
  for mon in monomials do
    i := Degree(mon, Parent(F).1);
    j := Degree(mon, Parent(F).2);
    Append(~points, [i,j]);
  end for;
  N := Polytope(points);
  return N;
end function;

//given a,b in F_{p^r}, and F_{p^r}
//compute the number field to lift to, and choose a lift of a,b to this number field
function lift_point(point, field_of_defn)
  a := point[1]; b := point[2];
  extension_poly := DefiningPolynomial(field_of_defn);
  lift_extension_poly := ChangeRing(extension_poly, Integers());
  r := Degree(field_of_defn);
  if r gt 1 then 
    L<t> := NumberField(lift_extension_poly);
    lift := func<x,t,r|&+[(Integers()!coeffs[i])*t^(i-1) : i in [1..r]] where coeffs:=Eltseq(x)>;
    lift_a := lift(field_of_defn!a,t,r);
    lift_b := lift(field_of_defn!b,t,r);
  else 
    L := RationalField();
    lift_a := Integers()!a;
    lift_b := Integers()!b;
  end if;
  return [lift_a, lift_b], L;
end function;

//sections is a sequence of polynomials over the integers 
//defining a vector space V = span_Q(p : p in sections)
//we find a subspace for the polynomials p over the integers such that
//the curve defined by p=0 has a singularity at (a,b,c) of mult. m
function ImposeFirstPatchSingularityOfMultiplicity(point, multiplicity, L, sections)
  if #sections eq 0 then 
    return sections;
  end if;

  //this homomorphism just casts integer elements of L as magma integers
  a := point[1]; b := point[2];
  r := Degree(L);
  H := hom< RationalField() -> Integers() | >;

  poly_ring_L<x,y> := PolynomialRing(L, 2);
  change_section_ring_hom := hom < Universe(sections) -> poly_ring_L | [x,y]>;

  sections_copy := change_section_ring_hom(sections);

  M := ZeroMatrix(Integers(), r*Binomial(multiplicity+1, 2), #sections);
  for col_index := 1 to #sections do 
    s := sections_copy[col_index];
    ctr := 1;
    for i := 0 to (multiplicity-1) do 
      //differentiate wrt x i times
      s_derivative_x := Derivative(s, i, 1);
      for j := 0 to (multiplicity-1)-i do 
        //differentiate wrt y j times
        s_derivative_y := Derivative(s_derivative_x, j, 2);
        //ensure derivative of polynomial passes through point
        s_derivative_evaluated := Eltseq(Evaluate(s_derivative_y, [a,b]));
        conditions := H(Eltseq(s_derivative_evaluated));
        for l := 1 to r do 
          M[ctr, col_index] := conditions[l];
          ctr +:= 1;
        end for;
      end for;
    end for;
  end for;
  // print M;
  BN:=Basis(NullspaceOfTranspose(M));
  // print BN;
  seq:=[Normalize(&+[BN[i][j]*sections[j]:j in [1..#sections]]):i in [1..#BN]];
  return seq;
end function;

//impose singularity in patch u=1/x, v=y/x with u = 0
function ImposeSecondPatchSingularityOfMultiplicity(point, multiplicity, L, sections, n, E)
  if #sections eq 0 then 
    return sections;
  end if;

  a := point[1]; b := point[2];
  r := Degree(L);
  H := hom< RationalField() -> Integers() | >;

  poly_ring_L<x,y> := PolynomialRing(L, 2);
  change_section_ring_hom := hom < Universe(sections) -> poly_ring_L | [x,y]>;

  sections_copy := change_section_ring_hom(sections);
  

  M := ZeroMatrix(Integers(), r*Binomial(multiplicity+1, 2), #sections);
  for col_index := 1 to #sections do 
    s := sections_copy[col_index];
    //transform s to patch u=1/x, v=y/x^E
    coeffs, monos := CoefficientsAndMonomials(s);
    monos := [x^(E*(n-Degree(exp, 2))-Degree(exp, 1)) * y^(Degree(exp,2)) :  exp in monos];
    s := &+[coeffs[i]*monos[i] : i in [1..#coeffs]];
    ctr := 1;
    for i := 0 to (multiplicity-1) do 
      //differentiate wrt x i times
      s_derivative_x := Derivative(s, i, 1);
      for j := 0 to (multiplicity-1)-i do 
        //differentiate wrt y j times
        s_derivative_y := Derivative(s_derivative_x, j, 2);
        //ensure derivative of polynomial passes through point
        s_derivative_evaluated := Eltseq(Evaluate(s_derivative_y, [a,b]));
        conditions := H(Eltseq(s_derivative_evaluated));
        for l := 1 to r do 
          M[ctr, col_index] := conditions[l];
          ctr +:= 1;
        end for;
      end for;
    end for;
  end for;
  // print M;
  BN:=Basis(NullspaceOfTranspose(M));
  // print BN;
  seq:=[Normalize(&+[BN[i][j]*sections[j]:j in [1..#sections]]):i in [1..#BN]];
  return seq;
end function;


//assume input is affine plane curve over F_p
function LiftSingularCurve(C)
  g := Genus(C);
  d := Degree(C);

  A := Ambient(C);
  F := DefiningPolynomial(C);
  p := Characteristic(BaseField(C));
  x := Name(Parent(F),1); y := Name(Parent(F),2);
  //make monic
  n := Degree(F, 2); a_n := Coefficient(F, 2, n);
  F :=  y^n + &+[Coefficient(F, 2, i) * a_n^(n-1-i)*y^i : i in [0..(n-1)] ];
  
  //compute first order partial derivatives
  F_1 := Derivative(F,1);
  F_2 := Derivative(F,2);

  //find polynomial whose irred. factors corresp. to x-coordinates
  //of singular points
  r_1 := UnivariatePolynomial(Resultant(F, F_1, 2));
  r_2 := UnivariatePolynomial(Resultant(F_1, F_2, 2));
  r := GCD(r_1, r_2);

  patch_1_singular_points := [**];
  patch_2_singular_points := [**];
  patch_3_singular_points := [**];

  if r ne 1 then 
    //there are singular points on F = 0
    x_factors := Factorisation(r);
    for factor_1 in x_factors do 
      factor_x := factor_1[1];
      factor_x_degree := Degree(factor_x);
      K<a> := GF(p^factor_x_degree);
      Ku<u> := PolynomialRing(K);
      _, xroot := HasRoot(factor_x, K);
      y_factors := Factorisation(Evaluate(F, [xroot, u]));
      for factor_2 in y_factors do
        factor_y := factor_2[1];
        factor_y_degree := Degree(factor_y);
        L<b> := GF(p^(factor_x_degree*factor_y_degree));
        _, yroot := HasRoot(factor_y, L);
        F_x_value := Evaluate(F_1, [xroot, yroot]);
        F_y_value := Evaluate(F_2, [xroot, yroot]);
        F_value := Evaluate(F, [xroot, yroot]);
        //check that the point is singular
        if F_x_value eq 0 and F_y_value eq 0 and F_value eq 0 then
          L_u_v<u,v> := PolynomialRing(L, 2);
          F_eval := Evaluate(F, [u+xroot, v+yroot]);
          // print F_eval;
          // print Monomials(F_eval);
          m := 2;
          //find the multiplicity of the singular point
          while HomogeneousComponent(F_eval, m) eq 0 do 
            m +:= 1;
          end while;
          sing_pt_data := [* [xroot, yroot], L, m *];
          Append(~patch_1_singular_points, sing_pt_data);
        end if;
      end for;
    end for;
  end if;
  

  //move to patch u=1/x, v=y/x^E with u = 0
  coeffs, monos := CoefficientsAndMonomials(F);
  E := Maximum([Ceiling(Degree( Coefficient(F, 2, n-i))/i)  : i in [1..n] ]);
  new_monos := [x^(E*(n-Degree(exp, 2))-Degree(exp, 1)) * y^(Degree(exp,2)) :  exp in monos];
  G := &+[coeffs[i]*new_monos[i] : i in [1..#coeffs]];
  y_factors := Factorisation(UnivariatePolynomial(Evaluate(G, [0, y])));
  for factor_1 in y_factors do
    factor_y := factor_1[1];
    factor_y_degree := Degree(factor_y);
    K<a> := GF(p^factor_y_degree);
    _, yroot := HasRoot(factor_y, K);
    F_x_value := Evaluate(Derivative(G,1), [0, yroot]);
    F_y_value := Evaluate(Derivative(G,2), [0, yroot]);
    if F_x_value eq 0 and F_y_value eq 0 then
      L_u_v<u,v> := PolynomialRing(K, 2);
      G_eval := Evaluate(G, [u, v+yroot]);
      m := 2;
      //find the multiplicity of the singular point
      while HomogeneousComponent(G_eval, m) eq 0 do 
        m +:= 1;
      end while;
      sing_pt_data := [* [0,yroot], K, m *];
      Append(~patch_2_singular_points, sing_pt_data);
    end if;
  end for;

  delta_adjustment_1 := 0;
  delta_adjustment_2 := 0;
  if #patch_1_singular_points gt 0 then 
    delta_adjustment_1 := &+[Degree(sing_pt_data[2])*Binomial(sing_pt_data[3], 2) : sing_pt_data in patch_1_singular_points];
  end if;
  if #patch_2_singular_points gt 0 then
    delta_adjustment_2 := &+[Degree(sing_pt_data[2])*Binomial(sing_pt_data[3], 2) : sing_pt_data in patch_2_singular_points];
  end if;

  if g ne (E*n-2)*(n-1)/2 - (delta_adjustment_1 + delta_adjustment_2) then 
    print "Curve has non-ordinary singularities!";
    return -1;
  end if;


  R<x,y> := PolynomialRing(Integers(), 2);
  original_sections := [x^i*y^j : i in [0..((n-j)*E)], j in [0..n] ];
  sections := original_sections;
  for sing_pt_data in patch_1_singular_points do 
    lifted_point, L := lift_point(sing_pt_data[1], sing_pt_data[2]);
    sections := ImposeFirstPatchSingularityOfMultiplicity(lifted_point, sing_pt_data[3], L, sections);
  end for;
  for sing_pt_data in patch_2_singular_points do 
    lifted_point, L := lift_point(sing_pt_data[1], sing_pt_data[2]);
    sections := ImposeSecondPatchSingularityOfMultiplicity(lifted_point, sing_pt_data[3], L, sections, n, E);
  end for;


  if #sections eq 0 then 
    print "Not possible to lift!";
    print "No bivariate polynomials over the integers/rationals meet the singular conditons!";
    return -1;
  end if;

  //compute smith normal form
  //first, set up matrix whose col vectors correspond to the sections
  A := ZeroMatrix(Integers(), #original_sections, #sections);
  for j := 1 to #sections do 
    s := sections[j];
    for i := 1 to #original_sections do 
      A[i,j] := MonomialCoefficient(s, original_sections[i]);
    end for;
  end for;
  //now, compute smith normal form
  S, P, Q := SmithForm(A);

  //the columns of A span a subspace W of Q^D, where D = Binomial(d+2,2) = #original_sections
  //we want a basis of Z^D,
  //where the first dim_Q(W) vectors in the basis give a basis for W \cap Z^D
  //the columns of the following matrix give us such a basis!
  new_polynomial_basis_matrix := P^(-1);
  
  


  F_naive_lift := R!ChangeRing(F, Integers());
  F_naive_lift_vector := ZeroMatrix(Integers(), #original_sections, 1);
  for i := 1 to #original_sections do 
    F_naive_lift_vector[i,1] := MonomialCoefficient(F_naive_lift, original_sections[i]);
  end for;
  //write F in new basis
  F_naive_lift_vector_in_new_basis := P*F_naive_lift_vector;
  //check that the coefficients from #sections+1 to #original_sections 
  //are divisible by p
  error_div_by_p := true;
  for i := #sections+1 to #original_sections do 
    if F_naive_lift_vector_in_new_basis[i, 1] mod p ne 0 then 
      error_div_by_p := false;
      print "Not possible to lift!";
      return -1;
    end if;
  end for;


  F_lift_vector_in_new_basis := VerticalJoin(RowSubmatrix(F_naive_lift_vector_in_new_basis, 1, #sections), ZeroMatrix(Integers(), #original_sections-#sections, 1));
  F_lift_vector := new_polynomial_basis_matrix*F_lift_vector_in_new_basis;

  assert ChangeRing(F_naive_lift_vector, GF(p)) eq ChangeRing(F_lift_vector, GF(p)); 


  F_lift := &+[F_lift_vector[i,1] * original_sections[i] : i in [1..#original_sections]];

  


  return F_lift;

end function;
