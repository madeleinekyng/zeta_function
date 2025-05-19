load "singular_point_lifting.m";
load "castryck_lifting_code.m";


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

function change_poly_for_rational_function_field(poly)
  poly := ChangeRing(poly, RationalField());
  old_y := Parent(poly).2;
  y_degree := Degree(poly, old_y);
  R1<x> := PolynomialRing(RationalField());
  R<y> := PolynomialRing(R1);
  proj1 := hom< Parent(poly) -> R1 | [x, 1]>;
  res_poly := 0;
  // print Parent(poly);
  for j := 0 to y_degree do
    res_poly +:= y^j*proj1(Coefficient(poly, old_y, j));
  end for;
  return res_poly;
end function;


function change_poly_for_finite_field_function_field(poly)
  base_field := BaseRing(Parent(poly));
  old_y := Parent(poly).2;
  y_degree := Degree(poly, old_y);
  R1<x> := PolynomialRing(base_field);
  R<y> := PolynomialRing(R1);
  proj1 := hom< Parent(poly) -> R1 | [x, 1]>;
  res_poly := 0;
  // print Parent(poly);
  for j := 0 to y_degree do
    res_poly +:= y^j*proj1(Coefficient(poly, old_y, j));
  end for;
  return res_poly;
end function;

function birational_transform(F)
  x := Parent(F).1;
  y := Parent(F).2;
  a_n := LeadingCoefficient(F, y);
  if a_n eq 1 then
    return F;
  end if;
  n := Degree(F, y);
  new_F := y^n;
  new_F +:= &+[Coefficient(F, y, i)*a_n^(n-1-i)*y^i : i in [0..(n-1)] ];
  return new_F;
end function;
  
function naive_lift(F)
  R<x,y> := PolynomialRing(RationalField(), 2);
  monomials := Monomials(F); 
  coefficients := Coefficients(F);
  new_F := &+[Integers()!(coefficients[i]) * Evaluate(ChangeRing(monomials[i], Integers()), [x,y]) : i in [1..#monomials]];
  return new_F;
end function;

function lattice_width_transformation(F, v)
  if v cmpeq -1 then
    N := ConvexHullMonomials(F);
    _, u := Width(N);
    v := Representative(u);
  end if;
  x := Parent(F).1;
  y := Parent(F).2;
  phi := ChangeBasis(v);
  monomials := Monomials(F);
  coefficients := Coefficients(F);
  new_monomials := [];
  for monomial in monomials do
    i := Degree(monomial, 1);
    j := Degree(monomial, 2);
    new_degrees := phi([i,j]);
    // print new_degrees;
    Append(~new_monomials, [new_degrees.1, new_degrees.2]);
  end for;
  // print new_monomials;
  min_i := Minimum([new_monomials[i][1] : i in [1..#new_monomials]]);
  min_j := Minimum([new_monomials[i][2] : i in [1..#new_monomials]]);
  // print min_i, min_j;
  new_F := 0;
  for i := 1 to #new_monomials do
    new_monomials[i][1] -:= min_i;
    new_monomials[i][2] -:= min_j;
    new_F +:= coefficients[i] * x^(new_monomials[i][1]) * y^(new_monomials[i][2]);
  end for;
  // print new_monomials;
  return new_F;
end function;

function decrease_y_degree_for_low_degree_nodal_plane_curve(C)
  assert Degree(C) le 7;
  //try and get model by projection from singular point
  S := SingularPoints(C);
  if #S gt 0 then 
    // there is a rational node/singular point 
    // and we can get a y-degree (d-2) model
    pt := S[1];
    F := DefiningPolynomial(C);
    x := Parent(F).1; y := Parent(F).2;
    F_translated := Evaluate(F, [x+pt[1], y + pt[2]]);
    G := Evaluate(F_translated, [x*y, y]);
    factorisation := Factorisation(G);
    if #factorisation eq 2 then 
      G := factorisation[2][1];
      return G;
    end if;
    G := Evaluate(F_translated, [x, x*y]);
    factorisation := Factorisation(G);
    if #factorisation eq 2 then 
      G := factorisation[2][1];
      return Evaluate(G, [y,x]);
    end if;
  end if;
  C_proj := ProjectiveClosure(C);
  S_proj := SingularPoints(C_proj);
  if #S_proj gt 1 then 
    pt := S_proj[1];
    if pt[2] ne 0 then 
      C := AffinePatch(C_proj, 2);
      pt := [pt[1]*pt[2]^(-1), pt[3]*pt[2]^(-1)];
    else 
      C := AffinePatch(C_proj, 1);
      pt := [pt[2]*pt[1]^(-1), pt[3]*pt[1]^(-1)];
    end if;
    F := DefiningPolynomial(C);
    x := Parent(F).1; y := Parent(F).2;
    F_translated := Evaluate(F, [x+pt[1], y + pt[2]]);
    G := Evaluate(F_translated, [x*y, y]);
    factorisation := Factorisation(G);
    if #factorisation eq 2 then 
      G := factorisation[2][1];
      return G;
    end if;
    G := Evaluate(F_translated, [x, x*y]);
    factorisation := Factorisation(G);
    if #factorisation eq 2 then 
      G := factorisation[2][1];
      return Evaluate(G, [y,x]);
    end if;
  end if;
  return -1;
end function;

function get_gonal_plane_model(C)
  // x := Ambient(C).1; y := Ambient(C).2;
  gonality, _, gonal_map := Genus6GonalMap(C);
  def_pols := DefiningPolynomials(gonal_map);
  R<x,y,z> := PolynomialRing(BaseRing(C),3);
  extend_var := hom<Universe(def_pols) -> R | [x,y]>;
  new_poly_ring<s> := PolynomialRing(BaseRing(C));
  new_poly_ring<t> := PolynomialRing(new_poly_ring);
  F := extend_var(DefiningPolynomial(C));
  G := extend_var(def_pols[1])-z*extend_var(def_pols[2]);
  res := Resultant(F, G, y);
  factors := Factorisation(res);
  for factor in factors do 
    if IsUnivariate(factor[1]) eq false then 
      new_F := factor[1];
    end if;
  end for;
  if Degree(new_F, x) eq gonality then 
    unextend_var := hom<R->new_poly_ring | [t,1,s]>;
    new_F := unextend_var(new_F);
    coeffs := Coefficients(new_F);
    a_n := coeffs[gonality+1];
    coeffs := [a_n^(gonality-i)*coeffs[i] : i in [1..gonality] ] cat [1];
    new_F := new_poly_ring!coeffs;
    return new_F;
  end if;
  res := Resultant(F, G, x);
  factors := Factorisation(res);
  for factor in factors do 
    if IsUnivariate(factor[1]) eq false then 
      new_F := factor[1];
    end if;
  end for;
  if Degree(new_F, y) eq gonality then 
    unextend_var := hom<R->new_poly_ring | [1,t,s]>;
    coeffs := Coefficients(new_F);
    a_n := coeffs[gonality+1];
    coeffs := [a_n^(gonality-i)*coeffs[i] : i in [1..gonality] ] cat [1];
    new_F := new_poly_ring!coeffs;
    new_F := unextend_var(new_F);
    return new_F;
  end if;
  //try again after transformation (x,y) -> (x+cy, y) if first time failed
  A := Ambient(C); 
  translate := Automorphism(A, Random(BaseRing(C))*Ambient(C).2);
  C := translate;
  gonality, _, gonal_map := Genus6GonalMap(C);
  def_pols := DefiningPolynomials(gonal_map);
  R<x,y,z> := PolynomialRing(BaseRing(C),3);
  extend_var := hom<Universe(def_pols) -> R | [x,y]>;
  new_poly_ring<s> := PolynomialRing(BaseRing(C));
  new_poly_ring<t> := PolynomialRing(new_poly_ring);
  F := extend_var(DefiningPolynomial(C));
  G := extend_var(def_pols[1])-z*extend_var(def_pols[2]);
  res := Resultant(F, G, y);
  factors := Factorisation(res);
  for factor in factors do 
    if IsUnivariate(factor[1]) eq false then 
      new_F := factor[1];
    end if;
  end for;
  if Degree(new_F, x) eq gonality then 
    unextend_var := hom<R->new_poly_ring | [t,1,s]>;
    new_F := unextend_var(new_F);
    coeffs := Coefficients(new_F);
    a_n := coeffs[gonality+1];
    coeffs := [a_n^(gonality-i)*coeffs[i] : i in [1..gonality] ] cat [1];
    new_F := new_poly_ring!coeffs;
    return new_F;
  end if;
  res := Resultant(F, G, x);
  factors := Factorisation(res);
  for factor in factors do 
    if IsUnivariate(factor[1]) eq false then 
      new_F := factor[1];
    end if;
  end for;
  if Degree(new_F, y) eq gonality then 
    unextend_var := hom<R->new_poly_ring | [1,t,s]>;
    coeffs := Coefficients(new_F);
    a_n := coeffs[gonality+1];
    coeffs := [a_n^(gonality-i)*coeffs[i] : i in [1..gonality] ] cat [1];
    new_F := new_poly_ring!coeffs;
    new_F := unextend_var(new_F);
    return new_F;
  end if;
  //give up if not found yet
  return -1;
end function;


//assume F defined over F_p[x,y]
function lift_curve(F)
  A := AffineSpace(Parent(F));
  t := Cputime();
  Q := change_poly_for_finite_field_function_field(F);
  // print "Q is", Q;
  L := FunctionField(Q);
  genus := Genus(L);
  // print genus;
  N := ConvexHullMonomials(F);
  if NumberOfInteriorPoints(N) eq genus then
    // vprint Kyng, 2: "Baker's bound met, naively lifting";
    //naive lift works
    new_F := naive_lift(F);
    new_F := birational_transform(new_F);
    new_F := change_poly_for_rational_function_field(new_F);
    t_1 := Cputime(t);
    return new_F, t_1, -1, -1;
  end if;
  if genus le 5 then
    // vprint Kyng, 2: "Genus doesn't exceed 5, using CV18";
    C := Curve(A,F);
    try
      new_F, W_0, W_inf := GonalityPreservingLift(C);
      t_1 := Cputime(t);
      return new_F, t_1, W_0, W_inf;
    catch e 
      print "Lift failed, trying next";
      // vprint Kyng, 2: "Gonality Preserving Lift failed";
    end try;
  end if;
  lattice_width, u := Width(N);
  u := SetToIndexedSet(u);
  // vprint Kyng, 2: "Lattice width is", lattice_width;
  if lattice_width le 4 then
    // vprint Kyng, 2: "Lattice width doesn't exceed 5, using CV20";
    if Degree(Q) ne lattice_width then 
      new_F := lattice_width_transformation(F, u[1]);
      new_F := change_poly_for_finite_field_function_field(new_F);
    else 
      new_F := Q;
    end if;
    if lattice_width eq 3 then 
      try
        new_F := lift_gonality_3(new_F);
        t_1 := Cputime(t);
        return new_F, t_1, -1, -1;
      catch e
        // vprint Kyng, 2: "Low-gonal lifting failed";
        print "Lift failed, trying next";
      end try;
    end if;
    if lattice_width eq 4 then
      try
        new_F := lift_gonality_4(new_F);
        t_1 := Cputime(t);
        return new_F, t_1, -1, -1;
      catch e
        // vprint Kyng, 2: "Low-gonal lifting failed";
        print "Lift failed, trying next";
      end try;
      // return new_F;
    end if;
  end if;
  if lattice_width eq 5 then
    for i := 1 to #u do
      new_F := lattice_width_transformation(F, u[i]);
      new_F := change_poly_for_finite_field_function_field(new_F);
      try
        new_F := lift_gonality_5(new_F);
        t_1 := Cputime(t);
        return new_F, t_1, -1, -1;
      catch e
        // vprint Kyng, 2: "Low-gonal lifting failed";
        print "Lift failed, trying next";
      end try;
    end for;
  end if;
  if genus eq 6 then 
    C := Curve(A, F);
    new_F := get_gonal_plane_model(C);
    if new_F cmpne -1 then 
      if Degree(new_F) ge 3 and Degree(new_F) le 5 then
        if Degree(new_F) eq 5 then 
            new_F := lift_gonality_5(new_F);
        elif Degree(new_F) eq 4 then 
            new_F := lift_gonality_4(new_F);
        elif Degree(new_F) eq 3 then
            new_F := lift_gonality_3(new_F);
        end if;
        t_1 := Cputime(t);
        return new_F, t_1, -1, -1;
      end if;
    end if;    
  end if;  
  if Degree(F) le 7 then 
    C := Curve(A, F);
    new_F := decrease_y_degree_for_low_degree_nodal_plane_curve(C);
    if new_F cmpne -1 then 
      new_F := birational_transform(new_F);
      new_F := change_poly_for_finite_field_function_field(new_F);
      if Degree(new_F) ge 3 and Degree(new_F) le 5 then
        if Degree(new_F) eq 5 then 
            new_F := lift_gonality_5(new_F);
        elif Degree(new_F) eq 4 then 
            new_F := lift_gonality_4(new_F);
        elif Degree(new_F) eq 3 then
            new_F := lift_gonality_3(new_F);
        end if;
        t_1 := Cputime(t);
        return new_F, t_1, -1, -1;
      end if;
    end if;    
  end if;  
  C := Curve(A,F);
  new_F := LiftSingularCurve(C);
  new_F := birational_transform(new_F);
  new_F := change_poly_for_rational_function_field(new_F);
  t_1 := Cputime(t);
  return new_F, t_1, -1, -1;
end function;






