//helper function for computing convex hull
function right_turn(S)
    M:=Matrix(S[#S-2..#S]);
    return Determinant(HorizontalJoin(
                        ColumnMatrix([CoefficientRing(M) | 1,1,1]),M)) lt 0;
end function;

//compute convex hull of monomials in F
function NewtonPolygon(F)
    monos := Monomials(F);
    monos := [PowerSequence(Integers()) | Exponents(m) : m in monos];
    // Begin by sorting the points into lex order
    S:=Sort(monos);
    // Calculate the upper hull
    upperhull:=[S[1],S[2]];
    for i in [3..#S] do
        Append(~upperhull,S[i]);
        while #upperhull gt 2 and not right_turn(upperhull) do
            Remove(~upperhull,#upperhull - 1);
        end while;
    end for;
    // Now the lower hull
    lowerhull:=[S[#S],S[#S - 1]];
    for i in [#S - 2..1 by -1] do
        Append(~lowerhull,S[i]);
        while #lowerhull gt 2 and not right_turn(lowerhull) do
            Remove(~lowerhull,#lowerhull - 1);
        end while;
    end for;
    // Remove the first and last point from the lower hull (since they'll be in
    // the upper hull) and combine the two halves
    vertices:=upperhull cat lowerhull[2..#lowerhull - 1];
    //reverse to put in anticlockwise order
    vertices:=Reverse(vertices);
    //return vertices as list of vectors
    return [Vector(vertex) : vertex in vertices];
end function;

//returns integral points in an integral convex polygon
//input is vertices in anticlockwise order
function PointsInPolygon(vertices)
  w_0 := vertices[1];
  m := #vertices;
  points := [];
  for i := 1 to m-2 do
    a_b_vector := vertices[i+1]-w_0;
    c_d_vector := vertices[i+2]-w_0;
    alpha, u, v := XGCD(a_b_vector[1],a_b_vector[2]);
    beta := (c_d_vector, Vector([u,v]));
    gamma := Determinant(Matrix([a_b_vector, c_d_vector])) div alpha;
    horizontal_vector := a_b_vector div alpha;
    vertical_vector := Vector([-v,u]);
    j_0 := i eq 1 select 0 else 1;
    j_1 := gamma;
    points cat:= [w_0 + i*horizontal_vector + j*vertical_vector : i in [Ceiling(beta*j/gamma)..(alpha + Floor((beta-alpha)*j/gamma))], j in [j_0..j_1]];
  end for;
  return points;
end function;


//input: 
//an integral convex polygon K (represented by vertices in anticlockwise order),
//an integral simplex/triangle T containing K,
//a positive integer s specifying the dilation of K
//output:
//Kpts, Tpts, extract_rows, Q_row_lens,
//where:
//Q_row_lens is a triple containing 3 positive integers.
//Tpts are the points in max(s,3)*T
//ordered such that the first Q_row_lens[1] points 
//all have barycentric coordinate wrt [T[1], T[2], T[3]]
//greater than or equal to 1 for T[1],
//and the next Q_row_lens[2] points have 
//all have barycentric coordinate wrt [T[1], T[2], T[3]]
//greater than or equal to 1 for T[2],
//and the next Q_row_lens[3] points have 
//all have barycentric coordinate wrt [T[1], T[2], T[3]]
//greater than or equal to 1 for T[3],
//Kpts are the points in s*T
//ordered consistently with the order of points in Tpts
//extract_rows is a function that lets one
//extract the rows from a column matrix indexed by Tpts
//that are at indices belonging to Kpts
function OrderedPointsInPolygonAndTriangleDilation(K, T, s)
  a_b_vector := T[2]-T[1];
  c_d_vector := T[3]-T[1];

  //dilate and offset the polygons
  h := Max(s, 3);
  offset := (h-s)*T[1];
  K := [s*v + offset : v in K];
  T := [h*v : v in T];

  C := ChangeRing((T[1]+T[2]+T[3]), RationalField())/3;
  alpha, u_v_pair := XGCD(Eltseq(a_b_vector));
  u_v_pair := Vector(Eltseq(u_v_pair));

  beta := (u_v_pair, c_d_vector);
  gamma := Determinant(Matrix([a_b_vector, c_d_vector])) div alpha;


  horizontal_vector := a_b_vector div alpha;
  horizontal_vector_normal := Vector([-horizontal_vector[2], horizontal_vector[1]]);
  vertical_vector := Vector([-u_v_pair[2], u_v_pair[1]]);

  //"above" j_0, we begin getting points in T
  j_0 := (horizontal_vector_normal, T[1]);
  //above j_1, we get points in segment 3 (where barycentric coordinate of T[3] is >= 1/3)
  //below j_1, we get points in segments 1 and 2
  j_1 := Ceiling((ChangeRing(horizontal_vector_normal, RationalField()), C))-1;
  //"below" j_2, we get points in T
  j_2 := (horizontal_vector_normal, T[3]);

  //det_1 is used for computing horizontal limits for dividing segment 1 from segment 2
  det_1 := Determinant(Matrix([C, c_d_vector]));

  //[a b] -> [0 alpha]
  //[c d] -> [gamma beta]
  //note the matrix below has determinant -1
  U := Transpose(Matrix([horizontal_vector_normal, u_v_pair]));
  U_inverse := U^(-1);

  const_1 := (T[1]*U)[2] - (beta/gamma)*((T[1]*U)[1]);
  const_2 := (T[2]*U)[2] - ((beta-alpha)/gamma)*((T[2]*U)[1]);

  //apply unimodular_transformation_matrix to each vertex in K
  U_K := Reverse([v*U : v in K]);

  min_first_coordinate_U_K := Minimum([v[1] : v in U_K]);
  max_first_coordinate_U_K := Maximum([v[1] : v in U_K]);

  lowest_second_coordinate := ZeroMatrix(Integers(), 1, max_first_coordinate_U_K-min_first_coordinate_U_K+1);
  highest_second_coordinate := ZeroMatrix(Integers(), 1, max_first_coordinate_U_K-min_first_coordinate_U_K+1);

  for m := 1 to #K do 
    edge := U_K[m mod #K + 1]-U_K[m];

    if edge[1] gt 0 then
      //will give a low coordinate 
      i_0 := U_K[m][1];
      i_1 := U_K[m mod #K + 1][1];
      lowest_second_coordinate[1,i_0 - min_first_coordinate_U_K+1] :=  U_K[m][2];
      lowest_second_coordinate[1,i_1 - min_first_coordinate_U_K+1] :=  U_K[m mod #K + 1][2];
      for i := i_0+1 to i_1-1 do 
        lowest_second_coordinate[1,i - min_first_coordinate_U_K+1] :=  Ceiling(U_K[m][2] + edge[2]*((i-i_0)/edge[1]));
      end for;
    elif edge[1] lt 0 then 
      //will give a high coordinate 
      i_0 := U_K[m][1];
      i_1 := U_K[m mod #K + 1][1];
      highest_second_coordinate[1,i_0 - min_first_coordinate_U_K+1] :=  U_K[m][2];
      highest_second_coordinate[1,i_1 - min_first_coordinate_U_K+1] :=  U_K[m mod #K + 1][2];
      for i := i_0-1 to i_1+1 by -1 do 
        highest_second_coordinate[1,i - min_first_coordinate_U_K+1] :=  Floor(U_K[m][2] + edge[2]*((i-i_0)/edge[1]));
      end for;
    else 
      i := U_K[m][1];
      if U_K[m][2] lt U_K[m mod #K + 1][2] then 
        lowest_second_coordinate[1,i - min_first_coordinate_U_K+1] :=  U_K[m][2];
        highest_second_coordinate[1,i - min_first_coordinate_U_K+1] := U_K[m mod #K + 1][2];
      else 
        highest_second_coordinate[1,i - min_first_coordinate_U_K+1] :=  U_K[m][2];
        lowest_second_coordinate[1,i - min_first_coordinate_U_K+1] := U_K[m mod #K + 1][2];
      end if;
    end if;
  end for;


  indices := [i gt 1 select (Self(i-1) + 1 + highest_second_coordinate[1,i-1]-lowest_second_coordinate[1,i-1]) else 0 : i in [1..(max_first_coordinate_U_K-min_first_coordinate_U_K+2)]];


  U_K_points_1 := [];
  U_K_points_2 := [];
  U_K_points_3 := [];

  U_K_points := Sort(PointsInPolygon(U_K));

  if (j_1+1) ge min_first_coordinate_U_K and (j_1+1) le max_first_coordinate_U_K then 
    l := (j_1+1) - min_first_coordinate_U_K;
    index := 1 + indices[l+1];
    U_K_points_3 cat:= U_K_points[index..#U_K_points];
    U_K_points := U_K_points[1..(index-1)];
  end if;


  for j := min_first_coordinate_U_K to Minimum(j_1, max_first_coordinate_U_K) do 
    l := j-min_first_coordinate_U_K;
    second_coordinate_divider := Ceiling((j*beta+det_1)/gamma)-1;
    if (second_coordinate_divider ge lowest_second_coordinate[1, l+1]) and (second_coordinate_divider lt highest_second_coordinate[1, l+1]) then 
      //there are points in K on either side of the dividing line 
      indices_1 := [(indices[l+1]+1)..(indices[l+1]+1+(second_coordinate_divider-lowest_second_coordinate[1,l+1]))];
      indices_2 := [indices[l+1]+1+(1+second_coordinate_divider-lowest_second_coordinate[1,l+1])..indices[l+2]];
      U_K_points_1 cat:= U_K_points[indices_1];
      U_K_points_2 cat:= U_K_points[indices_2];    
    elif (second_coordinate_divider ge highest_second_coordinate[1, l+1]) then 
      //there are points on K only below the dividing line (in segment 1)
      indices_1 := [(indices[l+1]+1)..(indices[l+2])];
      U_K_points_1 cat:= U_K_points[indices_1];
    else 
      //there are points on K only above the dividing line (in segment 2)
      indices_2 := [(indices[l+1]+1)..(indices[l+2])];
      U_K_points_2 cat:= U_K_points[indices_2];
    end if;
  end for;


  K_points_1 := [v*U_inverse : v in U_K_points_1];
  K_points_2 := [v*U_inverse : v in U_K_points_2];
  K_points_3 := [v*U_inverse : v in U_K_points_3];



  //points on lines below any points in K 
  U_T_minus_K_points_1 := [Vector([j,i]) : i in [Ceiling(const_1 + beta/gamma*j)..Ceiling((j*beta+det_1)/gamma)-1], j in [j_0..min_first_coordinate_U_K-1]];


  //points on lines that intersect K with 2nd coordinate below K
  U_T_minus_K_points_1 cat:= [Vector([j,i]) : i in [Ceiling(const_1 + beta/gamma*j)..Minimum(lowest_second_coordinate[1,j-min_first_coordinate_U_K+1]-1, Ceiling((j*beta+det_1)/gamma)-1)], j in [min_first_coordinate_U_K..Minimum(max_first_coordinate_U_K, j_1)]];



  //points on lines that intersect K with 2nd coordinate above K
  U_T_minus_K_points_1 cat:= [Vector([j,i]) : i in [highest_second_coordinate[1,j-min_first_coordinate_U_K+1]+1..Ceiling((j*beta+det_1)/gamma)-1], j in [min_first_coordinate_U_K..Minimum(max_first_coordinate_U_K, j_1)]];



  //points on lines above any points in K  
  U_T_minus_K_points_1 cat:= [Vector([j,i]) : i in [Ceiling(const_1 + beta/gamma*j)..Ceiling((j*beta+det_1)/gamma)-1], j in [max_first_coordinate_U_K+1..j_1]];


  T_minus_K_points_1 := [v*U_inverse : v in U_T_minus_K_points_1];

  //points on lines below any points in K 
  U_T_minus_K_points_2 := [Vector([j,i]) : i in [Ceiling((j*beta+det_1)/gamma)..Floor(const_2 + (beta-alpha)*j/gamma)], j in [j_0..min_first_coordinate_U_K-1]];


  //points on lines that intersect K with 2nd coordinate below K
  U_T_minus_K_points_2 cat:= [Vector([j,i]) : i in [Ceiling((j*beta+det_1)/gamma)..lowest_second_coordinate[1,j-min_first_coordinate_U_K+1]-1], j in [min_first_coordinate_U_K..Minimum(max_first_coordinate_U_K, j_1)]];


  //points on lines that intersect K with 2nd coordinate above K
  U_T_minus_K_points_2 cat:= [Vector([j,i]) : i in [Maximum(highest_second_coordinate[1,j-min_first_coordinate_U_K+1]+1,Ceiling((j*beta+det_1)/gamma))..Floor(const_2 +(beta-alpha)*j/gamma)], j in [min_first_coordinate_U_K..Minimum(max_first_coordinate_U_K, j_1)]];




  

  //points on lines above any points in K  
  U_T_minus_K_points_2 cat:= [Vector([j,i]) : i in [Ceiling((j*beta+det_1)/gamma)..Floor(const_2 +(beta-alpha)*j/gamma)], j in [max_first_coordinate_U_K+1..j_1]];





  T_minus_K_points_2 := [v*U_inverse : v in U_T_minus_K_points_2];

  //points on lines below any points in K 
  U_T_minus_K_points_3 := [Vector([j,i]) : i in [Ceiling(const_1 +beta/gamma*j)..Floor(const_2 +(beta-alpha)*j/gamma)], j in [j_1+1..min_first_coordinate_U_K-1]];


  //points on lines that intersect K with 2nd coordinate below K
  U_T_minus_K_points_3 cat:= [Vector([j,i]) : i in [Ceiling(const_1 +beta/gamma*j)..lowest_second_coordinate[1,j-min_first_coordinate_U_K+1]-1], j in [Maximum(min_first_coordinate_U_K, j_1+1)..max_first_coordinate_U_K]];


  //points on lines that intersect K with 2nd coordinate above K
  U_T_minus_K_points_3 cat:= [Vector([j,i]) : i in [highest_second_coordinate[1,j-min_first_coordinate_U_K+1]+1..Floor(const_2 +(beta-alpha)*j/gamma)], j in [Maximum(min_first_coordinate_U_K, j_1+1)..max_first_coordinate_U_K]];

  //points on lines above any points in K  
  U_T_minus_K_points_3 cat:= [Vector([j,i]) : i in [Ceiling(const_1 +beta/gamma*j)..Floor(const_2 +(beta-alpha)*j/gamma)], j in [Maximum(max_first_coordinate_U_K+1,j_1+1) ..j_2]];


  T_minus_K_points_3 := [v*U_inverse : v in U_T_minus_K_points_3];

  //compute points in s*K (original K)
  Kpts := K_points_1 cat K_points_2 cat K_points_3;
  if s lt 3 then 
    Kpts := [v - offset : v in Kpts];
  end if;

  //T ordered so that points "close to" T[1] occur first,
  //followed by points "close to" T[2],
  //followed by points "close to" T[3]
  Tpts := K_points_1 cat T_minus_K_points_1 cat K_points_2 cat T_minus_K_points_2 cat K_points_3 cat T_minus_K_points_3;

  //extract entries will take a row vector of size #T,
  //where the entries are indexed by v in hT, in the order computed by this function,
  //and extract the entries corresponding to sK, in the order computed by this function
  extract_entries := func<mat | HorizontalJoin(<ColumnSubmatrix(mat, 1, #K_points_1), ColumnSubmatrix(mat, #K_points_1 + #T_minus_K_points_1 + 1, #K_points_2), ColumnSubmatrix(mat, #K_points_1 + #T_minus_K_points_1 + #K_points_2 + #T_minus_K_points_2 + 1 , #K_points_3)>)>;

  Q_row_lens := <(#K_points_1 + #T_minus_K_points_1), (#K_points_2 + #T_minus_K_points_2), (#K_points_3 + #T_minus_K_points_3)>;
  return Kpts, Tpts, extract_entries, Q_row_lens;
end function;

// Assume Conv(vertices) is contained in the 1st quadrant
// vertices is a list of vectors defining an integral convex polygon
function ComputeBoundingTriangle(vertices, p)
  m := #vertices;
  //initialise bounding triangle as first triangle in triangulation
  T := [vertices[1], vertices[2], vertices[3]];
  //initialise maximum volume of internal triangle as volume 
  //of first triangle in triangulation
  max_vol := Determinant(Matrix([T[2]-T[1], T[3]-T[1]]));
  if m gt 3 then 
    for i := 1 to (m-2) do 
      u_0 := vertices[i];
      for j := i+1 to (m-1) do 
        u_1 := vertices[j];
        for k := j+1 to m do 
          u_2 := vertices[k];
          vol := Determinant(Matrix([u_1-u_0, u_2-u_0]));
          if vol ge max_vol then 
            max_vol := vol;
            w_0 := u_0;
            w_1 := u_1;
            w_2 := u_2;
          end if;
        end for;
      end for;
    end for;
    //we have found internal triangle of max vol
    //now compute bounding triangle
    T[1] := w_0 + (w_2 - w_1);
    T[2] := w_1 + (w_0 - w_2);
    T[3] := w_2 + (w_1 - w_0);
    max_vol := 4*max_vol;

    //check if Conv((0,0), (d, 0), (0,d)) is a better fit
    //than the bounding triangle we computed
    d := Maximum([(v, Vector([1,1])) : v in vertices]);
    if d^2 le max_vol then 
      T[1] := Vector([0,0]);
      T[2] := Vector([d,0]);
      T[3] := Vector([0,d]);
      max_vol := d^2;
    end if;
  end if;

  //now check if volume is divisible by p,
  //and modify triangle if so
  if max_vol mod p eq 0 then 
    a_b_vector := T[2]-T[1];
    c_d_vector := T[3]-T[1];
    alpha, u, v := XGCD(a_b_vector[1],a_b_vector[2]);
    gamma := Determinant(Matrix([a_b_vector, c_d_vector])) div alpha;
    beta := (c_d_vector, Vector([u,v]));
    t, beta := Quotrem(beta, gamma);
    a_0 := a_b_vector[1] div alpha;
    b_0 := a_b_vector[2] div alpha;
    u := u + t*(b_0);
    v := v - t*(a_0);
    if alpha mod p eq 0 then 
      T[2] +:= Vector([a_0, b_0]);
    end if;
    if gamma mod p eq 0 then 
      w_2 := Ceiling((gamma-1)/alpha);
      if w_2 mod p eq 0 then 
        w_2 +:= 1;
      end if;
      w_1 := Floor(w_2*beta/gamma);
      T[3] +:= Vector([w_1, w_2])*Matrix(Integers(), 2, 2, [a_0, b_0, -v, u]);
    end if;
  end if;
  return T, Determinant(Matrix([T[2]-T[1],T[3]-T[1]]));
end function;

function ComputeMatrixByDeformationRecurrence(F, K, T, p, s, lambda)
  residue_ring_factorial := Integers(p^(lambda+2*s));
  residue_ring_recurrence := Integers(p^(lambda+s));
  final_residue_ring := Integers(p^(lambda));

  coeffs, monos := CoefficientsAndMonomials(F); 
  F_monomial_dictionary := AssociativeArray();
  for i := 1 to #monos do 
    F_monomial_dictionary[Vector(Exponents(monos[i]))] := coeffs[i];
  end for;

  m := (p-1)*s;
  h := Maximum(s, 3);

  factorial_p_vals := [i gt 1 select Self(i) + Valuation(i,p) else 0 : i in [0..m]];
  factorials_without_p_factors := [i gt 1 select Self(i) * (factorial_p_vals[i+1] eq factorial_p_vals[i] select i else (i div p^(factorial_p_vals[i+1] - factorial_p_vals[i]))  ) else residue_ring_factorial!1 : i in [0..m]];

  multinomial_coeff_valid_eltseq := func<x | factorials_without_p_factors[m+1]/(factorials_without_p_factors[x[1]+1]*factorials_without_p_factors[x[2]+1]*factorials_without_p_factors[x[3]+1])*p^(factorial_p_vals[m+1]-factorial_p_vals[x[1]+1]-factorial_p_vals[x[2]+1]-factorial_p_vals[x[3]+1]) >;
  multinomial_coeff := func<x | &and[(IsIntegral(x[i]) and (x[i] ge 0)) : i in [1..3]] select multinomial_coeff_valid_eltseq(Eltseq(ChangeRing(x,Integers()))  )  else 0>;

  sKPoints, hTPoints, extract_entries, row_lens := OrderedPointsInPolygonAndTriangleDilation(K, T, s);

  vertex_matrix := Matrix([T[1], T[2],T[3]]);
  extended_vertex_matrix := HorizontalJoin(vertex_matrix, Matrix(Integers(), 3, 1, [1,1,1]));
  inverse_vertex_matrix := ChangeRing(extended_vertex_matrix, RationalField())^(-1);
  vol := Determinant(extended_vertex_matrix);

  a_vectors := vol*Transpose(RowSubmatrix(inverse_vertex_matrix, 1, 2));
  C_constants := -vol*inverse_vertex_matrix[3];

  a_vectors := ChangeRing(a_vectors, Integers());
  C_constants := ChangeRing(C_constants, Integers());
  
  hTPointsConvexCombs := HorizontalJoin(Matrix([t: t in hTPoints]), Matrix(Integers(), #hTPoints, 1, [h : _ in [1..#hTPoints]]));
  hTPointsConvexCombs := ChangeRing(hTPointsConvexCombs, RationalField());
  hTPointsConvexCombs *:= inverse_vertex_matrix;


  M_s := ZeroMatrix(final_residue_ring, #sKPoints, #sKPoints);
  Q_0 := ZeroMatrix(residue_ring_recurrence, #hTPoints, 0);
  Q_1 := ZeroMatrix(residue_ring_recurrence, #hTPoints, 0);
  A_1 := ZeroMatrix(residue_ring_recurrence, #hTPoints, 0);
  A_2 := ZeroMatrix(residue_ring_recurrence, #hTPoints, 0);

  F_coeff := func<v| IsDefined(F_monomial_dictionary, v) select F_monomial_dictionary[v] else 0>;
  
  hTPoints_index_1 := 1;
  for max_index := 1 to 3 do 
    hTPoints_index_2 := hTPoints_index_1 + row_lens[max_index] - 1;
    indices := [hTPoints_index_1..hTPoints_index_2];
    v_t := vertex_matrix[max_index];
    a_t := a_vectors[max_index];
    C := C_constants[max_index];

    F_monomials_for_Q := [v_t - t + z :  t in hTPoints[indices], z in hTPoints];
    F_coeffs := [F_coeff(v) :  v in F_monomials_for_Q];
    F_coeffs_matrix := Matrix(residue_ring_recurrence, #hTPoints, row_lens[max_index], F_coeffs);
    D_0 := DiagonalMatrix(residue_ring_recurrence, #hTPoints, [(-(a_t, z)-m*C) :  z in hTPoints]);

    Q_1 := HorizontalJoin(Q_1, Matrix(residue_ring_recurrence, #hTPoints, row_lens[max_index], [IsZero(f) select f else (C-(a_t, F_monomials_for_Q[i]))*f : i->f in F_coeffs]));
    Q_0 := HorizontalJoin(Q_0, D_0 * F_coeffs_matrix);
    A_1 := HorizontalJoin(A_1, a_t[1]*F_coeffs_matrix);
    A_2 := HorizontalJoin(A_2, a_t[2]*F_coeffs_matrix);
    hTPoints_index_1 := hTPoints_index_2 + 1;
  end for;


  sKPoints_copy := sKPoints;
  range := [1..#sKPoints];
  row_computed := [false : _ in range];
  edge_polynomial_ring := PolynomialRing(final_residue_ring);
  ParallelSort(~sKPoints_copy, ~range);
  //the following loop computes rows of M_s
  //corresponding to indices v in sK on the edges of sK
  //since most of the entries in that row will be zero
  //and applying the deformation recurrence to compute such a row
  //will be slower than just computing the appropriate polynomial power
  //for the univariate polynomial corresponding to the edge of sK
  for i := 1 to #K do 
    edge_direction := K[i mod #K + 1] - K[i];
    gcd_edge_direction, bezout_coeffs := XGCD(Eltseq(edge_direction));
    bezout_coeffs := Vector(bezout_coeffs);
    edge_direction := edge_direction div gcd_edge_direction;
    edge_direction_normal := Vector([-edge_direction[2], edge_direction[1]]);
    gamma := [K[i] + t*edge_direction : t in [0..gcd_edge_direction]];
    F_gamma := edge_polynomial_ring![F_coeff(v) : v in gamma];
    F_gamma_power := F_gamma^((p-1)*s);
    s_gamma_init_vertex := s*K[i];
    //iterate along v in edge s*gamma of sK
    for t := 0 to s*gcd_edge_direction-1 do 
      v := s_gamma_init_vertex + t*edge_direction;
      //find index of v in sKPoints
      //via binary search of sorted list
      L := 1;
      R := #sKPoints;
      while L le R do 
        M := ShiftRight(L+R,1);
        if sKPoints_copy[M] lt v then 
          L := M+1;
        elif sKPoints_copy[M] gt v then 
          R := M-1;
        else 
          break;
        end if;
      end while;
      i_v := range[M];
      //for v on s*gamma, the only u in sK for which [F^((p-1)s)]_{pv-u} may be non-zero
      //are for those u also on s*gamma. 
      //(otherwise pv-u will have negative barycentric coeffs on vertices of (p-1)*s*K outside of the end points of the edge
      // (p-1)*s*gamma, i.e. pv-u will be outside of (p-1)*s*K)
      //so pv-u = p*(sK[i] + t*direction_vector)-(sK[i]+t'*direction_vector)
      //        = (p-1)*s*K[i] + (p*t-t')*direction_vector
      //corresponding coeff of F_gamma_power is at the (p*t-t')-th coefficient
      //t' is given by dot prod (u-sK[i], bezout_coefficients)
      M_s[i_v] := Vector( [(u-s_gamma_init_vertex, edge_direction_normal) eq 0 select ((u-s_gamma_init_vertex, bezout_coeffs) le p*t select Coefficient(F_gamma_power, p*t-(u-s_gamma_init_vertex, bezout_coeffs)) else 0) else 0 : u in sKPoints] );
      row_computed[i_v] := true;
    end for;
  end for;



  scale_final_vector_unit_part := (residue_ring_recurrence!1/residue_ring_recurrence!vol)^m * 1/residue_ring_recurrence!factorials_without_p_factors[m+1];
  divide_final_vector_prime_power_part := p^factorial_p_vals[m+1];

  // t_0 := Cputime();
  v_index := 0;
  for v in sKPoints do 
    v_index +:= 1;
    if row_computed[v_index] then 
      continue;
    end if;
    w := p*v + (h-s)*vertex_matrix[1];
    

    const_summand := Vector(RationalField(), [w[1], w[2], h+m])*inverse_vertex_matrix;
    U := Vector(residue_ring_recurrence, [multinomial_coeff(const_summand - hTPointsConvexCombs[i]) : i in [1..#hTPoints]]);    
    
//residue_ring_recurrence := Integers(p^(lambda+s));

    Q := Q_0 + w[1]*A_1 + w[2]*A_2;

//time
    if 1 eq 1 then
	LR := pAdicQuotientRing(p, lambda+s);
	Z := IntegerRing();

	sym := func<V | ChangeRing(ChangeRing(V, LR), Z)>;
	U := sym(U);
	Q := sym(Q);
	Q_1 := sym(Q_1);

	Q := SparseMatrix(Q);
	Q_1 := SparseMatrix(Q_1);

	trans := 0 eq 1; // seems slower
	if trans then
	    Transpose(~Q);
	    Transpose(~Q_1);
	end if;

	for i := 0 to (m-1) do 
	  if trans then
	      U := MultiplyByTranspose(U, Q);
	  else
	      U *:= Q;
	  end if;
	  U := sym(U);
	  Q +:= Q_1;
	end for;
    else
	for i := 0 to (m-1) do 
	    U *:= Q;
	    Q +:= Q_1;
	end for;
    end if;

//// "Final U:", U;
    //delete extraneous entries from U 
    //(entries that correspond to monomials u outside of sK)
//// "scale_final_vector_unit_part:", scale_final_vector_unit_part;
//"vec extract:", Vector(extract_entries(U));
    U := scale_final_vector_unit_part * Vector(extract_entries(U));
//"new U", U;
    U := ChangeRing(ChangeRing(U, Integers()) div divide_final_vector_prime_power_part, final_residue_ring);

//// "final U", U;

    M_s[v_index] := U;
  end for;

  return M_s;
end function;

function ComputeMatrixNaive(F, NPolygonVertices, p, s, lambda)
  basis := PointsInPolygon([s*v : v in NPolygonVertices] );
  M_s := ZeroMatrix(Integers(p^lambda), #basis, #basis);
  F_power := F^((p-1)*s);
  for i:=1 to #basis do
    v := basis[i];
    for j :=1 to #basis do 
      u := basis[j];
      w_2 := p*v[2]-u[2]; 
      w_1 := p*v[1]-u[1];
      if w_2 ge 0 and w_1 ge 0 then
        y_coeff := Coefficient(F_power, w_2);
        M_s[i, j] := Coefficient(y_coeff, w_1);
      end if;
    end for;
  end for;
  return M_s;
end function;


function largest_power(s, upper_limits)
  D := #upper_limits;
  largest_pow := 1;
  for r:=1 to D do
    if upper_limits[r] ge s then
      //this means that matrix M_s occurs in the 
      //sum for the trace formula for |X(F_{p^r})|
      //meaning that the power M_s^r will be required
      largest_pow := r;
    end if;
  end for;
  return largest_pow;
end function;

function smallest_power(s, upper_limits)
  D := #upper_limits;
  smallest_pow := D;
  for r:=0 to (D-1) do
    if upper_limits[D-r] ge s then
      //this means that matrix M_s occurs in the 
      //sum for the trace formula for |X(F_{p^(D-r)})|
      //meaning that the power M_s^(D-r) will be required
      smallest_pow := D-r;
    end if;
  end for;
  return smallest_pow;
end function;

function CountPointsOnTorus(F, R, PrecSeq : Version := 0)
// {Counts the points on the curve defined by F inside the torus}
  lambda := Maximum(PrecSeq);
  p := Characteristic(Parent(F));
  K := NewtonPolygon(F);
  //upper limit in trace formula for computing #C(F_{q^r}) mod p^lambda_r 
  trace_formula_upper_limits := [PrecSeq[r] + Ceiling(PrecSeq[r]/((p-1)*r) )-1 : r in [1..R] ];
  S := Maximum(trace_formula_upper_limits);
  traces := [[0 : _ in [1..R]] : _ in [1..S] ];
  //for each M_s, find the smallest power of it that we ever need to compute
  lower_limits := [smallest_power(s, trace_formula_upper_limits) : s in [1..S]];
  //for each M_s, find the largest power of it that we ever need to compute
  upper_limits := [largest_power(s, trace_formula_upper_limits) : s in [1..S]];

  if Version eq 0 then 
    Version := 1;
  end if;

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

  compute_matrix_time := 0.0;
  traces_of_powers_time := 0.0;
  for s := 1 to S do
    t := Cputime();
    M_s := ComputeMatrix(s);
    t := Cputime(t); compute_matrix_time +:= t;
    vprintf Kyng, 2: "Compute M_%o: %o\n", s, t;
    L := lower_limits[s];
    H := upper_limits[s];
    len := H-L+1;
    /*
    w is width of "window" of consecutive powers to be set up first.
    Not sure which is optimal choice (floor or ceiling of Sqrt(len)).
    */
    t := Cputime();
    w := Isqrt(len);
    P := [M_s];
    if L eq 1 then
        traces[s][1] := Trace(P[1]);
    end if;
    //compute baby steps M_s^2, ..., M_s^w
    for i := 2 to w do 
      Append(~P, P[i - 1] * M_s);
      if i ge L then 
        traces[s][i] := Trace(P[i]);
      end if;
    end for;

    target := L - w;
    //need M_s^(i) for i >= L-w
    //to compute M_s^L by a baby step multiplication
    //i.e., M_s^L = M_s^i * M_s^j for some j in {1,...,w}
    //loop essentially does binary powering to get power
    //close to M_s^L
    while #P lt target do 
      ow := w;
      w := 1;
      //increase w while [M_s^1, ..., M_s^w] has been computed and stored
      //usually will just get w = ow
      while w le #P + 1 and IsDefined(P, w+1) do 
        w +:= 1;
      end while;
      if w gt ow then 
        target := L-w;
        if #P ge target then 
          break;
        end if;
      end if;
      l := #P;
      good_i := 0;
      for i := l to 1 by -1 do
        //find first power M_s^i that we have computed s.t.
        //M_s^(i + #P) is a smaller power than M_s^L
        if IsDefined(P, i) and l + i le L then
          good_i := i;
          break;
        end if;
      end for;
      i := good_i;
      //compute M_s^l * M_s^i = M_s^(l+i)
      P[l + i] := P[l] * P[i];
      if l+i ge L then 
        traces[s][l + i] := Trace(P[l + i]);
      end if;
    end while;
    //now in the sequence P
    //we have a matrix M_s^(L-i) for some i in {0, ..., w}
    l := #P;


    while l lt H do 
      if l ge L then 
        //do giant step (i.e., mult by M_s^w)
        if not IsDefined(P, l) then 
          P[l] := P[l - w] * P[w];
        end if;
        if not IsDefined(traces[s], l) or traces[s][l] eq 0 then
          traces[s][l] := Trace(P[l]);
        end if;
      end if;
      for i := 1 to w do 
        li := l + i;
        if li lt L then 
          //li is not a power in the range [L..H]
          continue;
        end if;
        if li gt H then 
          //we have gone past the power H and do not need 
          //traces at this power or beyond
          break;
        end if;
        if i eq w and li lt H then 
          continue;
        end if;
        //do trace-of-product baby step 
        traces[s][li] := TraceOfProduct(P[l], P[i]);
      end for;
      l +:= w;
    end while;
    t := Cputime(t); traces_of_powers_time +:= t;
    vprintf Kyng, 2: "Traces of powers for M_%o: %o\n", s, t;
  end for;
  counts := [];
  for r := 1 to R do
    lambda_r := PrecSeq[r];
    tau_r := Ceiling(lambda_r/((p-1)*r));
    upper_limit := trace_formula_upper_limits[r];
    count := 1;
    count +:= &+[(-1)^s*(&+[Binomial(-lambda_r, t)*Binomial(lambda_r, s-t) : t in [0..tau_r-1]])*traces[s][r] : s in [1..upper_limit]];
    count := (p^r-1)^2*count;
    count := Integers(p^lambda_r)!count;
    count := Integers()!count;
    Append(~counts, count);
  end for;
  vprint Kyng: "ComputeMatrix cumulative time:", compute_matrix_time;
  vprint Kyng: "TracesOfPowers cumulative time:", traces_of_powers_time;
  return counts;
end function;
