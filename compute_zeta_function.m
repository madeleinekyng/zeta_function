//assume input curve is geometrically irreducible affine plane curve
//output is numerator of zeta function of its normalisation
function ComputeZetaFunctionNumerator(C : Version := 0)
  ResetMaximumMemoryUsage();
  //compute genus and corrections for input curve
  t := Cputime();
  t_0 := Cputime();
  g, corrections, F := ComputeGenusAndCorrections(C);
  t_0 := Cputime(t_0);
  vprint Kyng, 1: "ComputeGenusAndCorrections Memory (MB) : ", GetMaximumMemoryUsage() div (1024^2), "\n";
  // print t;
  if g eq 0 then 
    return 1;
  end if;
  p := Characteristic(BaseRing(C));
  //precisions lambda_r required for recovering the point-count in degree r extension
  required_precisions := [Floor(r/2 + Log(p, 4*g)) + 1 : r in [1..g] ];
  ResetMaximumMemoryUsage();
  t_1 := Cputime();
  counts := CountPointsOnTorus(F, g, required_precisions : Version := Version);
  t_1 := Cputime(t_1);
  vprint Kyng, 1: "CountPointsOnTorus Memory (MB) : ", GetMaximumMemoryUsage() div (1024^2), "\n";
  hasse_weil_errors := [0 : _ in [1..g]];
  coefficients :=  [0 : _ in [1..(2*g+1)]];
  coefficients[1] := 1; 
  coefficients[2*g+1] := p^g;
  for r := 1 to g do 
    lambda_r := required_precisions[r];
    hasse_weil_error := (counts[r] + corrections[r] - (p^r+1)) mod p^(lambda_r);
    hasse_weil_error := hasse_weil_error le 2*g*p^(r/2) select hasse_weil_error else (hasse_weil_error-p^(lambda_r));
    hasse_weil_errors[r] := hasse_weil_error;
    coefficients[r+1] := &+[hasse_weil_errors[i]*coefficients[r-i+1] : i in [1..r] ];
    coefficients[r+1] := coefficients[r+1] div r;
    coefficients[2*g+1-r] := p^(g-r)*coefficients[r+1];
  end for;
  t := Cputime(t);
  print p, ",", g, ",", t_0, ",", t_1, ",", t, ",", GetMaximumMemoryUsage() div (1024^2);
  return Polynomial(coefficients);
end function;

function zetaLinear(C)
  return ComputeZetaFunctionNumerator(C : Version := 2);
end function;

function zetaQuadratic(C)
  return ComputeZetaFunctionNumerator(C : Version := 1);
end function;



