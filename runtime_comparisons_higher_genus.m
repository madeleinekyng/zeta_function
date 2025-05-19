load "count_plane_model.m";
load "compute_corrections.m";
load "compute_zeta_function.m";


SetGPU(true);
SetSeed(314);
SetVerbose("Tuitman", 1);
SetVerbose("Kyng", 2);

DO_VERS1 := 1 eq flag_kyng_1;
DO_VERS2 := 1 eq flag_kyng_2;
DO_TUITMAN := 1 eq flag_tuitman;

C := AffinePatch(RandomCurveByGenus(g, GF(p)),1);

if DO_VERS1 then
  "Version 1";
  a := ComputeZetaFunctionNumerator(C : Version := 1);
  print Coefficients(a);
  exit;
end if;

if DO_VERS2 then
  "Version 2";
  b := ComputeZetaFunctionNumerator(C : Version := 2);
  print Coefficients(b);
  exit;
end if;

load "run_tuitman.m";
if DO_TUITMAN then
  "Tuitman";
  c, bool := run_tuitman(C);
  if bool eq false then
    print "Lifting for Tuitman failed \n";
  else 
    print Coefficients(c);
  end if;
  exit;
end if;

exit;
