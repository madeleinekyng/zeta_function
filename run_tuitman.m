load "compute_lift.m";
import "/usr/local/magma/package/Geometry/Crv/Tuitman/pcc_p/pcc_p.m": num_zeta_p;

// SetGPU(true);
// GetNGPUs();
// SetNthreads(16);
// SetSeed(314);

SetVerbose("Tuitman",1);

function run_tuitman(C)
  ResetMaximumMemoryUsage();
  t := Cputime();
  Fq:=BaseRing(C);
  q:=#Fq;
  p:=Characteristic(Fq);
  n:=Degree(Fq);
  g:=Genus(C);


    t_0 := Cputime();
    hyper, H := IsHyperelliptic(C);
    t_0 := Cputime(t_0);
    if hyper then
      f,h:=HyperellipticPolynomials(H);  assert IsZero(h);
      if q eq p then
        Q:=RationalField();
        Qx<x>:=PolynomialRing(Q);
        Qxy<y>:=PolynomialRing(Qx);
        Qt<t>:=RationalFunctionField(Q);
        F:=y^2;
        for i:=0 to Degree(f) do
          F:=F-(IntegerRing()!Coefficient(f,i))*x^i;
        end for;
        W0:=IdentityMatrix(Qt,2);
        Winf:=Matrix(Qt,[[1,0],[0,1/t^(g+1)]]);
      else 
        m:=PolynomialRing(IntegerRing())!DefiningPolynomial(Fq);
        K<a>:=NumberField(m);
        Kx<x>:=PolynomialRing(K);
        Kxy<y>:=PolynomialRing(Kx);
        Kt<t>:=RationalFunctionField(K);
        F:=y^2;
        for i:=0 to Degree(f) do
          for j:=1 to n do
            F:=F-(IntegerRing()!Eltseq(Coefficient(f,i))[j])*a^(j-1)*x^i;
          end for;
        end for;
        W0:=IdentityMatrix(Kt,2);
        Winf:=Matrix(Kt,[[1,0],[0,1/t^(g+1)]]);
      end if;

      l := LPolynomial(F,p:W0:=W0,Winf:=Winf);
      t := Cputime(t);
      print p, ",", g, ",", t_0, ",", 0.00, ",", t-t_0, ",",  t, ",", GetMaximumMemoryUsage() div (1024^2);
      return l, true;
    //   return cache(C, l);
    end if;

    F := DefiningPolynomial(C);
    Q, t_lift, W0, Winf := lift_curve(F);
    if W0 cmpne -1 then
      //matrices computed during lifting
      l := num_zeta_p(Q,p:N:=0,exactcoho:=0,W0:=W0,Winf:=Winf);
    else 
      try 
        l := num_zeta_p(Q,p:N:=0,exactcoho:=0,W0:=0,Winf:=0);
      catch e 
        print "Try our singular point lift instead";
        t_lift := Cputime();
        new_F := LiftSingularCurve(C);
        t_lift := Cputime(t_lift);
        new_F := birational_transform(new_F);
        new_F := change_poly_for_rational_function_field(new_F);
        l := num_zeta_p(new_F,p:N:=0,exactcoho:=0,W0:=0,Winf:=0);
      end try;
      // l := LPolynomial(F,p);  
    end if;
    t := Cputime(t);
    print p, ",", g, ",", t_0, ",", t_lift, ",", t-(t_0+t_lift), ",",  t, ",", GetMaximumMemoryUsage() div (1024^2);
    return l, true;
end function;