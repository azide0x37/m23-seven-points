// Magma referee: 23-adic factorization of the descended sextic.
// Expected receipt: LOCAL23_FACTORS 2,4; LOCAL23_E 2,4; LOCAL23_F 1,1;
// LOCAL23_TAME true  (both e prime to 23).
Q := Rationals(); R<x> := PolynomialRing(Q);
f := -139453053861313073 + -868575878997768238*x^1 + -759255603013669319*x^2 + -55027953306246948*x^3 + 353749018385880145*x^4 + 206305139624557234*x^5 + 50019668646075143*x^6;
K23 := pAdicField(23, 120); RK<y> := PolynomialRing(K23);
fac := Factorization(RK!f);
degs := [Degree(g[1]) : g in fac];
print "LOCAL23_FACTORS", degs;
es := []; fs := [];
for g in fac do
  LF := LocalField(K23, g[1]);
  Append(~es, RamificationIndex(LF));
  Append(~fs, InertiaDegree(LF));
end for;
print "LOCAL23_E", es;
print "LOCAL23_F", fs;
print "LOCAL23_TAME", forall{e : e in es | e mod 23 ne 0};
print "PASS iff FACTORS [2,4] (any order), E [2,4], F [1,1], TAME true";
