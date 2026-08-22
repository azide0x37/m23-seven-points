// M23 bare-SqCt referee — paste into the free Magma calculator.
// Verifies: the seven Ni(2A,23A,23B) representatives (product, classes,
// generation) and the square-root-cycle-type base null: no tau in the
// transporter of sigma0 to sigmaInf with tau^2 = sigma1, for both
// orientations of each of the seven. Expected ledger:
//   SEVEN_OK true / GEN_ORDER 10200960 (x7) / M23_SQCT_BASE: 0 0 0 0 0 0 0
// Convention: these permutations satisfy (left action) x*y*z = id, i.e.
// in Magma right action  Z*Yi*Xi eq Id.  All identities asserted.
S := Sym(23);
X := [S| ]; Y := [S| ];
X := [Id(S) : i in [1..7]]; Y := [Id(S) : i in [1..7]];
X[1] := S ! (6,14)(7,20)(8,21)(9,19)(10,22)(12,15)(13,18)(16,23);
Y[1] := S ! (1,16,19,20,6,21,17,23,12,11,22,8,13,7,15,18,9,14,5,10,4,3,2);
X[2] := S ! (6,19)(7,15)(8,13)(9,14)(10,16)(12,20)(18,21)(22,23);
Y[2] := S ! (1,22,18,6,13,12,11,16,14,5,23,7,20,9,19,15,8,21,17,10,4,3,2);
X[3] := S ! (3,5)(4,17)(6,15)(8,20)(9,22)(12,23)(13,14)(16,18);
Y[3] := S ! (1,12,11,10,17,18,19,7,23,6,20,13,8,16,22,21,4,5,9,15,14,3,2);
X[4] := S ! (3,7)(5,18)(6,21)(9,10)(11,14)(13,23)(15,20)(17,22);
Y[4] := S ! (1,13,15,23,20,11,9,21,22,6,8,5,17,16,10,4,7,12,14,18,19,3,2);
X[5] := S ! (3,13)(4,12)(5,23)(6,7)(10,15)(14,17)(16,19)(18,21);
Y[5] := S ! (1,5,22,18,16,9,7,4,13,20,17,19,6,8,21,14,23,10,12,11,15,3,2);
X[6] := S ! (3,21)(5,9)(6,16)(8,13)(10,12)(11,15)(17,23)(19,20);
Y[6] := S ! (1,17,6,13,19,7,10,4,21,23,11,12,15,8,18,20,14,9,16,5,22,3,2);
X[7] := S ! (3,21)(4,12)(5,6)(7,23)(9,20)(11,22)(13,18)(16,19);
Y[7] := S ! (1,7,4,21,17,19,23,15,18,16,20,14,6,8,13,9,5,11,10,12,22,3,2);
Z := S ! (1,2,3,4,10,11,12,7,19,18,8,6,9,16,17,21,22,5,14,20,13,15,23);
ok := true;
for i in [1..7] do
  assert Order(X[i]) eq 2;
  assert Order(Y[i]) eq 23; assert Order(Z) eq 23;
  assert Z*Y[i]*X[i] eq Id(S);              // right-action form of x.y.z = 1
  assert Order(sub<S | X[i], Y[i]>) eq 10200960;
  printf "GEN_ORDER %o\n", Order(sub<S | X[i], Y[i]>);
end for;
printf "SEVEN_OK %o\n", ok;
counts := [];
for i in [1..7] do
  hits := 0;
  // orientation 1: (s0, s1, sInf) = (y, y^-1 x y, z) in left action.
  // orientation 2: (z, x, y).  In Magma right action the conjugation
  // condition sInf = tau^-1 s0 tau reads s0^tau eq sInf either way.
  or1 := <Y[i], X[i]^(Y[i]^-1), Z>;   // y^-1 x y (left) = X^(Y^-1) (Magma)
  or2 := <Z, X[i], Y[i]>;
  for T in [or1, or2] do
    s0 := T[1]; s1 := T[2]; sInf := T[3];
    fl, tau0 := IsConjugate(S, s0, sInf);
    assert fl;
    C := Centraliser(S, s0);
    assert Order(C) eq 23;
    for c in C do
      tau := c*tau0;
      assert s0^tau eq sInf;
      if tau^2 eq s1 then hits +:= 1; end if;
    end for;
  end for;
  Append(~counts, hits);
end for;
printf "M23_SQCT_BASE: ";
for h in counts do printf "%o ", h; end for;
printf "\n";
printf "PASS %o\n", &+counts eq 0;
