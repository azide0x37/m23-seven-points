// Magma referee: Galois groups of the two independent descended sextics
// for the six-point M23 Hurwitz orbit (paper labels {1,2,3,4,5,7}).
// Expected: both irreducible over Q with GaloisGroup = S6 (6T16).
R<x> := PolynomialRing(Rationals());
f1 := -139453053861313073 + -868575878997768238*x^1 + -759255603013669319*x^2 + -55027953306246948*x^3 + 353749018385880145*x^4 + 206305139624557234*x^5 + 50019668646075143*x^6;
f2 := 414128288417144984367919381 + -3014801889733613820545273694*x^1 + 8281435636737711157987163503*x^2 + -10236272033398981465535697652*x^3 + 5060936190487869829531262115*x^4 + -489750524557256227855164622*x^5 + 141385642915876396665810361*x^6;
print "f1 irreducible:", IsIrreducible(f1);
print "f2 irreducible:", IsIrreducible(f2);
G1 := GaloisGroup(f1); print "f1: order", Order(G1), "id", TransitiveGroupIdentification(G1);
G2 := GaloisGroup(f2); print "f2: order", Order(G2), "id", TransitiveGroupIdentification(G2);
print "PASS iff both orders 720, ids 16";
