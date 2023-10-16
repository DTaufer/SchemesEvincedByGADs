

------------------------------------------------------------------------------------------
---- This is the ancillary file of the paper
---- ON SCHEMES EVINCED BY GENERALIZED ADDITIVE DECOMPOSITIONS AND THEIR REGULARITY
---- by A. Bernardi, A. Oneto, D. Taufer
---- v. 2023/10
------------------------------------------------------------------------------------------

------------------------------------------------------------------------------------------
---- Construction of Natural Apolar Scheme
------------------------------------------------------------------------------------------

naturalApolarScheme = method();
naturalApolarScheme (RingElement,RingElement) := (F,L) -> (
    ringF := ring(F);
    if L == 0 then error "the linear form has to be different than zero";
    if not(ring(L) === ring(F)) then error "the form and the linear form have to be from the same ring";
-- construct the linear tranformation changing the support of L to one of the variables
    var := first entries (vars ringF);
    transf := apply(var, x -> if x == (leadTerm(L)/leadCoefficient(L)) then (
	    1/leadCoefficient(L) * ((1 + 1 / leadCoefficient L) * leadTerm L - L)
	    ) else x);
    phi := map(ringF,ringF,matrix{transf});
-- construct the dual linear transformation
    invTransf := sub(contract(transpose vars ringF, matrix phi),ringF);
    psi := map(ringF,ringF,transpose (invTransf * transpose vars ringF));
-- change of coordinats to the new support
    L1 := phi(L);
    F1 := phi(F);
-- compute the apolar ideal of the dehomogenization of the polynomial in divided powers
    ringF' := QQ[select(var, x -> x != L1)];
    f1 = sub(sub(toDividedPowers(F1), {L1 => 1}), ringF');
    f1perp = inverseSystem(f1, DividedPowers => true);
-- return the homogenization of the latter apolar after the dual change of variables
    return psi(homogenize(sub(f1perp,ringF), L1))
    )

naturalApolarScheme (List,List) := (F,L) -> (
    if #(F) != #(L) then error "the two lists must have the same number of elements";
    return intersect(for i to #(F)-1 list naturalApolarScheme(F_i,L_i))
    )

isApolar = method();
isApolar (Ideal,RingElement) := (I,F) -> (
    if not(ring(I) === ring(F)) then error "the form and the ideal have to be from the same ring";
    if not(X == saturate(X)) then error "the ideal is not saturated";
    if not(dim(X) == 1) then error "the ideal does not define a 0-dim scheme";
    G := flatten entries gens I;
    return all(G,g -> diff(g,F) == 0)
    )

------------------------------------------------------------------------------------------
---- Example 3.8, 3.9, 3.10
------------------------------------------------------------------------------------------
S = QQ[x_0,x_1,x_2];
L = x_0 + 3*x_1 - 2*x_2;
F = L*(x_1+x_2)*x_2;

X = naturalApolarScheme(F,L)
isApolar(X,F), degree X, radical X

X' = naturalApolarScheme(F,x_0)
isApolar(X',F), degree X', radical X'

use S
F1 = 1/4*(x_1+2*x_2)^2*L; L1 = x_1+2*x_2;
F2 = 1/4*x_1^2*L; L2 = x_1;

X'' = naturalApolarScheme({F1,F2},{L1,L2})
isApolar(X'',F), degree X'', primaryDecomposition radical X''

------------------------------------------------------------------------------------------
---- Example 4.4
------------------------------------------------------------------------------------------
S = QQ[x_0,x_1];
G1 = 4*x_0^2+2*x_0*x_1-4*x_1^2;
G2 = -3*x_0-5*x_1;

F = x_0*G1 + x_1^2*G2;

G1' = 4*x_0+2*x_1;
G2' = -7*x_0-5*x_1;

F == x_0^2*G1' + x_1^2*G2'

Z = naturalApolarScheme({x_0*G1,x_1^2*G2},{x_0,x_1})

use S
Z' = naturalApolarScheme({x_0^2*G1',x_1^2*G2'},{x_0,x_1})

isApolar(Z,F), degree Z, primaryDecomposition radical Z
isApolar(Z',F), degree Z', primaryDecomposition radical Z'

------------------------------------------------------------------------------------------
---- Example 5.8, 5.12
------------------------------------------------------------------------------------------
S = QQ[x_0,x_1,x_2];
G1 = 10*x_0^3 - 4*x_0^2*x_1 + 4*x_0^2*x_2 - 4*x_0*x_1^2 - 8*x_0*x_1*x_2 - 3*x_0*x_2^2 - 8*x_1^3 - 4*x_2^3;
G2 = 5*x_0^3 + 9*x_0*x_1^2 - 5*x_1^3 - 7*x_1^2*x_2 + 6*x_1*x_2^2 - x_2^3;

F = x_0*G1 + x_1*G2;

Z = naturalApolarScheme({x_0*G1,x_1*G2},{x_0,x_1})
isApolar(Z,F), degree Z, for i to 6 list hilbertFunction(i,Z)

use S

G1' = 10*x_0^3 + x_0^2*x_1 + 4*x_0^2*x_2 - 4*x_0*x_1^2 - 8*x_0*x_1*x_2 - 3*x_0*x_2^2 - 4*x_2^3;
G2' = x_0*x_1^2 - 5*x_1^3 - 7*x_1^2*x_2 + 6*x_1*x_2^2 - x_2^3;

F == x_0*G1' + x_1*G2'

Z' = naturalApolarScheme({x_0*G1',x_1*G2'},{x_0,x_1})
isApolar(Z',F), degree Z', for i to 6 list hilbertFunction(i,Z')

------------------------------------------------------------------------------------------
---- Example 5.10
------------------------------------------------------------------------------------------
S = QQ[x_0..x_4];
G1 = x_0^2;    H1 = x_2;
G2 = x_1^2;    H2 = x_3;
G3 = (x_0+x_1)^2;    H3 = x_4;
G4 = (x_0-x_1)^2;    H4 = x_2 - 3*x_3 - 2*x_4;
G5 = (x_0+2*x_1)^2;    H5 = x_2 + x_3 + x_4;

F = H1*G1 + H2*G2 + H3*G3 + H4*G4 + H5*G5

Z = naturalApolarScheme({H1*G1,H2*G2,H3*G3,H4*G4,H5*G5},{x_0,x_1,x_0+x_1,x_0-x_1,x_0+2*x_1})
isApolar(Z,F), degree Z, for i to 6 list hilbertFunction(i,Z)

use S
G1 = x_0^2;    H1 = 2*x_2-7*x_3-5*x_4;
G2 = x_1^2;    H2 = 4*x_2-3*x_3-2*x_4;
G3 = (x_0+x_1)^2;    H3 = x_2+5*x_3+5*x_4;
F == G1*H1 + G2*H2 + G3*H3

Z' = naturalApolarScheme({H1*G1,H2*G2,H3*G3},{x_0,x_1,x_0+x_1})
isApolar(Z',F), degree Z', for i to 6 list hilbertFunction(i,Z')
