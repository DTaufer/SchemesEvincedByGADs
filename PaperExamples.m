// First, load the functions from the other file!

// Remark: 	To remove annoying indices, we identify R and S with k[x,y,z,u,v,w,...].
// 		This way, the polynomial x*y acts on x^2*y*z, and the result is 2*x*z.

// Summary:
// 	- Examples 3.10, 3.11, 3.12: learning examples.
// 	- Example 4.4: redundant GAD.
// 	- Example 4.6: long scheme (outside (d+1)-fat points).
// 	- Example 5.8: irredundant but irregular scheme.
// 	- Example 5.10: shortening tangential decompositions.
// 	- Example 5.13: better GAD for Ex.5.8, ensuring regularity.


// ------------
// Example 3.10
// ------------

R<x,y,z> := PolynomialRing(Rationals(),3);
F := (x + 3*y - 2*z)*(y + z)*z;
L := x + 3*y - 2*z;

Ftilde := Evaluate(F,[x-3*y+2*z,y,z]);
Hankel( Ftilde );

HankelKer(Ftilde) eq ideal<R | [z*(2*y-z),y^2]>;
I := ideal<R | [ Evaluate(_g,[x,-3*x+y,2*x+z]) : _g in Generators(HankelKer(Ftilde)) ]>;
I eq NaturalApolarScheme(F,L);

Radical(I) eq ideal<R | [2*y+3*z,2*x+z]>;
Dimension(I) eq 1; // projective dimension
HilbertSeries(I,4);
I subset AnnH(F);

I eq ideal<R|[(2*x+z)*(8*x-2*y+z),(3*x-y)^2]>;


// ------------
// Example 3.11
// ------------

R<x,y,z> := PolynomialRing(Rationals(),3);
F := (x + 3*y - 2*z)*(y + z)*z;
L := x;

Hankel( F );

Ibar := ideal<R | [5*z^3 + 76*y^2 - 12*y*z + 36*z^2, 2*y^2*z + z^3, y^3, 6*y*z^2 + z^3]>; // Ann(f)
{ Contract(g,Evaluate(DividedPowers(F),[1,y,z])) : g in Generators(Ibar) } eq {0};

HankelKer(F) eq NaturalApolarScheme(F,L);
I := HankelKer(F);

ideal< R | [Evaluate(g,[1,y,z]) : g in Basis(I)] > eq Ibar;

Radical(I) eq ideal<R | [y,z]>;
Dimension(I) eq 1;
HilbertSeries(I,4);
I subset AnnH(F);

I eq ideal<R|[76*x*y^2 - 12*x*y*z + 36*x*z^2 + 5*z^3, y^3, 2*y^2*z + z^3, 6*y*z^2 + z^3]>;


// ------------
// Example 3.12
// ------------

R<x,y,z> := PolynomialRing(Rationals(),3);
F := (x + 3*y - 2*z)*(y + z)*z;
L1 := y+2*z;
L2 := y;
F1 := L1^2/4*(x + 3*y - 2*z);
F2 := L2^2/4*(x + 3*y - 2*z);
F eq F1 - F2;

// First piece
F1tilde := Evaluate(4*F1,[y,x-2*z,z]);
Transpose( Hankel( StandardPowers(F1tilde) ) );

HankelKer(StandardPowers(F1tilde)) eq ideal<R | [8*y+z,z^2]>;
I1 := ideal<R | [ Evaluate(_g,[y,x,-2*y+z]) : _g in Generators(HankelKer(F1tilde)) ]>;
I1 eq NaturalApolarScheme(F1,L1);

Radical(I1) eq ideal<R | [x,2*y-z]>;
Dimension(I1) eq 1;
HilbertSeries(I1,3);
I1 subset AnnH(F1);

// Second piece
F2tilde := Evaluate(4*F2,[y,x,z]);
Transpose( Hankel( StandardPowers(F2tilde) ) );

HankelKer(StandardPowers(F2tilde)) eq ideal<R | [2*y+z,z^2]>;
I2 := ideal<R | [ Evaluate(_g,[y,x,z]) : _g in Generators(HankelKer(F2tilde)) ]>;
I2 eq NaturalApolarScheme(F2,L2);

Radical(I2) eq ideal<R | [x,z]>;
Dimension(I2) eq 1;
HilbertSeries(I2,3);
I2 subset AnnH(F2);

I := SchemeEvincedByGAD([L1,L2],[x+3*y-2*z,x+3*y-2*z],3);
I eq I1 meet I2;
I eq ideal<R|[4*x*y-10*x*z+2*y*z-z^2,x^2]>;


// -----------
// Example 4.4
// -----------

R<x,y> := PolynomialRing(Rationals(),2);

G1 := 4*x^2 + 2*x*y - 4*y^2;
G2 := -3*x - 5*y;

F := x*( G1 ) + y^2*( G2 ); 
I := SchemeEvincedByGAD([x,y],[G1,G2],3);
HilbertSeries(I,10);

G1b := 4*x + 2*y;
G2b := -7*x - 5*y;
F eq x^2*( G1b ) + y^2*( G2b );

Ib := SchemeEvincedByGAD([x,y],[G1b,G2b],3);
HilbertSeries(Ib,5);
I subset Ib;

// Waring decomposition

RQ<Q> := PolynomialRing(Rationals());
Rm7<r> := quo< RQ | [Q^2+7] >;
R<x,y> := PolynomialRing(Rm7,2);

G1 := 4*x^2 + 2*x*y - 4*y^2;
G2 := -3*x - 5*y;
F := x*( G1 ) + y^2*( G2 ); 

SchemeEvincedByGAD([x,y],[G1,G2],3) eq ideal<R|[x^2*y^3]>;

G1b := 4*x + 2*y;
G2b := -7*x - 5*y;
F eq x^2*( G1b ) + y^2*( G2b );

SchemeEvincedByGAD([x,y],[G1b,G2b],3) eq ideal<R|[x^2*y^2]>;

Iw := ideal<R | [79*x^2 - 166*x*y + 88*y^2]>;
Iw subset AnnH(F);
HilbertSeries(Iw,3);

L1 := (3*r+83)*x + 79*y;
L2 := (-3*r+83)*x + 79*y;

l1 := -(346/31061457*r + 5/986078);
l2 := 346/31061457*r - 5/986078;

F eq l1*L1^3 + l2*L2^3;
Iw eq SchemeEvincedByGAD([L1,L2],[R!1,1],3);


// -----------
// Example 4.6
// -----------

R<x,y,z,u,v,w> := PolynomialRing(Rationals(),6);

L := x;
Q := 60*z^3 + 60*z^2*u + 10*y^2*x + 70*z^2*x + 360*z*u*x + 60*u^2*x + 120*z*v*x + 70*y*x^2 + 75*z*x^2 + 70*u*x^2 + 180*v*x^2 + 10*w*x^2 + 24*x^3;

F := x^0*Q;
J := ideal<R | [w^2, v*w, u*w, z*w, y*w, v^2, u*v, z*v - 6*x*w, y*v, u^2 - 6*x*w, z*u - x*v, y*u, z^2 - x*u, y*z, y^2 - x*w]>;
J subset AnnH(F);
J eq ideal<R | [_g : _g in Generators(AnnH(F)) | Degree(_g) le 2]>;
HilbertSeries(J,3);

P := ideal<R | [y,z,u,v,w]>;
Radical(J) eq P;
P^5 subset J and not (P^4 subset J);

G := 6*x^4 + 70/3*x^3*y + 25*x^3*z + 70/3*x^3*u + 60*x^3*v + 10/3*x^3*w + 5*x^2*y^2 + 35*x^2*z^2 + 180*x^2*z*u + 60*x^2*z*v + 30*x^2*u^2 + 60*x*z^3 + 60*x*z^2*u + 5*z^4; 
De(x,G) eq F;
J eq SchemeEvincedByGAD([x],[G],4);

g := Evaluate(DividedPowers(G),[1,y,z,u,v,w]);
f := Evaluate(DividedPowers(F),[1,y,z,u,v,w]);
g-f eq 120*z^4;


// -----------
// Example 5.8
// -----------

Rl<l1,l2,l3,l4,l5,l6> := FunctionField(Rationals(),6);
R<x,y,z> := PolynomialRing(Rl,3);
G1 := 10*x^3 - 4*x^2*y + 4*x^2*z - 4*x*y^2 - 8*x*y*z - 3*x*z^2 - 8*y^3 - 4*z^3;
G2 := 5*x^3 + 9*x*y^2 - 5*y^3 - 7*y^2*z + 6*y*z^2 - z^3;

F := x*G1 + y*G2;
I := SchemeEvincedByGAD([x,y],[G1,G2],4);
HilbertSeries(I,7);

I1 := SchemeEvincedByGAD([x],[G1],4);
I2 := SchemeEvincedByGAD([y],[G2],4);

P1 := SchemeEvincedByGAD([x],[R!1],1);
P2 := SchemeEvincedByGAD([y],[R!1],1);

H := l1*x^2 + l2*x*y + l3*x*z + l4*y^2 + l5*y*z + l6*z^2;
G1l := G1 + y*H;
G2l := G2 - x*H;

F eq x*G1l+y*G2l;

I1l := SchemeEvincedByGAD([x],[G1l],4);
I2l := SchemeEvincedByGAD([y],[G2l],4);

rel1 := [];
for g in Generators(I1) do
	rel1 cat:= [ De(g,x*G1l) ];
end for;

rel2 := [];
for g in Generators(I2) do
	rel2 cat:= [ De(g,y*G2l) ];
end for;

&cat[Coefficients(_r) : _r in rel1 cat rel2]; // all these need to be 0

Hn := l2*x*y;
G1n := G1 + y*Hn;
G2n := G2 - x*Hn;

I eq SchemeEvincedByGAD([x,y],[G1n,G2n],4);


// ------------
// Example 5.10
// ------------

R<x,y,z1,z2,z3> := PolynomialRing(Rationals(),5);

L1 := x;
L2 := y;
L3 := x+y;
L4 := x-y;
L5 := x+2*y;

G1 := z1;
G2 := z2;
G3 := z3;
G4 := z1-3*z2-2*z3;
G5 := z1+z2+z3;

F := L1^2*G1 + L2^2*G2 + L3^2*G3 + L4^2*G4 + L5^2*G5;

I := SchemeEvincedByGAD([L1,L2,L3,L4,L5],[G1,G2,G3,G4,G5],3);
HilbertSeries(I,6);

IG1 := SchemeEvincedByGAD( [L1,L2,L3,L4,L5], [1,G2,G3,G4,G5], 3);
IG2 := SchemeEvincedByGAD( [L1,L2,L3,L4,L5], [G1,1,G3,G4,G5], 3);
IG3 := SchemeEvincedByGAD( [L1,L2,L3,L4,L5], [G1,G2,1,G4,G5], 3);
IG4 := SchemeEvincedByGAD( [L1,L2,L3,L4,L5], [G1,G2,G3,1,G5], 3);
IG5 := SchemeEvincedByGAD( [L1,L2,L3,L4,L5], [G1,G2,G3,G4,1], 3);

not IG1 subset AnnH(F);
not IG2 subset AnnH(F);
not IG3 subset AnnH(F);
not IG4 subset AnnH(F);
not IG5 subset AnnH(F);

(x-y)^2 eq 2*x^2+2*y^2-(x+y)^2;
F eq L1^2*(G1+2*G4) + L2^2*(G2+2*G4) + L3^2*(G3-G4) + L5^2*G5;
F eq L1^2*(3*z1-6*z2-4*z3) + L2^2*(2*z1-5*z2-4*z3) + L3^2*(-z1+3*z2+3*z3) + L5^2*G5;

I2 := SchemeEvincedByGAD([L1,L2,L3,L5],[G1+2*G4,G2+2*G4,G3-G4,G5],3);
HilbertSeries(I2,5);

(x+2*y)^2 eq 2*(x+y)^2-x^2+2*y^2;
F eq L1^2*(2*z1-7*z2-5*z3) + L2^2*(4*z1-3*z2-2*z3) + L3^2*(z1+5*z2+5*z3);

I3 := SchemeEvincedByGAD([L1,L2,L3],[2*z1-7*z2-5*z3,4*z1-3*z2-2*z3,z1+5*z2+5*z3],3);
I3 subset AnnH(F);
HilbertSeries(I3,4);

not I subset I2;
not I subset I3;


// ------------
// Example 5.13
// ------------

R<x,y,z> := PolynomialRing(Rationals(),3);
G1 := 10*x^3 - 4*x^2*y + 4*x^2*z - 4*x*y^2 - 8*x*y*z - 3*x*z^2 - 8*y^3 - 4*z^3;
G2 := 5*x^3 + 9*x*y^2 - 5*y^3 - 7*y^2*z + 6*y*z^2 - z^3;
F := x*G1 + y*G2;

G1b := 10*x^3 + x^2*y + 4*x^2*z - 4*x*y^2 - 8*x*y*z - 3*x*z^2 - 4*z^3;
G2b := x*y^2 - 5*y^3 - 7*y^2*z + 6*y*z^2 - z^3;
F eq x*G1b + y*G2b;

I := SchemeEvincedByGAD([x,y],[G1b,G2b],4);
HilbertSeries(I,5);
