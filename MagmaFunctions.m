// load "/home/dtaufer/Scrivania/Tensor/Conti/WorkingFunctions/FastApolarity.txt";


// ------------------------
// Circ action - Derivation
// ------------------------


function De(_g,_f)
// Given any polynomials g and f in the same space, it returns g circ f.
	out := 0;
	for _m in Terms(_g) do
		tmp := _f;
		exps := Exponents(_m);
		for i in [1..#exps] do
			for itmp in [1..exps[i]] do
				tmp := Derivative(tmp,Parent(_f).i);
			end for;
		end for;
		out +:= Coefficients(_m)[1]*tmp;
	end for;
	return out;
end function;


// -----------------------------
// Divided Powers & contractions
// -----------------------------


function MonomialFactorial( _m )
// Given a monomial m = x^a, it returns a!.
	return &*[Factorial(e) : e in Exponents( _m )];
end function;

function DividedPowers( _F )
// Given an homogeneous form F, it returns Fdp, i.e. F written with divided powers.
	return &+[_t*MonomialFactorial(_t) : _t in Terms(_F)];
end function;

function StandardPowers( _Fdp )
// Given an homogeneous form Fdp in divided powers, it returns the corresponding F in the standard monomial basis.
	return &+[_t/MonomialFactorial(_t) : _t in Terms(_Fdp)];
end function;

function MonomialContraction( _s, _t )
// Given two non-zero monomials s,t in the same space, it returns s (contract) t.
	local m,b;
	b, m := IsDivisibleBy(Monomials(_t)[1],Monomials(_s)[1]);
	if b then return Coefficients(_s)[1]*Coefficients(_t)[1]*m;
	else return 0; end if;
end function;

function Contract( _G, _F )
// Given two polynomials F,G in the same space, it returns G (contract) F.
	if _G eq 0 or _F eq 0 then return 0; end if;
	return &+[ MonomialContraction(_s,_t) : _s in Terms(_G), _t in Terms(_F)];
end function;


// -----------------------------
// Catalecticant matrices & AnnH
// -----------------------------


function Catalecticant(_i, _F)
// It returns the i-th catalecticant of the given homogeneous F.
	local R,d;
	R := Parent(_F);
	d := Degree(_F);
	return Matrix(BaseRing(R), [ [MonomialCoefficient(_x,m) : m in MonomialsOfDegree(R,d-_i)] : _x in [De(m,_F) : m in MonomialsOfDegree(R,_i)]]);
end function;

function AnnH(_F)
// It returns the annihilator ideal (by derivation) of the given homogeneous F.
	local R,d,I;
	R := Parent(_F);
	d := Degree(_F);
	I := ideal< R | [_x : _x in MonomialsOfDegree(R,d+1)] cat &cat[ [ &+[ v[j] * MonomialsOfDegree(R,i)[j] : j in [1..#MonomialsOfDegree(R,i)] ] : v in Basis(Kernel(Catalecticant(i, _F)))] : i in [0..d]] >;
	Groebner(I); // ** It computes a groebner basis of this ideal. If only interested in the ideal, remove this line I.
	return I;
end function;


// ---------------
// Hankel & Ann(f)
// ---------------


function Hankel( _F : small := false )
// It returns the Hankel matrix of an homogeneous form F of positive degree.
// Note: the matrix is transposed with respect to paper's notation, since Magma computes left kernels by default.
// If small is set true, it returns the smaller square matrix when it recognizes that the given F is not equal to L^k*x0^(d-k), for some linear form L.
	local R,n,Fdp,f,d,mons,F1,fact;
	R := Parent(_F);
	n := Rank(R);
	Fdp := DividedPowers(_F);
	f := Evaluate(Fdp, [1] cat [ R.i : i in [2..n]]);
	d := Degree( f );
	mons := [ Evaluate(_m, [1] cat [ R.i : i in [2..Rank(R)]]) : _m in MonomialsOfDegree(Parent(_F),d) ];
	if small then
		F1 := Evaluate(_F, [1] cat [ R.i : i in [2..n]]); // <- Test if we can use the square Hankel
		fact := Factorization(F1); // <- The function IsPower would be more efficient, but it depends on the base field! E.g. IsPower(2*x^2,2) = false over Q
		if Degree(F1) le 0 or ( #fact eq 1 and Degree(fact[1][1]) eq 1 ) then 
			return Matrix( Binomial(n+d, d+1), Binomial(n+d-1, d), [MonomialCoefficient(f,ma*mb) : ma,mb in mons] cat [0 : i in [1..Integers()!(Binomial(n+d-1, d)^2*(n-1)/(d+1))]] );
		else
			return Matrix( Binomial(n+d-1, d), [MonomialCoefficient(f,ma*mb) : ma,mb in mons] );
		end if;
	else
		return Matrix( Binomial(n+d, d+1), Binomial(n+d-1, d), [MonomialCoefficient(f,ma*mb) : ma,mb in mons] cat [0 : i in [1..Integers()!(Binomial(n+d-1, d)^2*(n-1)/(d+1))]] );
	end if;
end function;

function HankelKer(_F : efficient := false)
// It returns the homogeneous kernel of the Hankel operator defined by F
// If efficient is set true, it tries to use smaller Hankel matrices. This is slightly more efficient for large number of variables and degree of F
	local R,Ra,mons,H,gens,Ih,hR;
	R := Parent(_F);	
	Ra := PolynomialRing( BaseRing(R), Rank(R)-1 );
	mons := &cat( [SetToSequence(MonomialsOfDegree(Ra,i)) : i in [0..Degree(_F)+1]] );
	H := Hankel(_F : small := efficient);
	gens := [ &+[v[i]*mons[i] : i in [1..#ElementToSequence(v)]] : v in Basis(Kernel(H))];
	Ih := Homogenization(ideal<Ra|gens>);
	hR := hom< Parent(Generators(Ih)[1]) -> R | SetToSequence(MonomialsOfDegree(R,1))>;
	return ideal<R|[ hR(_G) : _G in Generators(Ih)]>;
end function;


// ------------------------------------------------
// Natural apolar schemes & Schemes evinced by GADs
// ------------------------------------------------


function Swap( _L, _i, _j )
// Given a list L, and returns the same list after swapping the places i and j
	local nL, tmp;
	nL := _L;
	if _i gt #_L or _j gt #_L then
		"Indexes longer than the sequence to swap"; return _L;
	end if;
	tmp := _L[_i];
	nL[_i] := _L[_j];
	nL[_j] := tmp;
	return nL;
end function;

function NaturalApolarScheme( _F, _L )
// It returns the natural scheme apolar to F and supported at L
// L may have zero X-coefficient
	local R,K,vars,n,fix,InvBaseChange,M,b,BaseChange,Fb,Ib,BaseChangeT,Hgen;
	R := Parent(_F);
	K := BaseRing(R);
	n := Rank(R);
	vars := SetToSequence(MonomialsOfDegree(R,1));
// Here we fix the case when L has zero X-coefficient
	fix := Index(vars,LeadingMonomial(_L));
	_F := Evaluate( _F, Swap( vars, 1, fix ) );
	_L := Evaluate( _L, Swap( vars, 1, fix ) );
// Base change
	InvBaseChange := [_L] cat vars[2..n];
	M := (Matrix(n, &cat[ [MonomialCoefficient(b,m) : m in vars] : b in InvBaseChange]))^(-1);
	b := ElementToSequence(Rows(M)[1]);
	BaseChange := [ &+[b[_i]*vars[_i] : _i in [1..n]] ] cat vars[2..n];
	Fb := Evaluate(_F, BaseChange);
// Homogenized Ann(f)
	Ib := HankelKer(Fb);
// Dual base change + fix
	BaseChangeT := [ &+[Transpose(M)[_j][_i]*vars[_i] : _i in [1..n]] : _j in [1..n] ];
	Hgen := [ Evaluate( Evaluate(_G, BaseChangeT), Swap( vars, 1, fix )) : _G in Generators(Ib)];
// Return
	return ideal<R|Hgen>;
end function;

function SchemeEvincedByGAD( _Ls, _Gs, _d )
// It returns the homogeneous ideal defining the scheme evinced by the gad sum Li^(d-deg(Gi))Gi
// Note: d must be >= deg(Gi)
// Li are not required to have non-zero X coefficient
	return &meet[ NaturalApolarScheme(_Ls[i]^(_d - Degree(_Gs[i]))*_Gs[i], _Ls[i]) : i in [1..#_Ls] ];
end function;
