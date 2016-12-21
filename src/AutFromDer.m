__MatToAut := function( G, M, phi )
  ord := FactoredOrder(G);
  p := ord[1][1];
  e := ord[1][2];
  T := Matrix([Eltseq(G.i @ phi) : i in [1..e]]);
  N := T*M*T^-1;
  im := [ < G.i, &*[ G.j^(Integers()!N[i][j]) : j in [1..e] ] > : i in [1..e] ];
  if not IsHomomorphism(G,G,im) then
    return false,_;
  end if; 
  return true,hom< G -> G | im >;
end function;

__AutToMat := function( G, a, phi )
  ord := FactoredOrder(G);
  p := ord[1][1];
  e := ord[1][2];
  M := [ Eltseq(G.i @ a) : i in [1..e] ];
  T := Matrix([Eltseq(G.i @ phi) : i in [1..e]]);
  return GL(e,p)!(T^-1*Matrix(GF(p),e,e,M)*T);
end function;

__E := function(MS,i,j)
  n := Nrows(MS.1);
  m := Ncols(MS.1);
  return MS.(m*(i-1)+j);
end function;

// The Lie subring inside the graded derivation ring.
__PartialDNaught := function( F ) 
  L := LieAlgebra(F);
  GD := GradedDerivationAlgebra(L);
  K := BaseRing(GD);
  n := Nrows(GD.1);
  MS := KMatrixSpace(K,n,n);
  V := sub< MS | [ Matrix(X) : X in Basis(GD) ] >;
  E := [];
  pos := 1;
  H := L`GradedInfo`HomogeneousComponents;
  for h in H do
    Append(~E,InsertBlock(ZeroMatrix(K,n,n),IdentityMatrix(K,Dimension(h)),pos,pos));
    pos +:= Dimension(h);
  end for;
  U := sub< MS | Basis(GradedDerivationAlgebra(LieAlgebra(F))) >;
  assert [ &+[ e*V.i*e : e in E ] : i in [1..Dimension(V)] ] subset U;
  eta := hom< V -> U | [<V.i,&+[ e*V.i*e : e in E ]> : i in [1..Dimension(V)]] >;
  return Kernel(eta);
end function;

// PO a total order where PO(a,b) returns true if a <= b.
__GetMax := function( PO, S )
  assert exists(max){ x : x in S | forall{ y : y in S | PO(y,x) } };
  return max;
end function;

__GetMin := function( PO, S )
  assert exists(min){ x : x in S | forall{ y : y in S | PO(x,y) } };
  return min;
end function;

Get_s := function( F, d )
  L := LieAlgebra(F);
  bas := Basis(L);
  inds := L`GradedInfo`HomogeneousIndices;
  ord_bas := [];
  projs := L`GradedInfo`Projections;
  for pi in projs do
    hom_comp := [];
    for v in bas do
      im := v @ pi;
      if im ne Parent(im)!0 then
        Append(~hom_comp,v);
      end if;
    end for;
    Append(~ord_bas,hom_comp);
  end for;
  V := VectorSpace(BaseRing(L), Dimension(L));
  hom_comps := [* VectorSpaceWithBasis( [ V!b : b in B ] ) : B in ord_bas *];
  
  min := [];
  for i in [1..#ord_bas] do
    B := ord_bas[i];
    for v in B do
      which_b := [ j : j in [1..Dimension(L)] | Coordinates(L,v*d)[j] ne 0 ];
      indices := [];
      for x in which_b do
        assert exists(j){ j : j in [1..#ord_bas] | L.x in ord_bas[j] };
        Append(~indices, inds[j]);
      end for;
      if #indices ne 0 then
        assert exists(k){ k : k in indices | forall{ l : l in indices | F`Preorder(k,l) } };
        dif := [ Maximum([k[l] - inds[i][l],0]) : l in [1..#k] ];
        Append(~min,dif);
      end if;
    end for;
  end for;

  assert exists(s){ s : s in min | forall{ t : t in min | F`Preorder(s,t) } };

  // SANITY
  for i in [1..#ord_bas] do
    B := ord_bas[i];
    for v in B do
      guess := [ inds[i][l] + s[l] : l in [1..#s] ]; 
      smaller_inds := [ t : t in [1..#inds] | F`Preorder(inds[t],guess) ];
      assert exists(max){ x : x in Reverse(smaller_inds) | forall{ y : y in smaller_inds | F`Preorder(inds[y],inds[x]) } };
      Remove(~smaller_inds,Index(smaller_inds,max));
      if not forall{ t : t in smaller_inds | (L!(v*d)) @ projs[t] eq L`GradedInfo`HomogeneousComponents[t]!0 } then
        "Think s=",s;
      end if;
    end for;
  end for;

  return s;
end function;

GetSmallerPD0 := function(F)
  G := F`Object;
  BF := BoundaryFilter(F);
  PD0 := PartialDNaught(F);
  FP, pi := FPGroup(F`Object);
  L := LieAlgebra(F);
  phi := F`Lie_Func;
  assert forall{ i : i in [1..Ngens(FP)] | FP.i @ pi eq F`Object.i };
  R := Relations(FP);
  R := [ r[2]^-1*r[1] : r in R ];
  R := [ R[1..Ngens(FP)], R[Ngens(FP)+1..#R] ];
  bas := [];
  im := [];
  for i in [1..Ngens(FP)] do
    assert exists(n){ n : n in F`Indices | (G.i in (n @ F)) and (G.i notin (n @ BF)) };
    Append(~im,n);
  end for;
  omega := map< {1..Ngens(FP)} -> F`Indices | [<i,im[i]> : i in [1..Ngens(FP)]] >;
  for d in Basis(PD0) do
    Index(Basis(PD0),d);
    s := Get_s(F,d);
    ep := hom< FP -> FP | [ <FP.i, FP.i*((((FP.i@pi)@phi)*d)@@phi)@@pi> : i in [1..Ngens(FP)] ] >;
    if not forall{ i : i in [1..Ngens(FP)] | G.i^-1 * (FP.i @ ep @ pi) in Center(G) } then
      R_ep_pi := [ (r @ ep) @ pi : r in R[2] ];
      i := 2;
      j := 1;
      k := 1;
      holds := true;
      while (not holds) or (i le Ngens(FP)) do
        index := [ omega(i)[l] + omega(j)[l] + s[l] : l in [1..#s] ];
        holds := R_ep_pi[k] in (index @ BF);

        if j eq i-1 then
          i +:= 1;
          j := 1;
        else
          j +:= 1;
        end if;
        k +:= 1;
      end while;

      if holds then
        Append(~bas,d);
      else
        "Dropped one";
      end if;
    else
      Append(~bas,d);
    end if;
  end for;
  return sub< PD0 | bas >;
end function;

__CentralAutos := function( G, A )
  T := pCentralTensor(G);
  K := BaseRing(T);
  p := Characteristic(K);
  d := Dimension(T`Domain[1]);
  e := Dimension(T`Codomain);
  MS := KMatrixSpace( GF(p), d+e, d+e );
  M := GL(d+e,p);
  I := MS!(M!1);
  cents := [];
  for i in [1..e] do
    for j in [1..d] do
      k := (j-1)*(d+e) + i+d;
      Append(~cents, M!(I+MS.k));
    end for;
  end for;
  C := sub< M | cents >;
  Aut := sub< M | cents, A >;
  _ := LMGOrder(Aut);
  repeat
    gens := [Random(C) : i in [1..2] ];
    S := sub< Aut | gens, A >;
  until LMGOrder(S) eq #Aut;
  return gens;
end function;

intrinsic PartialDeltaNaught( F::Flt ) -> GrpAut
{Returns the automorphism group of the group G = 0 @ F.}
  G := F`Object;
  p := Characteristic(BaseRing(LieAlgebra(F)));
  require pClass(G) eq 2 : "Only working for p-class 2 exponent p groups.";
  require IsPrime(Exponent(G)) : "Only working for p-class 2 exponent p groups.";
  A := AutomorphismGroupByInvariants(G);
  C := __CentralAutos(G, A);
  Aut := sub< Generic(A) | A, C >;
  _ := LMGOrder( Aut );
  GD,X,Y := MGradedDerivationAlgebra(F);
  MS := KMatrixSpace(GF(p), Degree(Aut), Degree(Aut));
  I := MS!(Aut!1);

  Fit, FitPC, phi := LMGFittingSubgroup(Aut);
  T := MS!Matrix([Eltseq(G.i @ F`Lie_Func) : i in [1..NPCgens(G)]]);
  gens := [ T^-1*(MS!(FitPC.i @@ phi))*T - I : i in [1..NPCgens(FitPC)] ];
  domain := [ d : d in gens | IsCoercible(GD,d) ];
  der := sub< MS | domain >;
  return der;
end intrinsic;

intrinsic MGradedDerivationAlgebra( F::Flt ) -> AlgMatLie, SeqEnum, SeqEnum
{Returns the M-graded derivation algebra as a direct sum of matrix Lie algebras.}
  if assigned F`Lie_Alg and assigned F`Lie_Alg`GradedInfo`GradedDerivationAlgebra`Indices then
    return F`Lie_Alg`GradedInfo`GradedDerivationAlgebra`DerivationAlgebra, 
           F`Lie_Alg`GradedInfo`GradedDerivationAlgebra`DirectSum,
           F`Lie_Alg`GradedInfo`GradedDerivationAlgebra`Indices;
  end if;
  L := LieAlgebra(F);
  projs := L`GradedInfo`Projections;
  indices := L`GradedInfo`HomogeneousIndices;
  hom_comps := L`GradedInfo`HomogeneousComponents;
  GD := GradedDerivationAlgebra(L);
  B := Basis(GD);
  ord_bas := [];
  ind := [];
  for d in B do
    potential_s := [];
    for i in [1..Nrows(d)] do
      v := d[i];
      temp_inds := [ indices[j] : j in [1..#indices] | v @ projs[j] ne hom_comps[j]!0 ];
      if not exists(min){ x : x in temp_inds | forall{ y : y in temp_inds | F`Preorder(x,y) } } then
        min := F`Indices[#F`Indices];
      end if;
      assert exists(i_ind){ indices[x] : x in [1..#indices] | L.i @ projs[x] ne hom_comps[x]!0 };
      Append(~potential_s, [ Maximum(min[k] - i_ind[k],0) : k in [1..#min] ]);
    end for;
    s := __GetMin( F`Preorder, potential_s );
    if s in ind then
      s_ind := Index(ind,s);
      Append(~ord_bas[s_ind],d);
    else
      Append(~ind,s);
      Append(~ord_bas,[d]);
    end if;
  end for;
  MS := KMatrixSpace(BaseRing(L),Dimension(L),Dimension(L));
  direct_sum := [* sub< MS | [ MS!x : x in b ] > : b in ord_bas *];

  L`GradedInfo`GradedDerivationAlgebra`DerivationAlgebra := GD;
  L`GradedInfo`GradedDerivationAlgebra`DirectSum := direct_sum;
  L`GradedInfo`GradedDerivationAlgebra`Indices := ind;
  return GD, direct_sum, ind;
end intrinsic;

intrinsic PartialDNaught( F::Flt ) -> AlgMatLie
{Returns the Lie subalgebra partial D_0.}
  GD,X,Y := MGradedDerivationAlgebra(F);
  PD0 := __PartialDNaught(F);
  inds := [ i : i in [1..#Y] | Y[i] ne [ 0 : j in [1..#Y[1]] ] ]; // (seq) indices of all nonzero indices.
  boundary := &cat[ Basis(X[x]) : x in inds ];
  assert forall{ b : b in boundary | IsCoercible(PD0,b) and PD0!b in PD0 };
  return PD0;
end intrinsic;

intrinsic GetInducedDegree( F::Flt, d::AlgMatLieElt ) -> SeqEnum
{Returns the degree of the derivation.}
  GD,X,Y := MGradedDerivationAlgebra(F);
  require d in GD : "Not a graded derivation.";
  if Parent(d)!0 eq d then
    return F`Indices[#F`Indices];
  end if;
  B := Basis(GD);
  C := Coordinates(GD,d);
  I := [ i : i in [1..#C] | C[i] ne 0 ];
  inds := {};
  for b in B[I] do
    assert exists(i){ i : i in [1..#X] | Matrix(b) in X[i] };
    Include(~inds, Y[i]);
  end for;
  return __GetMin(F`Preorder, inds);
end intrinsic;

intrinsic GetInducedDegree( F::Flt, d::Mtrx ) -> SeqEnum
{Returns the degree of the derivation.}
  GD,X,Y := MGradedDerivationAlgebra(F);
  require IsCoercible(GD,d) and (GD!d) in GD : "Not a graded derivation.";
  if Parent(d)!0 eq d then
    return F`Indices[#F`Indices];
  end if;
  d := GD!d;
  B := Basis(GD);
  C := Coordinates(GD,d);
  I := [ i : i in [1..#C] | C[i] ne 0 ];
  inds := {};
  for b in B[I] do
    assert exists(i){ i : i in [1..#X] | Matrix(b) in X[i] };
    Include(~inds, Y[i]);
  end for;
  return __GetMin(F`Preorder, inds);
end intrinsic;

__NormalForm := function( F, s )
  return &*[ F.i^(Integers()!s[i]) : i in [1..#s] ];
end function;

intrinsic FirstApproximation( F::Flt ) -> AlgMatLie
{Returns the first approximation of L(Delta F).}
  GD,X,Y := MGradedDerivationAlgebra(F);
  G := F`Object;
  BF := BoundaryFilter(F);
  pcgs := ExhibitingPCGS(F);
  n := #pcgs;
  p := Characteristic(BaseRing(GD));
  Fn := FreeGroup(n);
  FP, pi := FPGroup(G);
  alpha := hom< Fn -> FP | [<Fn.i, pcgs[i] @@ pi> : i in [1..n] ] >;
  comms := [ ((pcgs[j],pcgs[i]) @@ (alpha*pi))*(Fn.i,Fn.j) : i in [j+1..n], j in [1..n-1] ];
  powers := [ ((pcgs[k]^p) @@ (alpha*pi))*Fn.k^p : k in [1..n] ];
  assert forall{ r : r in comms | r @ (alpha*pi) eq G!1 };
  assert forall{ r : r in powers | r @ (alpha*pi) eq G!1 };
  L := LieAlgebra(F);
  PD0 := PartialDNaught(F);
  phi := F`Lie_Func;
  im := [];
  for i in [1..n] do
    assert exists(x){ x : x in F`Indices | (pcgs[i] in (x @ F)) and (pcgs[i] notin (x @ BF)) };
    Append(~im,x);
  end for;
  omega := map< {1..n} -> F`Indices | [<i,im[i]> : i in [1..n]] >;

  bas := [];
  for d in Basis(PD0) do
    s := GetInducedDegree(F,d);
    ep := hom< Fn -> Fn | [ <Fn.i, Fn.i*((L.i*d) @@ (alpha*pi*phi))> : i in [1..n] ] >;
    R_ep_pi := [ (r @ ep) @ (alpha*pi) : r in comms ];
    k := 1;
    holds := true;
    while holds and (k le #comms) do
      ji := Reverse(Eltseq(comms[k]))[1..2];
      j := ji[1];
      i := ji[2];
      index := [ omega(i)[l] + omega(j)[l] + s[l] : l in [1..#s] ];
      holds := R_ep_pi[k] in (index @ BF);
      k +:= 1;
    end while;
    if holds then
      Append(~bas,d);
    else
      "Dropped", Index(Basis(PD0),d);
    end if;
  end for;

  Approx := sub< PD0 | bas >;

  Q := sub< PD0 | [ b : b in Basis(PD0) | b notin Approx ] >;
  extra := [];
  for d in Q do
    s := GetInducedDegree(F,d);
    ep := hom< Fn -> Fn | [ <Fn.i, Fn.i*((L.i*d) @@ (alpha*pi*phi))> : i in [1..n] ] >;
    R_ep_pi := [ (r @ ep) @ (alpha*pi) : r in comms ];
    k := 1;
    holds := true;
    while holds and (k le #comms) do
      ji := Reverse(Eltseq(comms[k]))[1..2];
      j := ji[1];
      i := ji[2];
      index := [ omega(i)[l] + omega(j)[l] + s[l] : l in [1..#s] ];
      holds := R_ep_pi[k] in (index @ BF);
      k +:= 1;
    end while;
    if holds then
      Append(~extra,d);
    end if;
  end for;
  
  Approx2 := sub< PD0 | bas, extra >;
  return Approx2;
end intrinsic;

intrinsic ExhibitingPCGS( F::Flt ) -> SeqEnum
{Returns a pcgs that fully exhibits F.}
  L := LieAlgebra(F);
  return [ L.i @@ F`Lie_Func : i in [1..Dimension(L)] ];
end intrinsic;
