/* 
    Copyright 2019 Joshua Maglione.
    Distributed under GNU GPLv3.
*/



// =============================================================================
//                                    Filters
// =============================================================================
/*
  A filter constructor:
    M . . . The domain as a seqeunce of CCMon.
    Im. . . The sequence of subobjects in the image.
    Inds. . The sequence of indices corresponding the image.
    Map . . The function used to evaluate the filter.
    PO. . . The function used to determine the pre-order.

    TO. . . The boolean that states whether the filter is known to be totally
            ordered or not. 
*/
__GetFilter := function(M, Map, X, PO : TO := false)
  F := New(Flt);
  F`Domain := M;
  F`Map := Map;
  F`Object := X;
  F`Preorder := PO;
  F`TotallyOrdered := TO;
  return F;
end function;

// -----------------------------------------------------------------------------
//                                   Black-box
// -----------------------------------------------------------------------------

// LATER

// -----------------------------------------------------------------------------
//                                     Groups
// -----------------------------------------------------------------------------

intrinsic pCentralFilter( G::Grp, p::RngIntElt ) -> Flt
{Constructs the filter from the p-central series of G on the finite commutative 
cyclic monoid C(c, 1), where G has p-class c.}
  require Type(G) in {GrpMat, GrpPC, GrpPerm} : 
    "Cannot construct p-central series.";
  S := pCentralSeries(G, p);
  Dom := [CommutativeCyclicMonoid(#S, 1)];

  filt_eval := function(x)
    if x[1] eq 0 then
      return S[1];
    else
      return S[Integer(Dom[1]!(x[1]))];
    end if;
  end function;

  PO := function(s, t)
    return Integer(s) le Integer(t);
  end function;

  return __GetFilter(Dom, filt_eval, G, PO : TO := true);
end intrinsic;

intrinsic pCentralFilter( G::Grp ) -> Flt
{Constructs the filter from the p-central series of the p-group G on the finite 
commutative cyclic monoid C(c, 1), where G has p-class c.}
  if Type(G) eq GrpMat and not assigned G`Order then
    ord := LMGOrder(G);
  else
    ord := #G;
  end if;
  fac := Factorization(ord);
  require #fac eq 1 : "Group must be of prime-power order.";
  return pCentralFilter(G, fac[1][1]);
end intrinsic;

// =============================================================================
//                                  C.C. Monoids
// =============================================================================
__GetMonoid := function(ind, per)
  M := New(CCMon);
  M`Index := ind;
  M`Period := per;
  return M;
end function;

intrinsic NonnegativeIntegers() -> CCMon
{The monoid of nonnegative integers.}
  return __GetMonoid(-1, 0);
end intrinsic;

intrinsic CommutativeCyclicMonoid( r::RngIntElt, s::RngIntElt ) -> CCMon
{Returns the commutative cyclic monoid C(r, s), where r is the index and s the 
period.}
  require s gt 0 : "Period must be positive.";
  return __GetMonoid(r, s);
end intrinsic;
