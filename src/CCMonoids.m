/* 
    Copyright 2019 Joshua Maglione.
    Distributed under MIT License.
*/



// =============================================================================
//                         Cyclic Commutative Monoid Type
// =============================================================================

/*
    Cyclic commutative monoids
*/
declare type CCMon[CCMonElt];
declare attributes CCMon : Index, Period;

/*
  Description of attributes:
    If Index < 0, then CCMon == N. Otherwise, CCMon == N/~, where
              { i = j                i, j < Index,
      i ~ j = { 
              { i = j (mod Period)   i, j >= Index.
*/

declare attributes CCMonElt : Element, Parent;

/*
  Description of attributes:
    Element. . . . . . . . The corresponding integer.
    Parent . . . . . . . . The parent CCMon.
*/

// =============================================================================
//                     Cyclic Commutative Monoid Constructors
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

