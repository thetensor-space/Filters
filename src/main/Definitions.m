/* 
    Copyright 2019 Joshua Maglione.
    Distributed under GNU GPLv3.
*/


/*
    Filters
*/
declare type Flt;
declare attributes Flt : Boundary, Domain, Image, Indices, Map, Lattice, Length, 
  LieAlg, LieFunc, Object, Preorder, TotallyOrdered;

/* 
  Description of attributes:
    Boundary . . . . . . . The filter's boundary filter.
    Domain . . . . . . . . A sequence of cyclic commutative monoids.
    Image. . . . . . . . . A sequence of algebraic objects in the image.
    Indices. . . . . . . . A sequence of indices for the image.
    Map. . . . . . . . . . The map that evaluates the filter.
    Lattice. . . . . . . . The lattice of the filter.
    Length . . . . . . . . The length of the filter.
    LieAlg . . . . . . . . The associated Lie algebra.
    LieFunc. . . . . . . . The associated functor to the Lie algebra.
    Object . . . . . . . . The algebraic object for which this is a filter for.
    Preorder . . . . . . . A user defined function for N^d. It acts like `less than or equal to'.
    TotallyOrdered . . . . True/false depending if the ordering is totally ordered.
*/



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
