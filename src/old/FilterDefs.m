/* 
    Copyright 2019 Joshua Maglione.
    Distributed under GNU GPLv3.
*/



// Class of filters
declare type Flt;
declare attributes Flt : Boundary, Domain, Image, Indices, Lattice, Length, 
  Lie_Alg, Lie_Func, Map, Object, Preorder, Totally_Ordered;

/* 
  Description of attributes:
    Boundary . . . . . . . The filter's boundary filter.
    Domain . . . . . . . . An integer d, where the domain of the filter is N^d. 
    Image. . . . . . . . . A sequence of algebraic objects in the image.
    Indices. . . . . . . . A sequence of indices for the image.
    Lattice. . . . . . . . The lattice of the filter.
    Length . . . . . . . . The length of the filter.
    Lie_Alg. . . . . . . . The associated Lie algebra.
    Lie_Func . . . . . . . The associated functor to the Lie algebra.
    Map. . . . . . . . . . The map that evaluates the filter.
    Object . . . . . . . . The algebraic object for which this is a filter for.
    Preorder . . . . . . . A user defined function for N^d. It acts like `less than or equal to'.
    Totally_Ordered. . . . True/false depending if the ordering is totally ordered.
*/

