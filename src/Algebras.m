/* 
    Copyright 2019 Joshua Maglione.
    Distributed under MIT License.
*/




declare attributes Alg : FiltrationInfo;
FiltrationInfo_RF := recformat< BimapIndices : SeqEnum, Bimaps : List, 
  HomoComps : List, Indices : SeqEnum, Projs : List >;

/*
  Description of attributes:
    FiltrationInfo . . . . The record of the filter information.

  FiltrationInfo_RF:
    BimapIndices . . . . . The corresponding sequence (to Bimaps) of the indices
                           of the homogeneous components in the domain. 
    Bimaps . . . . . . . . The list of bimaps from the grading (TenSpcElt).
    HomoComps. . . . . . . }
    Indices. . . . . . . . } Not yet sure I need these...
    Projs. . . . . . . . . }
*/
