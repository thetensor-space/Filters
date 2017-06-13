/* 
    Copyright 2016, 2017, Joshua Maglione.
    Distributed under GNU GPLv3.
*/


import "FilterDefs.m" : __GetFilter;
import "Util.m" : __MySort;

__GenerateFilter := function( Im, MaxInds, PO : LexOrder := false )
  d := #MaxInds[1];
  // Set up dynamic lists. Orders for groups are automatically stored in Magma.
  // In this context, two groups are the same if and only if their orders are the same.
  Grps := Im;
  Inds := MaxInds;
  check := [ [ 0 : i in [1..#Grps] ] : j in [1..#Grps] ];

  // Take a shortcut that assumes that every index ending in 0 came from a filter.
  // This might possibly cause an error in a weird situation, but I cannot see how yet...
  oldInds := [ i : i in [1..#Inds] | Inds[i][d] eq 0 ];
  for i in oldInds do
    for j in oldInds do
      check[i][j] := 1;
    end for;
  end for;

  while check ne [ [ 1 : i in [1..#check] ] : j in [1..#check] ] do
    assert exists(k){ k : k in [1..#check] | 0 in &cat[ c[1..k] : c in check[1..k] ] }; 
    assert exists(entry){ [i,j] : j in [i..k], i in [1..k] | check[i][j] eq 0 };
//    assert exists(entry){ [i,j] : j in [i..#check], i in [1..#check] | check[i][j] eq 0 };
    s := Inds[entry[1]];
    t := Inds[entry[2]];
    u := [ s[i] + t[i] : i in [1..#s] ];
    x := __MySort( Inds, u, PO );
    updated := false;
    check[entry[1]][entry[2]] := 1;
    check[entry[2]][entry[1]] := 1;

    if x le #Inds then
      C := sub< Im[1] | CommutatorSubgroup( Grps[entry[1]], Grps[entry[2]] ), Grps[x] >;
      
      // If u in already in Inds, then we do not need to add an additional entry in Inds/Grps.
      // We check to see if Grps[x] is the same as C. If it is, then we do nothing; 
      // otherwise, we update the group and reset the rows and columns of the check matrix.
      if (Inds[x] eq u) and (#C ne #Grps[x]) then
        Grps[x] := C;
        for i in [1..#check] do
          check[i][x] := 0;
        end for;
        check[x] := [ 0 : i in [1..#check] ];
        updated := true;
      end if;

      // If u is not in Inds, then we need to insert into both Inds and Grps.
      if Inds[x] ne u then
        Insert(~Grps,x,C);
        Insert(~Inds,x,u);
        check := [ Insert(c,x,0) : c in check ];
        Insert(~check,x,[0 : i in [1..#check[1]]]);
        updated := true;
      end if;
    end if;

    // Check to see if we updated something in our lists.
    // If so, we need to update the groups above the updated group, and possibly merge entries.
    if updated then
      incomplete := true;
      i := x-1;
      
      // First we make sure the list of groups is decreasing.
      while incomplete do
        H := sub< Im[1] | C, Grps[i] >;
        if #H ne #Grps[i] then
          Grps[i] := H;
          for j in [1..#check] do
            check[j][i] := 0;
          end for;
          check[i] := [ 0 : j in [1..#check] ];
        else
          incomplete := false;
        end if;
        i -:= 1;
      end while;

      // Now we merge entries where the groups are the same.
      ords := {* #G : G in Grps *};
      while exists(o){ o : o in ords | Multiplicity(ords,o) gt 1 } do
        seq := [ #G : G in Grps ];
        i := Index(seq,o);
        for j in Reverse([i..i+Multiplicity(ords,o)-2]) do
          Remove(~Grps,j);
          Remove(~Inds,j);
          Remove(~check,j);
          check := [ Remove(c,j) : c in check ];
        end for;
        ords := {* #G : G in Grps *};       
      end while;
    end if;

  end while;

  // Make filter
  return __GetFilter( Im[1], Inds, Grps, PO : TotallyOrdered := true, Lex := LexOrder );
end function;

__ConstructFilter := function( F, H )
  G := F`Object;
  Im := Image(F);
  i := 1;
  repeat
    i +:= 1;
    K := sub< G | H, Im[i] >;
  until ((#K ne #Im[i]) and (#K ne #Im[i-1]) and forall{ k : k in Generators(K) | k in Im[i-1]}) or (i eq #Im);
  if i eq #Im then
    "Could not place into filter";
    return F;
  end if;
  M := MaximalIndices(F);
  index := M[i-1] cat [1];

  PO := function(x,y)
    j := 1;
    while j le #x do
      if x[j] lt y[j] then
        return true;
      elif x[j] gt y[j] then
        return false;
      end if;
      j +:= 1;
    end while;
    return true;
  end function;   
  return GenerateFilter( F, K, index, PO : Lex := true );
end function;

// Intrinsics  --------------------------------------------------------------------------

intrinsic GenerateFilter( F::Flt, H::Grp, i::SeqEnum, P::UserProgram : Lex := false ) -> Flt
{Returns the totally ordered filter generated by F and H.
We assume the maximal index for H is i.
The preorder is defined by P, where P(x,y) returns true if x `le' y.
If P is the lexicographical order set Lex to true.}
  require Type(Lex) eq BoolElt : "Parameter must be true/false.";
  require F`Totally_Ordered : "Filter must be totally ordered.";
  require forall{ h : h in Generators(H) | h in F`Object } : "Cannot find covering group.";
  require #(F`Indices[1])+1 eq #i : "Length of index not expected size.";
  
  Inds := [ Append(ind,0) : ind in F`Indices ];
  pos := __MySort( Inds, i, P );
  Insert( ~Inds, pos, i );
  Im := Insert( F`Image, pos, H );
  return __GenerateFilter( Im, Inds, P : LexOrder := Lex );
end intrinsic;


intrinsic GenerateFilter( F::Flt, S::SeqEnum, I::SeqEnum, P::UserProgram : Lex := false ) -> Flt
{Returns the totally ordered filter generated by F and S.
We assume that I is the sequence of maximal indices for S.
The preorder is defined by P, where P(x,y) returns true if x `le' y.
If P is the lexicographical order set Lex to true.}
  require Type(Lex) eq BoolElt : "Parameter must be true/false.";
  require F`Totally_Ordered : "Filter must be totally ordered.";
  require forall{ i : i in [1..#S] | forall{ h : h in Generators(S[i]) | h in F`Object } } : "Cannot find covering group.";
  require #(F`Indices[1])+1 eq #I[1] : "Length of index not expected size.";
  require #Set(I) eq #I : "Must have distinct indices.";

  Inds := [ Append(ind,0) : ind in F`Indices ]; 
  for i in [1..#I] do
    pos := __MySort( Inds, I[i], P );
    Insert( ~Inds, pos, I[i] );
    Im := Insert( F`Image, pos, S[i] );
  end for;
  return __GenerateFilter( Im, Inds, P : LexOrder := Lex);
end intrinsic;

// Created during March 28 -- April 7 2016 in response to Eamonn and Pete's visit to CSU
intrinsic ConstructFilter( F::Flt, X::[GrpElt] ) -> Flt
{Given a filter and a sequence of generators for a subgroup, construct a new filter by including <X> in the chain of subgroups.}
  G := F`Object;
  require ElementType(G) eq Type(X[1]) : "Unexpected element type.";
  require forall{ x : x in X | x in G } : "Generators must be contained in the group.";
  require F`Totally_Ordered : "Filter must be totally ordered.";
  require F`Max_Inds : "Subgroups in filter must have maximal indices.";
  H := sub< G | X >;
  if Type(H) eq GrpMat then
    require LMGIsNormal(G,H) : "Subgroup must be normal.";
  else
    require IsNormal(G,H) : "Subgroup must be normal.";
  end if;
  return __ConstructFilter( F, H );
end intrinsic;

// Created during March 28 -- April 7 2016 in response to Eamonn and Pete's visit to CSU
intrinsic ConstructFilter( F::Flt, H::Grp ) -> Flt
{Given a filter and a subgroup H, construct a new filter by including H in the chain of subgroups.}
  G := F`Object;
  require Type(H) eq Type(G) : "Unexpected group type.";
  require forall{ x : x in Generators(H) | x in G } : "Generators must be contained in the group.";
  if Type(H) eq GrpMat then
    require LMGIsNormal(G,H) : "Subgroup must be normal.";
  else
    require IsNormal(G,H) : "Subgroup must be normal.";
  end if;
  require F`Totally_Ordered : "Filter must be totally ordered.";
  require F`Max_Inds : "Subgroups in filter must have maximal indices.";
  return __ConstructFilter( F, H );
end intrinsic;
