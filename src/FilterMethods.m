/* 
    Copyright 2019 Joshua Maglione.
    Distributed under MIT License.
*/



import "Constructors.m" : __GetFilter;
import "Util.m" : __NextIncre;

// =============================================================================
//                                    Filters                                 
// =============================================================================
intrinsic Print( F::Flt ) 
{Print F.}
  d := #F`Domain;
  str_obj := Sprintf( "%o.", Type(F`Object) );
  if ISA(Type(F`Object), Grp) then
    str := "normal subgroups of " cat str_obj;
  elif ISA(Type(F`Object), Alg) then
    str := "ideals of " cat str_obj;
  else
    str := "subsets of " cat str_obj;
  end if;

  // We suppress the finiteness of the domain in the print statement.
	if d eq 1 then
		printf "Filter from N into the " cat str;
	else;
		printf "Filter from N^" cat IntegerToString(d) cat " into the " cat str;
	end if;
end intrinsic;

intrinsic Domain( F::Flt ) -> SeqEnum[CCMon]
{Returns a sequence of commutative cyclic monoids.}
  return F`Domain;
end intrinsic;

intrinsic IsFinite( F::Flt ) -> BoolElt
{Decides if the domain of F is finite.}
  return forall{X : X in Domain(F) | IsFinite(X)};
end intrinsic;

/*
  Eventually build a dynamic table so we don't have to continue computing 
  s @ F, but maybe this is fine.
*/
intrinsic '@'( s::Tup, F::Flt ) -> .
{Returns s @ F.}
  try
    x := Domain(F)!s;
  catch err
    error "Element is not in the domain of the filter.";
  end try;
  return x @ (F`Map);
end intrinsic;

intrinsic '@'( s::SeqEnum, F::Flt ) -> .
{Returns s @ F.}
  t := <x : x in s>;
  return t @ F;
end intrinsic;

intrinsic '@'( s::RngIntElt, F::Flt ) -> .
{Returns s @ F.}
  return <s> @ F;
end intrinsic;

intrinsic Image( F::Flt ) -> SeqEnum 
{Returns every subobject in the image of the finite filter F.}
  require IsFinite(F) : "Filter must be finite.";
  CP := CartesianProduct(<Set(X) : X in Domain(F)>);
  return {s @ F : s in CP};
end intrinsic;

intrinsic Object( F::Flt ) -> .
{Returns the object of the filter F.}
  return F`Object;
end intrinsic;

intrinsic Preorder( F::Flt ) -> UserProgram
{Returns the function, P, for the pre-order of the filter F. If x and y are in 
the domain of F, then P(x, y) returns true if x is less than or equal to y.}
  return F`Preorder;
end intrinsic;

intrinsic BoundaryFilter( F::Flt ) -> Flt
{Returns the boundary filter of F.}
  if assigned F`Boundary then
    return F`Boundary;
  end if;

  filt_eval := function(x) 
    return sub< Generic(Object(F)) | [s @ F : s in __NextIncre(x)] >;
  end function;

  BF := __GetFilter(Domain(F), filt_eval, Object(F), Preorder(F) : 
    TO := F`TotallyOrdered);
  F`Boundary := BF;

  return BF;
end intrinsic;




