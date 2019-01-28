/* 
    Copyright 2019 Joshua Maglione.
    Distributed under MIT License.
*/



// =============================================================================
//                                  C.C. Monoids
// =============================================================================
intrinsic Print( M::CCMon )
{Print M.}
  if M`Index lt 0 then
    printf "Nonnegative integer monoid";
  else
    printf "Commutative cyclic monoid C(%o, %o) on the set %o", M`Index, 
      M`Period, {0..M`Index + M`Period - 1};
  end if;
end intrinsic;

intrinsic 'eq'( M::CCMon, N::CCMon ) -> BoolElt
{M eq N}
  return (M`Index eq N`Index) and (M`Period eq N`Period);
end intrinsic;

intrinsic IsFinite( M::CCMon ) -> BoolElt
{Decides if M is finite.}
  return M`Index ge 0;
end intrinsic;

intrinsic IsCoercible( M::CCMon, s::RngIntElt ) -> BoolElt
{Returns the representative of s in M.}
  if s lt 0 then
    return false, _;
  end if;

  m := New(CCMonElt);
  if IsFinite(M) then
    if s lt M`Index then
      m`Element := s;
    else
      m`Element := M`Index + s mod M`Period;
    end if;
  else
    m`Element := s;
  end if;

  m`Parent := M;
  return true, m;
end intrinsic;

intrinsic IsCoercible( M::CCMon, s::CCMonElt ) -> BoolElt
{Returns the representative of s in M.}
  if M eq Parent(s) then
    return true, s;
  end if;
  return false, _;
end intrinsic;

intrinsic IsCoercible( M::CCMon, x::. ) -> BoolElt
{Returns the representative of x in M.}
  try
    y := M!(Integers()!x);
  catch err
    return false, _;
  end try;
  return true, y;
end intrinsic;

intrinsic Set( M::CCMon ) -> SetEnum 
{The set of representatives of the finite monoid M in the nonnegative integer 
monoid.}
  require IsFinite(M) : "Monoid must be finite.";
  return {M!s : s in [0..M`Index + M`Period - 1]};
end intrinsic;




// =============================================================================
//                              Elts of C.C. Monoids
// =============================================================================
intrinsic Print( s::CCMonElt ) 
{Print s}
  printf "%o", s`Element;
end intrinsic;

intrinsic 'eq'( s::CCMonElt, t::CCMonElt ) -> BoolElt
{Decides if s and t are equal.}
  return s`Element eq t`Element;
end intrinsic;

intrinsic 'eq'( s::CCMonElt, t::RngIntElt ) -> BoolElt
{Decides if s and t are equal.}
  return s`Element eq t;
end intrinsic;

intrinsic 'eq'( s::RngIntElt, t::CCMonElt ) -> BoolElt
{Decides if s and t are equal.}
  return s eq t`Element;
end intrinsic;

intrinsic Parent( s::CCMonElt ) -> CCMon
{Returns the parent commutative cyclic monoid of s.}
  return s`Parent;
end intrinsic;

intrinsic Integer( s::CCMonElt ) -> RngIntElt
{Returns the integer associated to the representative s.}
  return s`Element;
end intrinsic;

intrinsic '+'( s::CCMonElt, t::CCMonElt ) -> CCMonElt
{Returns s + t.}
  require Parent(s) eq Parent(t) : "Elements come from different monoids.";
  return Parent(s)!(s`Element + t`Element);
end intrinsic;

intrinsic '+'( s::CCMonElt, t::RngIntElt ) -> CCMonElt
{Returns s + t.}
  require t ge 0 : "Integer must be nonnegative.";
  return Parent(s)!(s`Element + t);
end intrinsic;

intrinsic '+'( s::RngIntElt, t::CCMonElt ) -> CCMonElt
{Returns s + t.}
  require s ge 0 : "Integer must be nonnegative.";
  return Parent(t)!(s + t`Element);
end intrinsic;

intrinsic '*'( n::RngIntElt, s::CCMonElt ) -> CCMonElt
{Returns n*s.}
  require n ge 0 : "Integer must be nonnegative.";
  return Parent(s)!(n * s`Element);
end intrinsic;

