/* 
    Copyright 2019 Joshua Maglione.
    Distributed under GNU GPLv3.
*/



// Returns all maximal elements of the monoid less than s.
// (s: Seq[Int]): Seq[Seq[Int]]
__NextIncre := function(s)
  d := #s;
  next := [];
  for i in [1..d] do
    t := s;
    t[i] +:= 1;
    Append(~next, t);
  end for;
  return next;
end function;


/*
  Not stack-safe, but I don't expect beyond 100 recursions. 

  Populates the lattice L with the entries from X based on the relation f. 
*/
__PopulateLatice := function(L, X, f)
  if #X eq 0 then return L; end if;

  // Runs through L and builds up nL. Tests against x, using f, and builds up
  // connections in s. 
  RunThru := function(L, nL, x, s, f)
    // end recursion
    if #L eq 0 then return nL, s; end if;

    t := L[1];
    if f(t[1], x) then      // t[1] < x, update s
      new_s := s cat [#nL + 1];
      Lat := nL cat [t];
    elif f(x, t[1]) then    // x < t[1], update L
      new_s := s;
      Lat := nL cat [<t[1], t[2] cat [#L + #nL + 1]>];
    else                    // x || t[1], do nothing
      new_s := s;
      Lat := nL cat [t];
    end if;
  
    return $$(L[2..#L], Lat, x, new_s, f);
  end function;

  nL, s := RunThru(L, [], X[1], [], f);
  Lat := nL cat [<X[1], s>];
  
  return $$(Lat, X[2..#X], f);
end function;

/*
  Not correct! Not really needed!

__ReorganizeLattice := function(L)
  my_cmp := func<x, y|#y[2] - #x[2]>;
  Lat, perm := Sort(L, my_cmp);
  return Lat;
end function;
*/

// Turn the lattice into a digraph and run a spanning tree algorithm.
__TrimLattice := function(L)
  D := Digraph< {1..#L} | [<i, Set(L[i][2])> : i in [1..#L]] >;
end function;


// Returns the lattice of X from the relation f. 
// (X: Seq[A], f: (A, A) => Boolean): Seq[Tup[A, Seq[Int]]]
// f should have the property f(x, y) <=> x < y.
__GenerateLattice := function(X, f) 
  
end function;
