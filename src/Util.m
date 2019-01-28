/* 
    Copyright 2019 Joshua Maglione.
    Distributed under MIT License.
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



// Returns the lattice of X from the relation f. 
// (X: Seq[A], U: A, f: (A, A) => Boolean): Seq[Tup[A, Set[Int]]]
// U should have the property that for all x in X, f(x, U).
// f should have the property f(x, y) <=> x < y.
// The algorithm returns a lattice in O(|X|^2) time. 
__GenerateLattice := function(X, U, f) 
  L := [<U, {IntegerRing() | }>];
  for x in X do 

    // sift down
    nodes_above := {1};
    nodes_below := {};
    nodes_test := [<1, L[1][2]>];

    while #nodes_test gt 0 do

      for node in nodes_test[1][2] do

        if f(x, L[node][1]) then
          Exclude(~nodes_above, nodes_test[1][1]);
          Include(~nodes_above, node);
          Append(~nodes_test, <node, L[node][2]>);
        elif f(L[node][1], x) then
          Include(~nodes_below, node);
        else
          Append(~nodes_test, <node, L[node][2]>);
        end if;

      end for;

      nodes_test := nodes_test[2..#nodes_test];

    end while;

    // place node
    Append(~L, <x, nodes_below>);
    for node in nodes_above do
      S := L[node][2];
      T := S join {#L};
      L[node][2] := T;
    end for;
    
    // clean up
    for node in nodes_above do
      S := L[node][2];
      T := S diff nodes_below;
      L[node][2] := T;
    end for;

  end for;
    
  return L;
end function;
