staload "./Input.sats"
staload "./Grammar.sats"
//
staload
_(*anon*) = "prelude/DATS/list.dats"
//
local
//
assume Input = List(Terminal)
//
in // in of [local]
//
implement Input_make_list (xs) = let
  implement
  list_map$fopr<string><Terminal> (i) = Symbol_make_term(i)
  val ys = list_map<string><Terminal> (xs)
  val ys = list_vt2t{Terminal} (ys)
in
  ys
end
//
implement
Input_isnot_empty (xs) = case+ xs of
| list_cons (_, _) => true
| _ => false
//
implement
Input_peek (xs) = let
  val- list_cons (x, xs) = xs
in
  x
end
//
implement
Input_pop (xs) = let
  val- list_cons (x, xs) = xs
in
  xs
end
//
end // end of [local]
//
