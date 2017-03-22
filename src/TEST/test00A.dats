#include
"share/atspre_staload.hats"
//
staload "libats/SATS/funset_avltree.sats"
staload _(*anon*) = "libats/DATS/funset_avltree.dats"
//

staload "libats/SATS/funmap_avltree.sats"
staload
_(*anon*) = "libats/DATS/funmap_avltree.dats"
//
staload "./../SATS/grm.sats"
staload _ = "./../DATS/grm.dats"
//
staload "./../SATS/grmfuncs.sats"
staload _ = "./../DATS/grmfuncs.dats"
//
#include "./test00.hats"
//
dynload "./../utils/DATS/fundigraph.dats"
dynload "./../DATS/grm.dats"
//
(* ****** ****** *)
//
implement
main0 () = let
//
val () = fprintln!(stdout_ref, "BEGIN of test00_A")
//
// setup a simple grammar
var gr = Grammar_make_nil ()
val _sS' = Grammar_add_nonterminal(gr, "S'")
val _sS = Grammar_add_nonterminal(gr, "S")
val _sL = Grammar_add_nonterminal(gr, "L")
val _sR = Grammar_add_nonterminal(gr, "R")
val _sSTAR = Grammar_add_terminal(gr, "*")
val _sEQUALS = Grammar_add_terminal(gr, "=")
val _sID = Grammar_add_terminal(gr, "id")

val st = Grammar_add_production (gr, _sS', $list{Symbol}(_sS, sym_EOF))
val _ = Grammar_add_production (gr, _sS, $list{Symbol}(_sL, _sEQUALS, _sR))
val _ = Grammar_add_production (gr, _sS, $list{Symbol}(_sR))
val _ = Grammar_add_production (gr, _sL, $list{Symbol}(_sSTAR, _sR))
val _ = Grammar_add_production (gr, _sL, $list{Symbol}(_sID))
val _ = Grammar_add_production (gr, _sR, $list{Symbol}(_sL))
//
val () = Grammar_set_start (gr, st)
//
in
//
test00_fun (gr);
//
fprintln!(stdout_ref, "END of test00_A")
//
end // end of [test00_A]
