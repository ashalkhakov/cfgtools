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
val () = fprintln!(stdout_ref, "BEGIN of test00_B")
//
var gr = Grammar_make_nil ()
//
val _sS = Grammar_add_nonterminal(gr, "S")
val _sE = Grammar_add_nonterminal(gr, "E")
val _sT = Grammar_add_nonterminal(gr, "T")
val _sF = Grammar_add_nonterminal(gr, "F")
val _sa = Grammar_add_terminal(gr, "a")
val _sLPAREN = Grammar_add_terminal(gr, "(")
val _sRPAREN = Grammar_add_terminal(gr, ")")
val _sPLUS = Grammar_add_terminal(gr, "+")
val _sMINUS = Grammar_add_terminal(gr, "-")
val _sSTAR = Grammar_add_terminal(gr, "*")
//
val _ = Grammar_add_production (gr, _sS, $list{Symbol}(_sE, sym_EOF))
val st = Grammar_add_production (gr, _sE, $list{Symbol}(_sE, _sPLUS, _sT))
val _ = Grammar_add_production (gr, _sE, $list{Symbol}(_sT))
val _ = Grammar_add_production (gr, _sT, $list{Symbol}(_sT, _sSTAR, _sF))
val _ = Grammar_add_production (gr, _sT, $list{Symbol}(_sF))
val _ = Grammar_add_production (gr, _sF, $list{Symbol}(_sLPAREN, _sE, _sRPAREN))
val _ = Grammar_add_production (gr, _sF, $list{Symbol}(_sMINUS, _sT))
val _ = Grammar_add_production (gr, _sF, $list{Symbol}(_sa))
//
val () = Grammar_set_start (gr, st)
//
in
//
test00_fun (gr);
fprintln!(stdout_ref, "END of test00_B")
//
end // end of [main0]
