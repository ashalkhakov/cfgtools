#include
"share/atspre_staload.hats"
//
staload SP = "./../utils/SATS/stapool.sats"
staload HT = "./../utils/SATS/ltab.sats"
//
staload "./../SATS/symbols.sats"
//
(* ****** ****** *)
//
staload _ = "prelude/DATS/integer.dats"
staload _ = "prelude/DATS/array.dats"
staload _ = "libats/DATS/hashfun.dats"
//
staload _ = "./../utils/DATS/ltab.dats"
staload _ = "./../utils/DATS/stapool.dats"
//
(* ****** ****** *)
//
#define ATS_DYNLOADFLAG 0
//
local
//
staload UN = "prelude/SATS/unsafe.sats"
//
staload _ = "./../utils/DATS/ltab.dats"
staload _ = "./../utils/DATS/stapool.dats"
//
vtypedef lkuptab (n:int) = $HT.hashtbl (string, int, n)
//
vtypedef SYMBOLS (i:int, j:int) = [n,m:int] @{
  termdefs= $SP.stapool_vt (string, i, n)
, terms= lkuptab (n)
, ntermdefs= $SP.stapool_vt (string, j, m)
, nterms= lkuptab (m)
, sym_eof= $SP.pptr(i)
, sym_eps= $SP.pptr(i)
} (* end of [SYMBOLS] *)
//
assume symbols (n:int, m:int) = SYMBOLS (n, m)
//
dataprop symbol_p (int, int, bool) =
  | {i,n:nat | i < n} symbol_p_terminal (i, n, true)
  | {i:int;n:nat | i < 0; ~i - 1 < n} symbol_p_nonterminal (i, n, false)
//
typedef symbol (i:int, n:int, b:bool) = (symbol_p (i, n, b) | int(i))
assume Symbol (n:int, b:bool) = [i:int] symbol (i, n, b)
//
in // in of [local]
//
implement
Symbol_is_terminal {b} (sym) =
  if sym.1 >= 0 then let
    prval symbol_p_terminal () = sym.0
  in
    true
  end else let
    prval symbol_p_nonterminal () = sym.0
  in
    false
  end // end of [Symbol_is_terminal]
//
implement
Symbol_is_nonterminal {b} (sym) =
  if sym.1 >= 0 then let
    prval symbol_p_terminal () = sym.0
  in
    false
  end else let
    prval symbol_p_nonterminal () = sym.0
  in
    true
  end // end of [Symbol_is_terminal]
//
implement
compare_Terminal_Terminal (x, y) = compare (x.1, y.1)
implement
eq_Terminal_Terminal (x, y) = (x.1 = y.1)
implement
neq_Terminal_Terminal (x, y) = (x.1 <> y.1)
//
implement
compare_Nonterminal_Nonterminal (x, y) = let
  prval symbol_p_nonterminal () = x.0
  prval symbol_p_nonterminal () = y.0
  val x1 = ~x.1 - 1
  val y1 = ~y.1 - 1
in
  compare (x1, y1)
end // end of [compare_Nonterminal_Nonterminal]
implement
eq_Nonterminal_Nonterminal (x, y) = (x.1 = y.1)
implement
neq_Nonterminal_Nonterminal (x, y) = (x.1 <> y.1)
//
(*implement
fprint_Nonterminal (out, syms, nterm) = let
  prval symbol_p_nonterminal () = nterm.0
  val idx = ~nterm.1 - 1
  prval [i:int] EQINT () = eqint_make_gint (idx)
  prval () = lemma_stapool_param (syms.ntermdefs)
  val n = stapool_used<string> (syms.ntermdefs)
  prval [n:int] EQINT () = eqint_make_guint (n)
  val-true = idx >= 0
  val-true = idx <= (sz2i)n
  val lab = pptr_read<string> (syms.ntermdefs, idx)
in
  fprint!(out, "NT('", lab, "')")
end // end of [fprint_Nonterminal]
//
implement
fprint_Terminal (out, syms, term) = let
  prval symbol_p_terminal () = term.0
  val idx = term.1
  val n = stapool_used<string> (syms.termdefs)
  val-true = idx < (sz2i)n
  val lab = pptr_read<string> (syms.termdefs, idx)
in
  fprint!(out, "T('", lab, "')")
end // end of [fprint_Terminal]
*)
//
(*implement
fprint_Symbol (out, alpha, sym) = (
  if Symbol_is_nonterminal (sym) then fprint_Nonterminal (out, alpha, sym)
  else fprint_Terminal (out, alpha, sym)
) (* end of [fprint_Symbol] *)
*)
//
implement
symbols_make_nil {n,m} (res, maxterms, maxnterms) = let
//
  val () = $SP.stapool_init<string> (res.termdefs, maxterms)
  val () = $SP.stapool_init<string> (res.ntermdefs, maxnterms)
//
  val () = $HT.hashtbl_make_nil<string,int> (res.terms, maxterms)
  val () = $HT.hashtbl_make_nil<string,int> (res.nterms, maxnterms)
//
  var itm_term: int
//
  val eof = $SP.stapool_alloc<string> (res.termdefs, "EOF")
  val-false = $HT.hashtbl_insert<string,int> (res.terms, "EOF", eof, itm_term)
  prval () = opt_clear (itm_term)
  val () = res.sym_eof := eof
//
  val eps = $SP.stapool_alloc<string> (res.termdefs, "EPS")
  val-false = $HT.hashtbl_insert<string,int> (res.terms, "EPS", eps, itm_term)
  prval () = opt_clear (itm_term)
  val () = res.sym_eps := eps
//
in
  (*empty*)
end // end of [symbols_make_nil]
//
implement
symbols_free {n,m} (res) = let
  //
  val () = $HT.hashtbl_free<string,int> (res.terms)
  val () = $HT.hashtbl_free<string,int> (res.nterms)
  //
  val () = $SP.stapool_free {string} (res.termdefs)
  val () = $SP.stapool_free {string} (res.ntermdefs)
  //
in
  (*empty*)
end // end of [symbols_free]
//
implement
symbols_insert_term {n,m} (syms, trm) = let
//
  typedef T1 = int
//
  var itm_term: T1
//
  prval () = $HT.lemma_hashtbl_param (syms.terms)
  val res1 = $HT.hashtbl_search<string,T1> (syms.terms, trm, itm_term)
//
in
  if :(itm_term: T1?) => res1 then let
    val res = opt_unsome_get (itm_term)
    val res = $UN.castvwtp0 {natLt(n)} (res)
  in
    (symbol_p_terminal () | res)
  end else let
    prval () = opt_unnone {T1} (itm_term)
    val-true = $SP.stapool_isnot_full<string> (syms.termdefs)
    val t = $SP.stapool_alloc<string> (syms.termdefs, trm)
    val t1 = (g0ofg1)t
    val-false = $HT.hashtbl_insert<string,int> (syms.terms, trm, t1, itm_term)
    prval () = opt_unnone {T1} (itm_term)
  in
    (symbol_p_terminal () | t)
  end // end of [if]
end // end of [symbols_insert_term]
//
implement
symbols_insert_nterm {n,m} (syms, ntm) = let
//
  typedef T2 = int
//
  var itm_ntm: T2
//
  prval () = $HT.lemma_hashtbl_param (syms.nterms)
  val res1 = $HT.hashtbl_search<string,T2> (syms.nterms, ntm, itm_ntm)
//
in
  if :(itm_ntm: T2?) => res1 then let
    val res = opt_unsome_get (itm_ntm)
    val res = $UN.castvwtp0 {natLt(m)} (res)
  in
    (symbol_p_nonterminal () | ~res - 1)
  end else let
    prval () = opt_unnone {T2} (itm_ntm)
    val-true = $SP.stapool_isnot_full<string> (syms.ntermdefs)
    val t = $SP.stapool_alloc<string> (syms.ntermdefs, ntm)
    val-false = $HT.hashtbl_insert<string,T2> (syms.nterms, ntm, t, itm_ntm)
    prval () = opt_clear {T2} (itm_ntm)
  in
    (symbol_p_nonterminal () | ~t - 1)
  end // end of [if]
end // end of [symbols_insert_nterm]
//
implement
sym_EOF {n,m} (syms) = let
  prval () = $SP.lemma_stapool_param (syms.termdefs)
  val res = syms.sym_eof
in
  (symbol_p_terminal () | res)
end // end of [sym_EOF]
//
implement
sym_EPS {n,m} (syms) = let
  prval () = $SP.lemma_stapool_param (syms.termdefs)
  val res = syms.sym_eps
in
  (symbol_p_terminal () | res)
end // end of [sym_EPS]
//
(*implement
symbol_is_valid {n,m,i} (syms, s) =
  if symbol_is_terminal (s) then let
    val x = s.1 < syms.
  in
  end else let
  in
  end
// : bool (i >= 0 && (b && i < n || ~b && i < m))
*)
//
implement{env}
foreach_term$fwork (trm, lab, env) = ()
implement{env}
foreach_term_env {n,m} (syms, env) = {
  implement
  $SP.stapool_foreach$fwork<string><env> (idx, x, env) = let
    val trm = $UN.castvwtp0{Terminal} (idx)
  in
    foreach_term$fwork<env> (trm, x, env)
  end // end of [$SP.stapool_foreach$fwork]
  val () = $SP.stapool_foreach_env<string><env> (syms.termdefs, env)
} (* end of [foreach_term_env] *)
//
implement{env}
foreach_nterm$fwork (ntm, lab, env) = ()
implement{env}
foreach_nterm_env {n,m} (syms, env) = {
  implement
  $SP.stapool_foreach$fwork<string><env> (idx, x, env) = let
    val trm = $UN.castvwtp0{Nonterminal} (idx)
  in
    foreach_nterm$fwork<env> (trm, x, env)
  end // end of [$P.stapool_foreach$fwork]
  val () = $SP.stapool_foreach_env<string><env> (syms.ntermdefs, env)
} (* end of [foreach_nterm_env] *)
//
//
implement
fprint_symbols (out, syms) = let
  val () = fprintln!(out, "terminals:")
  implement(env)
  foreach_term$fwork<env> (t, lab, env) = {
    val () = fprintln!(out, t.1)
    val () = fprintln!(out, " = ", lab)
    val () = fprint_newline (out)
  } (* end of [foreach_term$fwork] *)
  var env = 0: int
  val () = foreach_term_env<int> (syms, env)
  val () = fprintln!(out, "nonterminals:")
  implement(env)
  foreach_nterm$fwork<env> (nt, lab, env) = {
    val () = fprintln!(out, nt.1)
    val () = fprintln!(out, " = ", lab)
    val () = fprint_newline (out)
  } (* end of [foreach_nterm$fwork] *)
  val () = foreach_nterm_env<int> (syms, env)
in
end // end of [fprint_symbols]
//
end // end of [local]
//

