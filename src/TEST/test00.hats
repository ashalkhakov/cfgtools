//
extern
fun{a:t0p}
funset_filter$pred (x: a): bool
extern
fun{a:t0p}{env:vt0p}
funset_filter$fwork (x: a, &(env) >> _): void
extern
fun{a:t0p}{env:vt0p}
funset_filter_env (set: set(INV(a)), &(env) >> _): void
//
implement{a}
funset_filter$pred (x) = true
implement{a}{env}
funset_filter$fwork (x, env) = ()
implement{a}{env}
funset_filter_env (set, env) = let
  implement
  funset_foreach$fwork<a><env> (x, env) =
    if funset_filter$pred<a> (x) then let
      val () = funset_filter$fwork<a><env> (x, env)
    in
    end
in
  funset_foreach_env<a><env> (set, env)
end
//
(* ****** ****** *)

fun
test00_fun (gr: Grammar): void = let
//
val () = fprintln!(stdout_ref, "grammar: ", gr)
//
var alphabet = Grammar_get_syms (gr)
//
implement
funset_filter$pred<Symbol> (x) = Symbol_is_terminal (x)
implement(env)
funset_filter$fwork<Symbol><env> (x, env) = fprint_Symbol (stdout_ref, x)
//
var env: void
val () = fprint!(stdout_ref, "terminals:")
val () = funset_filter_env<Symbol> (alphabet, env)
//
implement
funset_filter$pred<Symbol> (x) = Symbol_is_nonterminal (x)
implement(env)
funset_filter$fwork<Symbol><env> (x, env) =
  (fprint_Symbol (stdout_ref, x); fprint_newline (stdout_ref))
val () = fprint!(stdout_ref, "nonterminals:")
val nonterminals = funset_filter_env<Symbol> (alphabet, env)
//
(*
val () = fprint!(stdout_ref, "productions starting with: ")
val () = fprint_Symbol (stdout_ref, _sE)
val () = fprint_newline (stdout_ref)
implement
funmap_filter$pred<Production,size_t> (x, k) = Production_derives (x) = _sE
implement(env)
funmap_filter$fwork<Production,size_t><env> (x, k, env) = fprintln!(stdout_ref, x)
val () = funmap_filter_env<Production,size_t> (prods, env)
*)
//
(*
val () = fprintln!(stdout_ref, "INITFIRST(E) = ", INITFIRST (gr, _sE))
val () = fprintln!(stdout_ref, "INITFIRST(S) = ", INITFIRST (gr, _sS))
val () = fprintln!(stdout_ref, "INITFIRST(F) = ", INITFIRST (gr, _sF))
*)
//
(*
var nnode_gfirst: size_t
var arrnode: ptr
val gfirst = GFIRST (gr, nnode_gfirst, arrnode)
val () = fprintln!(stdout_ref, "GFIRST(gr) = ")
val () = fprint_fundigraph (stdout_ref, gfirst)
val () = fprint_newline (stdout_ref)
val () = arrayptr_free (arrnode)
*)
//
var nonterms: ptr
var nontermmap: ptr
val nodecount = Grammar_nonterminals (gr, nonterms, nontermmap)
prval () = lemma_g1uint_param (nodecount)

val () = fprintln!(stdout_ref, "calling ERASABLE")
var erasable = ERASABLE (gr, nonterms, nontermmap, nodecount)
val () = fprintln!(stdout_ref, "erasable array:")
val () = fprint_arrayptr<bool> (stdout_ref, erasable, nodecount)
val () = fprint_newline (stdout_ref)

val () = fprintln!(stdout_ref, "calling FIRSTSETS")
var fstsets = FIRSTSETS (gr, erasable, nonterms, nontermmap, nodecount)
//
val () = fprintln!(stdout_ref, "FIRSTSETS(gr) = ")
val () = fprintln!(stdout_ref, "nonterminals array:")
val () = fprint_arrayptr<Nonterminal> (stdout_ref, nonterms, nodecount)
val () = fprint_newline (stdout_ref)
//
val () = fprintln!(stdout_ref, "first set termsets array:")
implement
fprint_val<set(Terminal)> (out, x) = let
  val () = fprint!(out, "{")
  val () = fprint_funset<Terminal> (out, x)
  val () = fprint!(out, "}")
in
end // end of [fprint_val]
val () = fprint_arrayptr<set(Terminal)> (stdout_ref, fstsets, nodecount)
val () = fprint_newline (stdout_ref)
//
var flwsets = FOLLOWSETS (gr, erasable, nonterms, nontermmap, fstsets, nodecount)
//
val () = fprintln!(stdout_ref, "followset termsets array:")
implement
fprint_val<set(Terminal)> (out, x) = let
  val () = fprint!(out, "{")
  val () = fprint_funset<Terminal> (out, x)
  val () = fprint!(out, "}")
in
end // end of [fprint_val]
val () = fprint_arrayptr<set(Terminal)> (stdout_ref, flwsets, nodecount)
val () = fprint_newline (stdout_ref)
//
val () = arrayptr_free (erasable)
val () = arrayptr_free (nonterms)
val () = arrayptr_free (fstsets)
val () = arrayptr_free (flwsets)
//
in
end // end of [test00_fun]
