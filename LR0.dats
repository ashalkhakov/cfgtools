#include "share/atspre_staload.hats"
//
staload "./Grammar.sats"
staload "./Configuration.sats"
staload "./Automaton.sats"
staload "./LR0.sats"
//
staload
_(*anon*) = "./Grammar.dats"
staload
_(*anon*) = "./Automaton.dats"
staload
_(*anon*) = "./Configuration.dats"
//
staload _ = "prelude/DATS/integer.dats"
staload _ = "prelude/DATS/reference.dats"
staload _ = "prelude/DATS/list.dats"
staload _ = "prelude/DATS/pointer.dats"
staload _ = "prelude/DATS/gorder.dats"
//
staload "libats/SATS/funmap_rbtree.sats"
staload "libats/SATS/funset_avltree.sats"
//
staload
_(*anon*) = "libats/DATS/qlist.dats"
staload
_(*anon*) = "libats/DATS/funmap_rbtree.dats"
staload
_(*anon*) = "libats/DATS/funset_avltree.dats"
staload
_(*anon*) = "prelude/DATS/unsafe.dats"
//
assume LR0StateNr = int
//
typedef set = set (ConfigurationNr)
datatype LR0State = LR0State of (set)
//
typedef key = LR0StateNr
typedef itm = LR0State
typedef map0 = map (itm, key)
typedef map = map (key, itm)
//
val the_state_set = ref (funmap_make_nil{itm,key} ())
val the_states = ref (funmap_make_nil{key,itm} ())
val the_next_key = ref (0)
//
implement
compare_elt_elt<ConfigurationNr> (x, y) = compare_ConfigurationNr_ConfigurationNr (x, y)
//
implement
compare_key_key<LR0StateNr> (x, y) = compare (x, y)
//
implement
compare_key_key<itm> (x, y) = let
  val LR0State (s0) = x
  val LR0State (s1) = y
in
  funset_compare<ConfigurationNr> (s0, s1)
end
//
fun lookup (s: int): LR0State = let
  val map = the_states[]
  var state : itm // uninitialized
  val-true = $effmask_ref (funmap_search<key,itm> (map, s, state))
  prval () = opt_unsome {itm} (state)
in
  state
end
//
implement
fprint_val<LR0StateNr> (out, lr0) = let
  val LR0State (set) = lookup (lr0)
  val () = fprint_int (out, lr0)
  val () = fprint!(out, "= {")
  val () = fprint_newline (out)
  implement{}
  fprint_funset$sep (out) = fprint_string (out, ",\n")
  val () = fprint_funset<ConfigurationNr> (stdout_ref, set)
  val () = fprint_newline (out)
  val () = fprintln!(out, "}")
in
end
//
implement
LR0State_fprint (out, lr0) = fprint_val<LR0StateNr> (out, lr0)
//
implement
LR0State_print (p) = LR0State_fprint (stdout_ref, p)
//
fun
states_insert (id: key, state: LR0State): void = let
  var res: itm?
  val (vbox pf_at | p_at) = ref_get_viewptr {map} (the_states)
  val-false = $effmask_ref (funmap_insert<key,itm> (!p_at, id, state, res))
  prval () = opt_clear (res)
in
end
//
fun
state_set_insert (state: LR0State, id: key): void = let
  var res: key?
  val (vbox pf_at | p_at) = ref_get_viewptr {map0} (the_state_set)
  val-false = $effmask_ref (funmap_insert<itm,key> (!p_at, state, id, res))
  prval () = opt_clear (res)
in
end
//
fun
LR0_make (state: LR0State): LR0StateNr = let
var k0: key
in
  if :(k0: key?) => funmap_search<itm,key> (the_state_set[], state, k0) then let
    val id = opt_unsome_get<key> (k0)
  in
    id
  end else let
    prval () = opt_unnone {key} (k0)
    val id = ref_get_elt<int> (the_next_key)
    val () = ref_set_elt<int> (the_next_key, id+1)
    val () = states_insert (id, state)
    val () = state_set_insert (state, id)
    (*
    val () = print!("new lr0 state: ")
    val () = LR0State_print (id)
    val () = print_newline ()
    *)
  in
    id
  end
end
//
implement
LR0_initial (prod) = let
  val conf = Configuration_make (prod)
  val set = funset_sing<ConfigurationNr> (conf)
  val state = LR0State (set)
  val stateNr = LR0_make (state)
in
  LR0_closure (stateNr)
end
//
implement
LR0_closure (lr0) = let
  val LR0State (set) = lookup (lr0)
  //
  vtypedef env = set(ConfigurationNr)
  //
  implement
  funset_foreach$fwork<ConfigurationNr><env>(conf, env) =
    if ~Configuration_is_final (conf) then let
      val dot = Configuration_dot (conf)
      val prod = Configuration_production (conf)
      val item = Production_item (prod, dot)
    in
      if symbol_is_nt (item) then let
        implement
        Production_head_foreach$fwork<env> (prod, env) = let
          val newconf = Configuration_make (prod)
          val found = funset_insert<ConfigurationNr> (env, newconf)
        in
          (*empty*)
        end // end of [Production_head_foreach$fwork]
        val () = Production_head_foreach_env<env> (item, env)
      in
      end
    end
  //
  fun
  aux (out: &(env) >> _): void = let
    var env1 = funset_nil {ConfigurationNr} ()
    val () = funset_foreach_env<ConfigurationNr><env> (out, env1)
    val u = funset_union<ConfigurationNr> (out, env1)
  in
    if funset_equal (u, out) then () (*fixed point*)
    else let
      val () = out := u
    in
      aux (out)
    end
  end // end of [aux]
  //
  var env = set
  val () = aux (env)
  //
  val state = LR0State (env)
  val res = LR0_make (state)
in
  res
end
//
typedef succ_key = @(LR0StateNr,Symbol)
typedef succ_itm = LR0StateNr
val the_successor = ref (funmap_nil {succ_key, succ_itm} ())
//
extern
fun
the_successor_get (): map (succ_key, succ_itm)
implement
the_successor_get () = the_successor[]
//
extern
fun{env:vt0p}
successor_foreach$fwork (LR0StateNr, Symbol, LR0StateNr, &(env) >> _): void
extern
fun{env:vt0p}
successor_foreach_env (env: &(env) >> _): void
implement{env}
successor_foreach_env (env) = let
  val map = the_successor_get ()
  implement
  funmap_foreach$fwork<succ_key,succ_itm><env> (k, x, env) =
    successor_foreach$fwork<env> (k.0, k.1, x, env)
in
  funmap_foreach_env<succ_key,succ_itm><env> (map, env)
end
//
implement
compare_key_key<succ_key> (x, y) = let
  val (st0, sym0) = x
  val (st1, sym1) = y
  val res = compare (st0, st1)
in
  if res = 0 then compare_Symbol_Symbol (sym0, sym1)
  else res
end
//
implement
LR0_goto (lr0, sym) = let
  var res: succ_itm?
  val k0 = @(lr0, sym)
in
  if :(res: succ_itm?) => funmap_search<succ_key,succ_itm> (the_successor[], k0, res) then let
    val st = opt_unsome_get<succ_itm> (res)
  in
    st
  end else let
    prval () = opt_unnone {succ_itm} (res)
    val LR0State (set) = lookup (lr0)
    var env = funset_nil {ConfigurationNr} ()
    vtypedef Tenv = set
    implement
    funset_foreach$fwork<ConfigurationNr><Tenv>(conf, env) =
      if ~Configuration_is_final (conf) then let
        val dot = Configuration_dot (conf)
        val prod = Configuration_production (conf)
        val item = Production_item (prod, dot)
      in
        if sym = item then let
          val newconf = Configuration_advance (conf)
          (*
          val () = println!("newconf = ", newconf)
          *)
          // ignore duplicates
          val _ = funset_insert<ConfigurationNr> (env, newconf)
        in
          (*empty*)
        end
      end
    // end of [funset_foreach$fwork]
    val () = funset_foreach_env<ConfigurationNr><Tenv> (set, env)
    val state = LR0State (env)
    val stateNr = LR0_make (state)
    val res = LR0_closure (stateNr)
    val (vbox pf_at | p_at) = ref_get_viewptr {map(succ_key,succ_itm)} (the_successor)
    var res0: succ_itm
    val-false = $effmask_ref (funmap_insert<succ_key,succ_itm> (!p_at, k0, res, res0))
    prval () = opt_clear {succ_itm} (res0)
  in
    res
  end
end
//
implement{env}
LR0State_foreach_env (lr0, env) = let
  //
  val LR0State (set) = lookup (lr0)
  //
  implement
  funset_foreach$fwork<ConfigurationNr><env>(conf, env) =
    LR0State_foreach_env$fwork<env> (conf, env)
  //
  val () = funset_foreach_env<ConfigurationNr><env> (set, env)
in
end
//
implement{env}
LR0_foreach_env (env) = let
  val map = the_states[]
  implement
  funmap_foreach$fwork<key,itm><env> (k, x, env) = let
    val LR0State (s) = x
  in
    LR0_foreach$fwork<env> (k, env)
  end // end of [funmap_foreach$fwork]
in
  funmap_foreach_env<key,itm><env> (map, env)
end
//
implement
LR0State_is_empty (lr0) = let
  val LR0State (set) = lookup (lr0)
in
  funset_is_nil (set)
end
//
implement
LR0State_is_accepting (lr0) = let
  implement
  LR0State_foreach_env$fwork<bool> (c, env) = begin
    env := Configuration_is_accepting (c) || env
  end // end of [LR0State_foreach_env$fwork]
  var env = false : bool
  val () = LR0State_foreach_env<bool> (lr0, env)

  val () = print!("state ")
  val () = print_int (lr0)
  val () = if env then println!(" is accepting")
           else println!(" is NOT accepting")

in
  env
end // end of [LR0State_is_accepting]
//
extern
castfn
LR0State2State (LR0StateNr): State // this is safe as long as both are integers
//
//
implement
LR0_construct (p0(*augmented production*)) = let
//
vtypedef env = @(set(LR0StateNr), map(@(LR0StateNr,Symbol),LR0StateNr))
fun
aux0 (env: &(env) >> _): void = let
  vtypedef env0 = @(set(LR0StateNr), map(@(LR0StateNr,Symbol),LR0StateNr), bool)
  implement
  funset_foreach$fwork<LR0StateNr><env0>(I, env) = let
    implement
    Symbol_foreach$fwork<env0> (sym, env) = let
      val J = LR0_goto (I, sym)
    in
      if LR0State_is_empty (J) then ()(*error state!*)
      else let
        // add (J) to env.0
        val ex = funset_insert<LR0StateNr> (env.0, J)
        // add (I,sym)->J to env.1
        var res: LR0StateNr
        val k0 = @(I, sym)
        val ex(*found*) = funmap_insert<(@(LR0StateNr,Symbol)),LR0StateNr> (env.1, k0, J, res)
        val () = env.2 := ex && env.2 // all items exist? or some new were inserted?
        prval () = opt_clear {LR0StateNr} (res)
      in
        (*empty*)
      end
    end // end of [Symbol_foreach$fwork]
    val () = Symbol_foreach_env<env0> (env)
  in
  end
//
  val env0 = @(env.0, env.1, (g0ofg1)true)
  var env1 = @(env.0, env.1, (g0ofg1)true)
  val () = funset_foreach_env<LR0StateNr><env0> (env0.0, env1)
//
in
  if funset_equal<LR0StateNr> (env0.0, env1.0)
    && env1.2 = true // funmap_equal<(@(LR0StateNr,Symbol)),LR0StateNr> (env0.1, env1.1)
  then ()(*fixed point*)
  else let
    val () = env.0 := env1.0
    val () = env.1 := env1.1
  in
    aux0 (env)
  end
end

val s0 = LR0_initial (p0)

val () = println!("initial state:")
val () = LR0State_print (s0)
val () = println!("end of initial state")

var env0 = @(funset_sing (s0), funmap_nil ())
val () = aux0 (env0)
val lr0states = env0.0
val lr0trans = env0.1

// output all states
var env = 1 : int
implement(env)
funset_foreach$fwork<LR0StateNr><env> (s, env) = let
  val () = println!("LR0 state: ")
  val () = LR0State_print (s)
  val _ = State_make ()
in
end // end of [LR0_foreach$fwork]
val () = funset_foreach_env<LR0StateNr><int> (lr0states, env)
//
extern
castfn
s2s (LR0StateNr): State
//
implement(env)
funmap_foreach$fwork<(@(LR0StateNr,Symbol)),LR0StateNr><env> (k, j, env) = let
  val (i, sym) = k
  val () = print!("transition: [")
  val () = print_int (i)
  val () = print!(",")
  val () = print!(sym)
  val () = print!("] -> ")
  val () = print_int (j)
  val () = print_newline ()
in
  (*empty*)
end
val () = funmap_foreach_env<(@(LR0StateNr,Symbol)),LR0StateNr><int> (lr0trans, env)
//
// make reduce actions
implement(env)
funset_foreach$fwork<LR0StateNr><env> (i, env) = let
  implement
  LR0State_foreach_env$fwork<env> (conf, env) =
    if Configuration_is_final (conf) then {
      val prod = Configuration_production (conf)
      // put reduce against all terminals in the alphabet
      implement
      Symbol_foreach$fwork<env> (sym, env) =
        if symbol_is_term (sym) then {
          val () = Action_put_reduce ((s2s)i, sym, prod)
        } (* end of [Symbol_foreach$fwork] *)
      // end of [Symbol_foreach$fwork]
      val () = Symbol_foreach_env<env> (env)
      // reduce against $ too!
      val () = Action_put_reduce ((s2s)i, sym_EOF, prod)
    } (* end of [LR0State_foreach_env$fwork] *)
  val () = LR0State_foreach_env<env> (i, env)
in
end // end of [LR0_foreach$fwork]
val () = funset_foreach_env<LR0StateNr><int> (lr0states, env)
//
// make shift actions
implement(env)
funmap_foreach$fwork<(@(LR0StateNr,Symbol)),LR0StateNr><env> (k, j, env) = let
  val (i, sym) = k
in
  if symbol_is_term (sym) then Action_put_shift ((s2s)i, sym, (s2s)j)
  else Goto_put ((s2s)i, sym, (s2s)j)
end
val () = funmap_foreach_env<(@(LR0StateNr,Symbol)),LR0StateNr><int> (lr0trans, env)
// make accept actions
implement(env)
funset_foreach$fwork<LR0StateNr><env> (s, env) =
  if LR0State_is_accepting (s) then let

    val () = print!("putting an accept for EOF: ")
    val () = print_int (s)
    val () = print_newline ()

  in
    Action_put_accept ((s2s)s, sym_EOF)
  end
// end of [LR0_foreach$fwork]
val () = funset_foreach_env<LR0StateNr><int> (lr0states, env)

(*
TODO: check?
The grammar is LR(0) if:
1. there are no shift-reduce conflicts: i.e., no state in the DFA has an outgoing arc
and a reduce circle.
2. There are no reduce-reduce conflicts: i.e. no state in the DFA contains two items
which have the dot at the end of the RHS.
*)
in
  s0
end
