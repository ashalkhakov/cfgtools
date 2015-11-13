#include "share/atspre_staload.hats"
//
staload "./Grammar.sats"
staload "./LR0Configuration.sats"
staload "./Automaton.sats"
staload "./LR0.sats"
//
staload
_(*anon*) = "./Grammar.dats"
staload
_(*anon*) = "./Automaton.dats"
staload
_(*anon*) = "./LR0Configuration.dats"
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
typedef set = set (LR0ConfigurationNr)
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
compare_elt_elt<LR0ConfigurationNr> (x, y) = compare_LR0ConfigurationNr_LR0ConfigurationNr (x, y)
//
implement
compare_key_key<LR0StateNr> (x, y) = compare (x, y)
//
implement
compare_key_key<itm> (x, y) = let
  val LR0State (s0) = x
  val LR0State (s1) = y
in
  funset_compare<LR0ConfigurationNr> (s0, s1)
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
  val () = fprint_funset<LR0ConfigurationNr> (stdout_ref, set)
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
  val conf = LR0Configuration_make (prod)
  val set = funset_sing<LR0ConfigurationNr> (conf)
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
  vtypedef env = set(LR0ConfigurationNr)
  //
  implement
  funset_foreach$fwork<LR0ConfigurationNr><env>(conf, env) =
    if ~LR0Configuration_is_final (conf) then let
      val dot = LR0Configuration_dot (conf)
      val prod = LR0Configuration_production (conf)
      val item = Production_item (prod, dot)
    in
      if symbol_is_nt (item) then let
        implement
        Production_head_foreach$fwork<env> (prod, env) = let
          val newconf = LR0Configuration_make (prod)
          val found = funset_insert<LR0ConfigurationNr> (env, newconf)
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
    var env1 = funset_nil {LR0ConfigurationNr} ()
    val () = funset_foreach_env<LR0ConfigurationNr><env> (out, env1)
    val u = funset_union<LR0ConfigurationNr> (out, env1)
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
  // NOTE: termination condition:
  // there exists in the set a configuration A -> .e
  // (where e is a symbol string)
  // for every nonterminal A which is focussed by the dot in
  // some other configuration in the set
  // - the number of nonterminals which are focussed but
  //   haven't been added to the closure will decrease
  val () = aux (env)
  //
  val state = LR0State (env)
  val res = LR0_make (state)
in
  res
end
//
implement
compare_key_key<(@(LR0StateNr,Symbol))> (x, y) = let
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
  val LR0State (set) = lookup (lr0)
  var env = funset_nil {LR0ConfigurationNr} ()
  vtypedef Tenv = set
  implement
  funset_foreach$fwork<LR0ConfigurationNr><Tenv>(conf, env) =
    if ~LR0Configuration_is_final (conf) then let
      val dot = LR0Configuration_dot (conf)
      val prod = LR0Configuration_production (conf)
      val item = Production_item (prod, dot)
    in
      if sym = item then let
        val newconf = LR0Configuration_advance (conf)
        (*
        val () = println!("newconf = ", newconf)
        *)
        // ignore duplicates
        val _ = funset_insert<LR0ConfigurationNr> (env, newconf)
      in
        (*empty*)
      end
    end
  // end of [funset_foreach$fwork]
  val () = funset_foreach_env<LR0ConfigurationNr><Tenv> (set, env)
  val state = LR0State (env)
  val stateNr = LR0_make (state)
  val res = LR0_closure (stateNr)
in
  res
end
//
implement{env}
LR0State_foreach_env (lr0, env) = let
  //
  val LR0State (set) = lookup (lr0)
  //
  implement
  funset_foreach$fwork<LR0ConfigurationNr><env>(conf, env) =
    LR0State_foreach_env$fwork<env> (conf, env)
  //
  val () = funset_foreach_env<LR0ConfigurationNr><env> (set, env)
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
    env := LR0Configuration_is_accepting (c) || env
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
implement
LR0_use_SLR1<> () = true
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
    && env1.2 = true then ()(*fixed point*)
  else let
    val () = env.0 := env1.0
    val () = env.1 := env1.1
  in
    aux0 (env)
  end
end // end of [aux0]
//
val s0 = LR0_initial (p0)
//
val () = println!("initial state:")
val () = LR0State_print (s0)
val () = println!("end of initial state")
//
var env0 = @(funset_sing (s0), funmap_nil ())
val () = aux0 (env0)
val lr0states = env0.0
val lr0trans = env0.1
//
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
    if LR0Configuration_is_final (conf) then {
      val prod = LR0Configuration_production (conf)
      val use_slr1 = LR0_use_SLR1 ()
      val () =
        if :(env: env) => use_slr1 then let
          // SLR(1): put reduce against all follow(Production_yields(prod))
          val lhs = Production_yields (prod)
          val fa = follow (lhs)

          val () = println!("follow(", lhs, ") = ", fa)

          implement(env)
          termset_foreach$fwork<env> (sym, env) = {
            val () = Action_put_reduce ((s2s)i, sym, prod)
          } (* end of [termset_foreach$fwork] *)
          var e = 1 : int
          val () = termset_foreach_env<int> (fa, e)
        in
          (*empty*)
        end
        else let
          // LR(0): put reduce against all terminals in the alphabet
          implement
          Symbol_foreach$fwork<env> (sym, env) =
            if symbol_is_term (sym) then {
              val () = Action_put_reduce ((s2s)i, sym, prod)
            } (* end of [Symbol_foreach$fwork] *)
          // end of [Symbol_foreach$fwork]
          val () = Symbol_foreach_env<env> (env)
          // reduce against $ too!
          val () = Action_put_reduce ((s2s)i, sym_EOF, prod)
        in
          (*empty*)
        end
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
