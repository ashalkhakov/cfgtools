sortdef t0p = t@ype

// digraph of n vertices
abstype digraph_type (n: int) = ptr

typedef digraph (n:int) = digraph_type (n)
typedef digraph = [n:nat] digraph (n)

fun
fundigraph_make {n:nat} (n:size_t n): digraph(n)

fun
fundigraph_size {n:nat} (digraph(n)): size_t(n) // nodes in the graph

fun
fundigraph_insert_edge {n,i,j:nat | i < n; j < n} (
  &digraph (n) >> _
, size_t i(*src*)
, size_t j(*dst*)
) : void

fun{
} fprint_fundigraph$sep (out: FILEref): void // "; "
fun{
} fprint_fundigraph$edgeto (out: FILEref): void // "->"
fun
fprint_fundigraph
  (out: FILEref, dg: digraph):  void

overload fprint with fprint_fundigraph

fun{env:vt0p}
fundigraph_foreach_dfs$fwork (
  size_t(*src*), size_t(*dst*), &(env) >> _
): void

fun{env:vt0p}
fundigraph_foreach_dfs_from_env
  {n:nat}
  (digraph (n), i: sizeLt(n), &(env) >> _): void

fun{env:vt0p}
fundigraph_foreach_edge$fwork (
  size_t(*src*), size_t(*dst*), &(env) >> _
): void
fun{env:vt0p}
fundigraph_foreach_edge
  {n:nat}
  (digraph (n), &(env) >> _): void

fun{env:vt0p}
fundigraph_scc$beg (&(env) >> _): void
fun{env:vt0p}
fundigraph_scc$node (size_t, &(env)>>_): void
fun{env:vt0p}
fundigraph_scc$end (&(env) >> _): void

fun{env:vt0p}
fundigraph_scc
  {n:nat}
  (digraph (n), &(env) >> _): void

(* ****** ****** *)
// reflexive, transitive closure of a directed graph

absvtype digraph_rtc (int) = ptr

fun
fundigraph_rtc_init
  {n:nat}
  (digraph (n)): digraph_rtc (n)
fun
fundigraph_rtc_free
  {n:nat}
  (digraph_rtc (n)): void

fun
fundigraph_rtc_reachable_from {n:nat} (!digraph_rtc (n), sizeLt(n), sizeLt(n)): bool

