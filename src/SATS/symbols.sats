#include
"share/atspre_staload.hats"

staload SP = "./../utils/SATS/stapool.sats"
staload HT = "./../utils/SATS/ltab.sats"

typedef SYMBOLSNODE = @{
  termdefs= $SP.stapool_vt0
, terms= $HT.HASHTBLNODE
, ntermdefs= $SP.stapool_vt0
, nterms= $HT.HASHTBLNODE
, sym_eof= int
, sym_eps= int
} (* end of [SYMBOLSNODE] *)
//
absvt@ype symbols (int(*terminals*), int(*nonterminals*)) = SYMBOLSNODE
//
vtypedef symbols = [n,m:int] symbols (n, m)
//
abst@ype Symbol (int, bool) = int
typedef Terminal (n:int) = Symbol (n, true)
typedef Terminal = [n:int] Terminal (n)
typedef Nonterminal (m:int) = Symbol (m, false)
typedef Nonterminal = [m:int] Nonterminal (m)
typedef Symbol (n:int) = [b:bool] Symbol (n, b)
typedef Symbol = [n:int;b:bool] Symbol (n, b)
//
#define TERMS_MIN 32
#define NTERMS_MIN 32
//
fun
symbols_make_nil {n,m:int | n >= TERMS_MIN; m >= NTERMS_MIN} (
  &SYMBOLSNODE? >> symbols, size_t(n)(*max terms*), size_t(m)(*max nterms*)
): void
//
fun
symbols_free {n,m:int} (&symbols (n, m) >> SYMBOLSNODE?): void
//
fun
symbols_insert_term {n,m:int} (
  &symbols (n,m) >> symbols (n1, m), string
): #[n1:int | n1 == n || n1 == n+1] Terminal (n1) // watch out for duplicates!
//
fun
symbols_insert_nterm {n,m:int} (
  &symbols (n,m) >> symbols (n, m1), string
): #[m1:int | m1 == m || m1 == m+1] Nonterminal (m1) // watch out for duplicates!
//
fun
sym_EOF {n,m:int} (&symbols (n, m)): Terminal (n)
//
fun
sym_EPS {n,m:int} (&symbols (n, m)): Terminal (n)
//
(*
fun
symbol_is_valid {n,m,i:int} (&symbols (n, m), Symbol (i, b)): bool (i >= 0 && (b && i < n || ~b && i < m))*)
//
fun{env:vt0p}
foreach_term$fwork {n:int} (Terminal (n), string, &(env) >> _): void
//
fun{env:vt0p}
foreach_term_env {n,m:int} (&symbols (n, m), &(env) >> _): void
//
fun{env:vt0p}
foreach_nterm$fwork {n:int} (Nonterminal (n), string, &(env) >> _): void
//
fun{env:vt0p}
foreach_nterm_env {n,m:int} (&symbols (n, m), &(env) >> _): void
//
fun
fprint_Nonterminal {n,m:int} (FILEref, &symbols (n, m), Nonterminal (m)): void
overload fprint with fprint_Nonterminal of 10
//
fun
fprint_Terminal {n,m:int} (FILEref, &symbols (n, m), Terminal (n)): void
overload fprint with fprint_Terminal of 10
//
fun
fprint_Symbol {n,m,i:int} (FILEref, &symbols (n, m), Symbol(i)): void
overload fprint with fprint_Symbol
//
fun
fprint_symbols (FILEref, &symbols): void
overload fprint with fprint_symbols
//
fun
Symbol_is_terminal {i:int} {b:bool} (Symbol (i, b)): bool b
//
fun
Symbol_is_nonterminal {i:int} {b:bool} (Symbol (i, b)): bool (~b)
//
fun
compare_Terminal_Terminal (x: Terminal, y: Terminal):<> int
overload compare with compare_Terminal_Terminal
//
fun
eq_Terminal_Terminal (x: Terminal, y: Terminal):<> bool
overload = with eq_Terminal_Terminal
//
fun
neq_Terminal_Terminal (x: Terminal, y: Terminal):<> bool
overload <> with neq_Terminal_Terminal
//
fun
compare_Nonterminal_Nonterminal (x: Nonterminal, y: Nonterminal):<> int
overload compare with compare_Nonterminal_Nonterminal
//
fun
eq_Nonterminal_Nonterminal (x: Nonterminal, y: Nonterminal):<> bool
overload = with eq_Nonterminal_Nonterminal
//
fun
neq_Nonterminal_Nonterminal (x: Nonterminal, y: Nonterminal):<> bool
overload <> with neq_Nonterminal_Nonterminal
//
fun
compare_Symbol_Symbol (x: Symbol, y: Symbol):<> int
overload compare with compare_Symbol_Symbol
//
fun
eq_Symbol_Symbol (x: Symbol, y: Symbol):<> bool
overload = with eq_Symbol_Symbol
//
fun
neq_Symbol_Symbol (x: Symbol, y: Symbol):<> bool
overload <> with neq_Symbol_Symbol
//
(* ****** end of [symbol.sats] ****** *)
