# cfgtools

Context-free grammar tools for ATS.

## Features

* `grm`: a typeful in-memory context-free grammar representation
* `grmfuncs`: efficient implementations of `FIRST`/`FOLLOW`-set
  computation for a given grammar
* `utils/ltab`: compact lookup hash table
* `utils/fundigraph`: directed graph representation with
  strongly-connected components and efficient reflexive, transitive
  closure algorithms

## Usage examples

TODO

## Getting started

### Running tests

The whole thing doesn't build yet, but the tests do. Please see the
`src/TEST` subdirectory.


## Roadmap

1. refactoring: make `grm` use the new `symbol` data type (already
   exists in a separate module)
2. implement code for doing constructions of automata (LR0, LR1,
   LALR1, LL1, etc.)
3. implement lexers/parsers for various inputs to `grm` (JSON format,
   something with yacc/lex compat, etc.)
4. implement different "plug-in" modules for outputting automata (as
   JSON/XML, as executable code -- ATS code, etc.)
5. compile to *WebAssembly*, make it available on a webpage ("enter
   your grammar here, have it converted to whatever you want!")
