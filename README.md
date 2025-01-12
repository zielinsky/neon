# Neon Language

**Neon** is an experimental programming language with dependent types, implementing Calculus of Constructions (CoC). It aims to provide a minimal yet expressive core language in which functions, types, and proofs can all coexist.


## Building

Neon is built with **Dune**. Ensure you have OCaml and Dune installed, then run:

```bash
dune build
```

To run the REPL (or a `.neon` file), do:

```bash
dune exec neon [file.neon]
```

- If you omit `[file.neon]`, Neon will start in an interactive REPL.
- Type `exit` to quit the REPL.

## Example

A small example of a Neon program illustrating dependent types and ADTs:

```neon
data List (A : Type) =
| Nil
| Cons (x : A) (xs : List(A))

let id (A : Type) (xs : List(A)) = xs

let nums = Cons(Int, 1, Cons(Int, 2, Nil(Int)))
let nums2 = id(Int, nums)
```

- `List` is a simple ADT with two constructors, `Nil` and `Cons`.
- `id` is a polymorphic function that takes a type `A` and a `List(A)`, returning the same list.
- `nums` is a `List Int` with two elements (1, 2).
- `nums2` is the result of applying `id(Int, nums)`.
