# Existentials

Rosi now has initial support for first-class implicit existentials.

## Types

Existential types use the keyword `exists`, as in:

```rosi
type Comparer : * -> *
type Comparer = \t. exists v. Pair (t -> v) (Compare v)
```

where `Compare v` is `v -> v -> Ord`.

Here `Comparer t` is an existential pair of a type `v` and a (normal) pair of a `t -> v` function and a `v` comparer.

Existential types can bind multiple variables at once

```rosi
type Bogus : * -> *
type Bogus = \t. exists u v. Pi {'1 := t -> u, '2 := t -> v, '3 := u -> v -> Bool}
```

Existential types can constrain their existential variables

```rosi
type Subrecord : R[*] -> *
type Subrecord z = exists y. y < z => Pi y
```

## Introduction

Introduction of existential types is implicit, driven by the expected type.

For example, suppose we have a function

```rosi
compare : Comparer t -> t -> t -> Cmp
```

We can then call `compare` as, for example,

```rosi
compare (pair .'1 f)
```

(assuming `f` is a suitable comparison function). Existential packing will be introduced automatically around the `pair` term.

Here is a more full example:

```rosi
compareField : {l := t} < z => #l -> Compare t -> Comparer (Pi z)
compareField l f = pair .l f
```

The `compareField` is returning a value of existential type, so `pair .l f` is automatically packed.

Packs can be made explicit using the `pack : #f -> f t -> (exists x. f x)` function:

```rosi
compareField' : forall z. {l := t} < z => #l -> Compare t -> Comparer (Pi z)
compareField' @z l f = pack #(\v. Pair (Pi z -> v) (Compare v)) (pair (.l) f)
```

The definition of `pack` does not do anything special; its only role is to fix the output type in a way that will trigger the automatic introduction of existential packing.

There is one current limitation on implicit packing: we do not implicitly pack at explicit type abstractions `\@t. M`. To pack a type abstraction, use the `pack` function.

## Elimination

Arguments to functions *that are known to be existential* are automatically unpacked.

For example, the `compare` function used above is defined:

```rosi
compare : Comparer t -> Compare t
compare p x y = p.'2 (p.'1 x) (p.'1 y)
```

Within the body of the `compare` function, we can use `p` as if it were a pair.

We can choose to bring the existentially-bound type into scope.

```rosi
compare' : forall t. Comparer t -> Compare t
compare' @t (@!v p) (x y : t) = p.'2 (p.'1 x : v) (p.'1 y : v)
```

We can also give a type annotation within the unpacking of an existential type.

```rosi
compare' @t (@!v p : Comparer t) (x y : t) = p.'2 (p.'1 x : v) (p.'1 y : v)
```

