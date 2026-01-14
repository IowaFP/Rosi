# Rosi

Rosi is an implementation of a row-typed functional programming language, based
on the Rose family of calculi.

The Rose calculi are formally described in:

* J. Garrett Morris and James McKinna. 2019. Abstracting extensible data types: or, rows by any other name. Proc. ACM Program. Lang. 3, POPL, Article 12 (January 2019), 28 pages. https://doi.org/10.1145/3290325
* Alex Hubers and J. Garrett Morris. 2023. Generic Programming with Extensible Data Types: Or, Making Ad Hoc Extensible Data Types Less Ad Hoc. Proc. ACM Program. Lang. 7, ICFP, Article 201 (August 2023), 29 pages. https://doi.org/10.1145/3607843
* Alex Hubers and Apoorv Ingle and Andrew Marmaduke and J. Garrett Morris. 2024. Extensible Recursive Functions, Algebraically. https://arxiv.org/abs/2410.11742

# Disclaimer

Rosi is research-grade software. In particular:

* The currently supported syntax is inflexible
* The typechecker is slow, and the evaluator is (remarkably) slower
* Error messages range from obscure to entirely inscrutable.

That having been said, there is some fun to be had in exploring the Rose approach to extensible data types, and in our treatment of polymorphism, and Rosi should make it easier to do so.

We welcome involvement&mdash;questions, bug reports, or patches.

# Building

Rosi builds using `cabal`. You should find that `cabal configure; cabal build` does the trick for you.

# Running

Rosi typechecks and evaluates Rose programs; it does not (yet) have a REPL or other interactive support.

By default, Rosi only checks types. (This probably says something about the focus of the implementors...) For example, to typecheck the extensible expression examples, you could say:

```shell
> cabal run Rosi -- -i rolib -i examples EE
>
```

Top-level definitions can be evaluated by providing the `-e` option. For example:

```shell
> cabal run Rosi -- -i rolib -i examples EE -e szId,szId0
szId = in (<0, in (<0, in (<1, ()>)>)>)
szId0 = in (<0, in (<0, in (<1, ()>)>)>)
>
```

By default, Rosi searches for modules in the current directory. Its search list can be expanded using the `-i` option. Common options can a configuration file in the current directory, or in your XDG_CONFIG directory. Rosi looks for configuration files with the same name as its executable; to take best advantage of this, you may not want to invoke Rosi via `cabal run`.

# Rose by Example

This section gives a brief overview of the Rose language, via a series of (hopefully illustrative) examples. These examples are drawn from the papers listed above.

## Wand's problem

The original motivation for Rose was suporting record concatenation, and its dual branching operator on variants.  Mitchell Wand's [1989 paper](https://lics.siglog.org/archive/1989/Wand-Typeinferenceforrec.html) on type inference for record concatenation [\[pdf\]](https://www.cs.tufts.edu/~nr/cs257/archive/mitch-wand/types-simple-objects.pdf) gives the following motivating challenge:

> Concatenation poses severe problems for typing systems. Consider the term *λxy.(x ∥ y).a + 1*. This should be applicable to any pair of records *x* and *y* in which *y* has an integer *a* field or in which *x* has an integer *a* field and *y* has an absent *a* field. This term does not have a principal type in any known system...

Wand's solution to this is to use intersection types to combine the two possible accounts of its type. In Rose, we use qualified types instead. Our solution looks like this (extracted from [Wand.ro](examples/Wand.ro)):

```
wand5 : forall x y z t. x + y ~ z, {'l := t} < z => Pi x -> Pi y -> t
wand5 = \ m n. prj (m ++ n) / 'l
```

We start with the type. The conclusion of the type, `Pi x -> Pi y -> t` indicates that this is a function from two records, built from rows `x` and `y`, to a result type `t`. The predicates of the type restrict `x` and `y`. First, we require that `x` and `y` must be able to be combined, giving a combined row `z`. This predicate might fail, for example, if `x` and `y` share a label. Then, we require that the label `'l` appear in the combined row `z`, associated with type `t`. This predicate might fail if neither `x` nor `y` contains row `l'`.

Several notes about Rosi:

* Rosi can (generally) infer kinds. However, there is no automatic quantification: all type variables must be explicitly listed in a `forall`.
* Concrete labels begin with a single quotation mark: `'l` is a concrete label, whereas `l` (without the quote) might be a type variable of label kind.
* Rows are written in braces, and associations with `:=`.
* All definitions *must* have type annotations (although they need not be adjacent in the source file).

We move on to the term. Rose's primitive record operations are *concatenation* of arbitrary records, and *projection* of arbitrary subrecords, as opposed to the more typical operations of *extension* with a single field and *projection* of single fields. In this case, the term has three operations:

* Concatenation `_ ++ _`: we begin by concatenating records `m` and `n`.
* Projection `prj _`: we then project an *arbitrary* subrecord of the concatenation. The particular subrecord projected will be determined by the context.
* Unlabeling `_ / _`: finally, we "unlabel" the projected record. The unlabeling operation `_ / #'l` is (almost) only well typed for the singleton record with field `'l`; this is the context that determines the projected subrecord.

Several additional notes about Rosi:

* Rosi's parser is not clever about left-hand sides of definitions: functions must be written using λs (syntactically `\`s) on the right-hand sides of equations.
* `'l` is a *singleton* value "carrying" the type `'l`. Our guiding principle for Rosi is that type arguments ought to be implicit, so we capture cases where type arguments are necessary using singletons. We do not always manage to follow this principle, sometimes because type inference is hard, and sometimes simply through oversights in the language.

Rosi can generally infer the presence of type abstractions and type applications, but they can be given explicitly if necessary. Here is the fully explicit version of the preceding example (inhabiting the same type:)
```
wand0 = /\ x y z : R[*], t : *. \ m : Pi x, n : Pi y.
        prj [{'l := t}] [z] ((++) [x] [y] [z] m n) / #'l
```
`R[k]` is syntax for rows of kind `k`; `*` is the kind of types. Rosi does not support general infix operators; the use of `++` as infix and `(++)` as the corresponding prefix operator is hard-wired into the parser.


We can abstract over the particular label being projected:
```
wand7 : forall x y z l t. x + y ~ z, {l := t} < z => #l -> Pi x -> Pi y -> t
wand7 = \l m n. prj (m ++ n) / l
```

The projection-and-unlabeling step of this example is commonplace. The [base library](rolib/Ro/Base.ro) defines an operator to do this:
```
sel : forall l : L, t : *, z : R[*]. {l := t} < z => Pi z -> #l -> t
sel = \ r l. prj r / l
```
and Rosi has syntax for selection:
```
wand8 : forall x y z l t. x + y ~ z, {l := t} < z => #l -> Pi x -> Pi y -> t
wand8 = \l m n. .l (m ++ n)
```
Here `.l` is the name of the `l` selection function. Rosi also allows you to write `m.l` or `n.l` for selection from a variable.


## Variants

Variants are dual to records. We can imagine a (less intuitive) dual to Wand's problem, with a type like:

```
dnaw : forall x y z t u. x + y ~ z, {'l := t} < z => (Sigma x -> u) -> (Sigma y -> u) -> t -> u
```

The claim is that, if we know that `{'l := t}` is somewhere in the combination of `x` and `y`, then given an *eliminator* for variants built from row `x` to type `u` and eliminator for variants built from row `y` to type `u`, we can get from a `t` to a `u`.  The term inhabiting this type is:

```
dnaw = \r s x. (r | s) (inj ('l := x))
```

This term also demonstrates three operators:

* Branching `_ | _`: we combine the eliminators for `Sigma x` and `Sigma y` to get an eliminator for `Sigma z`
* Injection `inj _`: dual to projection, injects arbitrary subvariants into a variant type.
* Labeling `_ := _`: in this case, we construct an element of the singleton variant type to inject.

Note that overload the labeling and unlabeling operators for construction and elimination of singleton records and variants.

As with selecting individual record fields, the base library defines an operator `con` that combines labeling and injection, and syntax for construction:
```
dnaw1 : forall x y z l t u. x + y ~ z, {l := t} < z => #l -> (Sigma x -> u) -> (Sigma y -> u) -> t -> u
dnaw1 = \l f g x. (f | g) (l: x)
```

Unlabeling is used in writing individual cases of a variant eliminator. Given a Boolean type defined as:
```
type Bool : *
type Bool = Sigma { 'True := Unit, 'False := Unit}
```
We could write the inversion function as:
```
not : Bool -> Bool
not = (\b. 'False: (b / 'True))
    | (\b. 'True: (b / 'False))
```
On the first line, `b` must be of the singleton variant type `Sigma { 'True := Unit }` (because we unlabel it with `'True`), and on the second line `b` must be of the singleton variant type `Sigma { 'False := Unit }`, for a similar reason. This pattern is abstracted by the `case` function:
```
not : Bool -> Bool
not = case #'True (\u. 'False: u)
    | case #'False (\u. 'True: u)
```
Again, this pattern is common enough that we have built in syntax for it.
```
not = 'True: u  -> 'False: u
    | 'False: u -> 'True: u
```
This syntax is not particularly flexible. In particular, we do not (yet) have any kind of support for nested patterns.

## Label-generic programming

One of the more recent developments of Rose is what we've termed *label-generic* programming.

To compare two Boolean values for equality, we could use a term like

```
eqBool : Bool -> Bool -> Bool
eqBool = 'True: u  -> id
       | 'False: u -> not
```

In writing this term, we needed to know the constructors of `Bool`, and that any two values of `Unit` type are identical. Consider the more general case, in which we have two values of an arbitrary variant type `Sigma z`. Intuitively, to compare them for equality, all we have to know is how to compare each type in the range of `z` for equality. The rest of the comparison would be the same for any instantiation of `z`.

Rose allows us to just such a generic comparison function. We proceed in several steps. First, we define what it means to be an equality comparison for a type `t`:
```
type Eq : * -> *
type Eq = \t. t -> t -> Bool
```
* Rose is an extension of Fω, with arbitrary access to type-level functions.
* That said, Rosi's current support for higher-order unification is, to be polite, minimal. Explicit type arguments are require more often than might be hoped.

Second, we need to express the idea of a *record of comparison functions for a row `z`*. In Rosi, we can write this as `Pi (Eq z)`. There is a subtlety here: because `Eq` is a `* -> *` operator, but `z` is a row, Rosi interprets `Eq z` as *mapping* the `Eq` function over the row `z`.

* Rosi also supports applying a row of type functions to a single argument.
* There is currently no explicit syntax for mapping function over rows.
* Rosi's kind inference algorithm currently eagerly commits to kindings of type variables. Kind annotation can be required.

Finally, we need a label-generic way to deconstruct a variant. The Rose operator that does this is called `ana`, for *analysis*. The following example is drawn from [rolib/ro/Base.ro](rolib/ro/Base.ro)

```
eqS : forall z : R[*]. Pi (Eq z) -> Eq (Sigma z)
eqS = \ d v w. ana #(\X. X)
                    (\l y. match v
                           ( l: x -> d.l x y
                           | otherwise -> False))
                    w
```
We perform analysis on variable `w`, of type `Sigma z`. The "body" of analysis&mdash;its second argument&mdash;must be polymorphic over *any* entry in row `z`. Its type must be
```
forall l : L, u : *. {l := u} < z => #l -> u -> Bool
```
That is to say: for any label `l` and type `u` such that the singleton row `{l := u}` is contained in row `z`, a function from a singleton `#l` and a value of type `u` to a `Bool`.

But remember that we know nothing about row `z`. How can we possibly hope to provide such a function? The key is that `z` appears not just in the type of `w`, but also in the type of `z` and in the type of `d`. While we know nothing about what label `l` and type `u` are, we do know that `v` may also be built out of constructor `l`, and that `d` contains an `l`-labeled `u -> u -> Bool` function.

We can now understand the "body" of the `ana`. We start by doing a case branch on `v`. If `v` was also built with label `l`, then we select the `l`-labeled entry from `d`, and pass it the contents of `v` and `w`. In all other cases, `v` and `w` are unequal, so we return `False.` (The `False` constant is [defined](rolib/Ro/Base.ro) just as you'd expect.)

To return to our starting point, we can now define an equality function for `Bool`s by just describing how to compare the `Unit` values carried in the `'True` and `'False` cases:
```
eqBool : Eq Bool
eqBool = eqS (every (\x y. True))
```
Each field of the argument to `eqS` is the same (they all compare units), so we can use the `every` combinator to build a suitable record.

## Higher-order rows and generic programming

Another recent focus of the development of Rose is *higher-order* row typed programming.

Suppose that we are attempting to describe extensible recursive types. One approach would be via *rows of functors*. This is essentially the row-typed generalization of the description of extensible variants in Wouter Sweirstra's [Data Types à la Carte](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/data-types-a-la-carte/14416CB20C4637164EA9F77097909409).

For example, in defining an extensible expression type, we could capture the arithmetic components with a row like
```
type ArithF = { 'Const := (\t. Nat), 'Plus := (\t. Pi {'1 := t, '2 := t }) }
```
That is to say: an arithmetic term is either a constant or a sum. In the first case, it has no subdata, but does carry a natural number. In the second, it has two instances of recursive subdata, and carries no additional data.

To define actual arithmetic terms, we would use this row in a recursive variant:
```
type Arith : *
type Arith = Mu (Sigma ArithF)

aexp : Arith
aexp = 'Plus: ('Const: 0) ('Const: 1)
```
But our focus in the rest of this section is on the rows themselves, not on the mechanisms of recursive types.

* Rosi allows `Pi` and `Sigma` to be used as `R[k] -> k` constructors for any kind `k`. In this case, we use `Sigma` at kind `R[* -> *] -> * -> *`; it does the only thing that makes sense at that kind.

Not everything of kind `* -> *` is a functor. We follow Haskell's lead in describing functoriality: a functor is exactly a type constructor that has a suitable mapping function:

```
type Functor : (* -> *) -> *
type Functor = \f. forall a b. (a -> b) -> f a -> f b
```

Now, just as in the previous section, we have an opportunity to avoid some boilerplate with label-generic programming. If we know that each type constructor appearing in a row is functorial, then we should know that variants built from that row are functorial as well. We can capture this intuition with the following definition:

```
fmapS : forall z : R[* -> *] .
        Pi (Functor z) -> Functor (Sigma z)
fmapS = \ d. /\ a b. \ f w.
        ana #(\x. x a)
            (\ l x. l: (d.l f x))
            w
```

The type of `fmapS` follows the same pattern as the type for `eqS`, using a dictionary of the mapping functions for `z` to build a mapping function for `Sigma z`.

The implementation of `fmapS` begins by abstracting over the record of mapping functions `d`, and then follows the type of `Functor (Sigma z)`, binding types `a` and `b`, the function `f`, and the variant `w` of type `Sigma z`.

* We do not actually need to bind type variable `b` here, but do so for clarity.

Next, we define a label-generic traversal of `w`. In the body of the `ana`, we are given its constructor `l` and contents `x`. We obtain the mapping function for `x` by getting the `l`-labeled entry in `d`; we then provide this mapping function with the argument `f` and contents `x`. Finally, we build a value of the result type by rewrapping it in constructor `l`.

* Note that the result of `d.l` is polymorphic; its instantiation with `a` and `b` is implicit.

There is one substantial complication. The type of `w` is not just `Sigma z`—which, remember, has kind `* -> *`, but is actually of type `(Sigma z) a`. This type simplifies to `Sigma (z a)`; that is to say, to a variant built from applying each type constructor in `z` to `a`. However, `d` is defined over row `z`, not over row `z a`!

To mediate situations like this, `ana` is given a type function argument, which function is then applied to the row `z` in the type of the body. Concretely, in this case, the body must have type

```
forall l : L, u : * -> *. {l := u} < z =>
           #l -> (\x. x a) u -> (Sigma z) b
```

where we have left the type application unreduced for emphasis. Understood this way, the body of the `ana` is equipped with the assumptions necessary to select from `d`.

* This dance might seem unnecessary: surely if we know that `{l := u} < z a`, then we know that `l` labelling something appears in `z`? Unfortunately, Rosi is not yet able to refine quantified types based on predicates over them, and so cannot refine the `u` to an application `u' a` for some new quantified type `u'`.

More discussion of these examples, including the dual account for records, is in the paper [Generic Programming with Extensible Data Types](https://doi.org/10.1145/3607843). More variations of these operators are contained in the [Ana.ro](examples/Ana.ro) and [Syn.ro](examples/Syn.ro) examples.

# The Rose Language

Finally, we have some otherwise unorganized notes on the language as implemented (or not) by Rosi.

## Other language features

Rosi supports an arbitrary fixed point operator `fix : forall a. (a -> a) -> a`

Rosi's type inference mechanism attempts to support first-class polymorphism. Initial results are promising (such as the instantiations in the functor example), although some gaps remain. See [examples/Poly.ro](examples/Poly.ro) for the current state.

## Rosi's type errors

Rosi's primitives on records and variants are highly polymorphic, and errors in their use generally arise as failures to solve predicates. For a simple example, consider:

```
broken : Pi {'A := Unit, 'B := Unit} -> Unit
broken = \x. sel x #'C
```

which attempts to project a missing field from a record. The error reported here is that the predicate `{C := Unit} < {'A := Unit, 'B := Unit}` is not entailed. This is because the type of `sel` itself is polymorphic: it works for any singleton row contained in the type of `x`, and checking whether the record we need is such a record is handled by Rosi's predicate solver.

As a further aid to users, Rosi does not yet track the origin of predicates. So, the error message that arises from this definition gives no clue as to which expression gave rise to the unsolvable predicate.
