# Subtyping As Polymorphism

The goal of these notes is to outline a response to Tang et al.'s 2023 OOPSLA paper, [*Subtyping As Parametric Polymorphism*](https://arxiv.org/pdf/2304.08267), which explores possible translations from source calculi equipped with various subtyping relations, to target calculi with row- or presence-polymorphism.

We will first clarify exactly what results are claimed by Tang et al., then explore what kinds of translations can be made to work in Rosi.

## Tang et al.'s Results

It is important to be precise in summarizing the results of the Tang paper, to avoid mistating or overgeneralizing the claims therein.

There are a number of both positive and negative results stated, each of which is stated formally about a specific source calculus and target calculus.

### Definitions

#### Source and Target Calculi

The source calculi are subject to the following limitations:

* The source calculi all contain explicit upcasts wherever a value of a subtype is used as a value of its supertype.
* The source calculi do not support polymorphism, so the records and variants they contain are always fully concrete. Therefore it is always straightforward to determine whether the subtyping relation holds.

Additionally, the source calculi may contain records, variants, or both, and those records or variants may be subject to a rank restriction, which is defined as follows:

> We say that a type has rank-n records, if no path from the root of the type (seen as an abstract syntax tree) to a record type passes to the left of n or more arrows.

"Rank-n variants" are defined similarly.

The source calculi also include a subtyping relation, according to which
which, a sub-record can contain extra fields, and a sub-variant can omit constructors. This relation is either:

1. Simple, meaning all types appearing in matched fields must be identical.
2. Strictly covariant, meaning the simple subtyping relation is lifted through covariant positions only. i.e. `(A -> B) < (C -> D)` if `B < D` and `A = C`.
3. Full, meaning the subtyping is inductively propagated through all positions of complex types, but reversed in contravariant positions. i.e. `(A ->B) < (C -> D)` if `A > C` and `B < D`.

The function arrow is the only type constructor in the source calculi, and stands in for arbitrary type constructors, for which the subtyping rules can easily be extended, based on the covariance or contravariance of their parameters.

Likewise, the target calculi contain records or variants, and are equipped with row polymorphism or presence polymorphism. For some calculi, this is restricted to rank-1 polymorphism.

#### Classes of Translations/Encodings

[Note: The terms "translation" and "encoding" are used interchangeably.]

Translations are characterized as either "Type-Only" or "Term-involved". They are also characterized as either "local" or "global", depending on whether they can be accomplished with changes only to parts of a program that relate to variants or records.

*Note that a "type-only" encoding also counts as "term-involved", and a "local" encoding also counts as a "global" one. Therefore, a fortiori, the existence of a local, type-only encoding implies the existence of a global, term-involved encoding, and the non-existence of global, term-involved encoding implies the non-existence of a local, type-only encoding.*

The strongest positive result stated by Tang et al. is that a local, term-involved translation exists from a calculus with full subtyping to a target calculus with neither subtyping nor polymorphism.

This translation (which they credit to earlier work by Pierce 2002, and Breazu-Tannen et al., 1991) replaces upcasts with explicit destruction and reconstruction of records, and explicit branching on variants. (My intuition is that this translation may not be possible in a language which includes both subtyping and some form of polymorphism or generics, since it relies on statically knowing the exact structure of the record or variant involved).

### Results

#### Simple Subtyping Results

Regarding the simple subtyping relation, Tang et al. state the following positive results: (identified by section number, rather than theorem number, since there are multiple theorems covering each translation).

*4.1 A Local, term-involved encoding of simple variant subtyping ***without*** polymorphism.*

*4.2 A local, type-only encoding of simple variant subtyping with row polymorphism.*

*4.3 A local, term-involved encoding of simple record subtyping ***without*** polymorphism.*

*4.4 A local, type-only encoding of simple record subtyping with presence polymorphism.*

They also state the following negative result, addressing the question of whether we can swap row and presence polymorphism to handle records and variants, respectively:

*4.5 There exists no global type-only encoding of simple record subtyping (to a target calculus) with row polymorphism, and no global type-only encoding of simple variant (in the target calculus) with presence polymorphism.*

##### Aside

We should be careful to avoid reading this result too broadly, as the actual theorem (Theorem 4.9 in the paper) is stated with respect to specific target calculi. As regards row polymorphism, it may be fair to interpret it as stating that we cannot give a type-only encoding of records with **only row polymorphism**, but even that should be understood with the caveat that this conclusion is limited to **the specific target calculus with row polymorphism**. This does not imply that presence polymorphism is necessary to give such a translation, since there may be some other language feature we could add to row polymorphism instead of presence polymorphism that would solve the problem. And depending what that feature is, it may be debatable whether what we have in that case is really **row polymorphism + X**, or just a different formulation of row polymorphism.

Only 1 out of the 3 proofs given for Theorem 4.9 depends on the requirement that the translation be type-preserving. As Tang et al. acknowledge, "this assumption can be too strong". One benefit of a parametric or row-polymorphic approach over subtyping is the ability to write functions over a structural subtype which preserve additional information in the return type. For example, a `rename` function which takes in a record, and returns the same record type. With only subtyping, we would have to "forget" everything but the name field in the return type. If a row polymorphic translation was able to preserve this additional information in a way that did not compromise the rest of the program, we would not want to reject the translation on that basis. Tang et al. recognize this, and instead prove a "weak type preservation" property for their translation in section 6, which merely requires that all terms in the translated program be well typed.

#### Strictly Covariant Subtyping Results

Regarding Strictly covariant subtyping, Tang et al. give the following positive result:

*5.2 A global type-only encoding of strictly covariant record subtyping in with presence polymorphism.*

along with these negative results:

*5.3 There exists no (global) type-only encoding of strictly covariant variant subtyping (to a target calculus) with (only) row polymorphism and variant polymorphism.*

Note that 5.3 also rules out the possibility of encoding full variant subtyping using (only) row polymorphism and record

#### Full Subtyping Results

The following previously mentioned positive result, credited to Pierce [2002] and Breauzu-Tannen et al. [1990].

*5.1 A local term-invvolved encoding of full record and variant subtyping without any polymorphism.*

Note that this implies that this local, term-involved encoding is also available for languages that do possess row or presence polymorphism.

There is also a negative result:

*5.4 There exists no (global) type-only encoding of full record subtyping (to a target calculus) with (only) row polymorphism and presence polymorphism.*

Note: The proof of result 5.4 (Theorem 5.4 in the paper) depends on type preservation, and, unlike Result 4.5, there is no alternative proof given which does not depend on type preservation. It may be worth taking a look to see if this leaves open the possibility of a non-type-preserving translation.

Finally, the paper gives its primary positive result.

*6.1 A local, type-only encoding of full subtyping from a source calculus with rank-2 records, to a target calculus with rank-1 presence polymorphism.*

The following related results are also stated regarding variants.

*6.2 A local, type-only encoding of full subtyping from a source calculus with rank-1 variants, to a target calculus with rank-1 row polymorphism.*

*6.2 A local, type-only encoding of full subtyping from a source calculus with rank-2 variants, to a target calculus with rank-1 presence polymorphism.*

(I'll need to think about why Result 6.2 is possible notwithstanding Result 4.5)

The purpose of restricting the target calculus to rank-1 polymorphism is to keep type inference for the target calculus decidable, so that upcasts and type annotations can simply be erased during the translation. As we will see, some of the challenges to giving a type-only translation is in knowing what type applications need to be inserted to replace upcasts.

## Tang et al.'s Examples

### 2.1 Simple Variant Subtyping as Row Polymorphism

Simple record subtyping is easily encoded in the target calculus with row polymorphism.

The following function expects a variant with two cases.

```haskell
getAge : Sigma {'Age := Nat, 'Year := Nat} -> Nat
getAge = \x. (match x ('Age: y -> y
                      |'Year: y -> 50 - y))
```

We have a variant whose type is declared as just one of those cases:

```haskell
year : Sigma {'Year := Nat}
year = 'Year: 11
```

We want to translate the following application of `getAge` to the upcast value `year`.

```haskell
getAge (year |> Sigma {'Age := Nat, 'Year := Nat})
```

In Tang's encoding, the type of `year` is made row polymorphic, so that it accepts a row parameter describing the additional cases. Then, at the call site, the upcast is replaced by an explicit type application, passing the row containing the missing case expected by `getAge`.

The Rosi equivalent of the Tang encoding is as follows:

```haskell
year' : forall d. Sigma ({'Year := Nat} + d)
year' = 'Year: 11

-- Rosi is able to infer the row argument if we omit it
ex_1 = getAge (year' @{'Age := Nat})
```

However, In Rosi, we can instead leave year monomorphic, and directly replace the upcast with `inj`.

```haskell
ex_2 = getAge (inj year)
```

### 2.2 Simple Record Subtyping as Presence Polymorphism

Since our language does not use presence polymorphism, the translation to presence polymorphism is not particularly relevant to us, except to show that our language can handle the examples given without presence polymorphism.

### 2.3 Exploiting Contravariance? (Why we can't use row polymorphism for record subtyping.)

This counterexample is a preview of the proof of Result 4.5.

```haskell
getName : Pi {'Name := String} -> String
getName x = x :/ 'Name

alice : Pi {'Name := "Alice", 'Age := 9}
alice = ('Name := "Alice", 'Age := 9)

getName (alice |> Pi {'Name := "Alice"})
```

Tang et al show that this example cannot be given a composable translation to their target calculus with row polymorphism.

Their proposed translation is basically this:

```haskell
getName' : forall r. Pi ({'Name := String} + r) -> String
getName' x = x.'Name


getName @{'Age := Nat} alice
```

`getName'` is parameterized over the extra fields of `x` polymorphic, so that it can take any record which contains `{'Name := String}`. The row argument `{'Age := Nat}` is explicitly passed at the call site. The main difference is that they use a normal record access operator, unlike Rosi's dot access operator, which desugars to the 2-step process of projecting out and then unlabeling a single field (`(prj x) :/ 'Name`).

However, they argue that this translation does not work, because the translation needs to be aware that the row argument `{'Age := Nat}` must be passed to `getName'` at the call site to replace the upcast, but for the translation to be composable, the result must be based only on the type of `getName` and `alice |> {'Name := "Alice"}`. These don't tell us what extra fields are present in `alice` before the upcast.

Something feels a bit funny about this example. The upcast focuses on the fields which must be present to make the application legal, but the target calculus requires that we instantiate the polymorphic function with the fields that we are going to ignore.

In Rosi, the above translation actually works fine. Furthermore, in Rosi, we have another option, which is to replace the upcast directly with `prj`.

```haskell
getName (prj alice)
```

The Rosi version does not require the type argument at the projection, since it is based on the type of `alice` and the type required by `getName`. However, if we were to make the projection operator more explicit, then it ought to be parameterized by the fields that we want to project out of `alice`; rather than by the fields that we want to discard.

I believe that this is actually the key point. In the source calculus, the upcast refers to the fields of the record which are remembered when passed to the function, but the target calculus requires knowledge of the fields which must be forgotten. This mismatch makes the translation more difficult to accomplish. On the other hand, we can directly translate the simple (shallow) upcast as `prj` in Rosi, because Rosi doesn't need to be told about the fields which we are going to ignore.

[NOTE: Is what I've said here actually accurate with respect to how type inference works in Rosi?]

### 2.5 Strictly Covariant Record Subtyping as Presence Polymorphism

Presence polymorphism Bob Loblaw.

### 2.6 No Type-Only Encoding of Strictly Covariant Variant Subtyping as Polymorphism

The problematic example in this section is based on a requirement that a case split in the target calculus requires a monomorphic value.

">"The difficulty with encoding `parseAge` with row polymorphism is that the abstraction of the row variable for the inner record of data✗ is hoisted up to the top-level, but case split requires a monomorphic value. Thus, we must instantiate 𝜌2 with Age : Int before performing the case split." - Tang et al, p. 10

However, this is not a problem for us, because our case branching construct does not require a monomorphic value.

### 2.7 No Type-Only Encoding of Full Record Subtyping as Polymorphism

The examples in this section address the problem of upcasting functions, taking into account contravariance of types in argument position.

I will need to analyze this in more detail, but the initial problems seem to be with the bureaucratic restrictiveness of presence and row polymorphism in the target calculus.

In any case, the particular examples in this section are no problem for Rosi:

```haskell
getUnit : Pi {'Name := String} -> Unit
getUnit = \x. prj x

getUnit_upcast : Pi {'Name := String, 'Age := Int} -> Unit
getUnit_upcast = getUnit . prj
```

## Additional Problematic Examples

Since we are able to handle most of the examples in section 2 in multiple ways, we will need more complicated examples to illustrate where the difficulties arise in the Rosi translation. These will mainly involve more deeply nested ("higher rank") records and variants.

## Replacing Upcasts with prj and inj (shallowly)

To encode simple subtyping, we can simply replace all upcasts with `prj` for records, or `inj` for variants.

To replace an upcast of a function, as long as it is only based on simple subtyping of the argument and return type, we can simply pre- or post- compose with `inj` or `prj`, depending whether the argument or return types are records or variants.

```haskell
pRet : Unit -> Pi y
pRet = const ('1 := tt, '2 := tt)

pRet_upcast : Unit -> Pi x
pRet_upcast =  prj . pRet
```

[See `SubtypingAsPolymorphism.ro` for more examples.]

I think this is composable, but it doesn't really matter because this doesn't work if the argument or return types contain nested records or variants.

## Sketch of a Translation for Full Record and Variant Subtyping

To be developed further.

The general idea is that we just parameterize all record or variant arguments over a row, with the appropriate constraint.

```haskell
getChildName : Pi {'Child := Pi {'Name := String}} -> String
getChildName = \ x. (x :/ 'Child) :/ 'Name

-- translates to
getChildName_deepPoly : {'Name := String} < r, {'Child := Pi r} < r' => Pi r' -> String
getChildName_deepPoly = \x. x.'Child.'Name
```

TODO: Develop an actual set of rules.

## Composability of translation rules

TODO: Make an argument that the above rules compose.

* Add a note about the ambiguity of the middle step of a double-`prj` and how it may cause a problem for composability if the encoding ever results in `prj . prj`

## Next Steps

* Examine Ningning Xie's paper on disjoint polymorphism and see how it relates to what we've explored here.
