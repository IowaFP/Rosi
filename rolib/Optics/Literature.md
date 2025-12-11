Reading list

# Bidirectional transformations
- Introduction to BX
    - https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/ssbx-intro.pdf
- Combinators for Bidirectional Tree Transformations: A Linguistic Approach to the View-Update Problem
    - https://dl.acm.org/doi/pdf/10.1145/1232420.1232424

# Symmetric lenses & complements
- Symmetric Lenses
    - https://www.cis.upenn.edu/~bcpierce/papers/symmetric.pdf 
- Complements Witness Consistency
    - https://groups.inf.ed.ac.uk/bx/2016-Bx-CWC.pdf
-  Three Complementary Approaches to Bidirectional Programming.
    Provides a good explanation of the utility of complements.
    - https://janis-voigtlaender.eu/papers/ThreeComplementaryApproachesToBidirectionalProgramming.pdf

# Lenses *without* combinators
- HOBiT: Programming Lenses Without Lens Combinators.
    This may be a promising avenue of Rosi if we can realize BX sans combinators
    - https://mengwangoxf.github.io/Papers/ESOP18.pdf
- Applicative Bidirectional Programming with Lenses
    This is closer to the mark for us.
    - https://www2.sf.ecei.tohoku.ac.jp/~kztk/papers/kztk_icfp2015.pdf

# Profunctor optics
- What you need to know about Yoneda:
    - https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf
- Profunctor Optics: Modular Data Accessors
    (fairly accessible and implementation oriented)
    - https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/poptics.pdf
- Bartosz Milewski on optics:
    - https://bartoszmilewski.com/2022/04/05/teaching-optics-through-conspiracy-theories/
- Invariant functor optics (easier to digest profunctors):
    - https://dl.acm.org/doi/pdf/10.1145/3191697.3191718

# Library documentation
- Using Haskell's Generic to derive lenses, prisms, etc.
    A wealth of good examples.
    - https://dl.acm.org/doi/pdf/10.1145/3236780

# Dependent lenses
- Secondary reading that may be relevant to dependent rows
    - https://www.cse.chalmers.se/~nad/publications/danielsson-dependent-lenses.pdf
    - https://www.cse.chalmers.se/~nad/publications/capriotti-danielsson-vezzosi-higher-lenses.pdf

# Open problems in BX
- Towards a Repository of Bx Examples
    - https://www.cs.ox.ac.uk/jeremy.gibbons/publications/repo.pdf
    http://bx-community.wikidot.com/examples:home
- Benchmarx:
    - https://ris.utwente.nl/ws/portalfiles/portal/5301511/bx2014.pdf
- Benchmarx Reloaded (2017): 
    - https://ceur-ws.org/Vol-1827/paper6.pdf
- Benchmarx 2.0 (for concurrent model synchronization), 2024: 
    - https://dl.acm.org/doi/pdf/10.1145/3652620.3688217
- Provenance meets Bidirectional Transformations: 
    - https://www.usenix.org/system/files/tapp2019-paper-anjorin.pdf

# The Van Laarhoven Representation
The Data.Lens package represents a lens as:
    type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t
Some reading:
- Functor is to Lens as Applicative is to Biplate:
    - https://arxiv.org/pdf/1103.2841
- CPS based functional references:
    - https://www.twanvl.nl/blog/haskell/cps-functional-references

# Research questions
- This section from Pickering et al strikes me:
    - "Prisms are an implementation of first-class patterns, unlike other proposals; for example, Tullsen
    [37] recognised the close connection between data constructors and pattern matching.
    Pattern matching is the method which is used to deconstruct values constructed by
    data constructors; first-class patterns should also be able to re-build the values that
    they match."

