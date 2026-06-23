# Custom Operators

Rosi supports programmer-defined custom operators.

## Syntax

Any consecutive sequence of operator symbols will be interpreted as an operator symbol. An operator symbol is any of `":+-*\\/=?|&><!$%^~"`. This is almost the same set supported by Idris 2, but we omit `.`, `#`, and `@`, which are reserved for built-in Rosi syntax.

As in Haskell:

- Surrounding an operator symbol means it will be parsed like an ordinary variable. (e.g. `(::) x xs` is the same as `cons x xs`)
- Surrounding a regular identifier with backticks `` ` `` goes the other way, turning the identifier into an operator, so ``x `cons` xs`` equals ``x::xs``

## Operator definitions

- Operators must be defined in surrounded form, in an ordinary top-level function declaration.

```
(::) = cons
```

or

```
(::) x xs = cons x xs
```

## Fixity Declarations

A fixity declaration has the form:

```
infixl | infixr | infix |  prefix | postfix <number> <operator>
```

e.g.

```
infixl 5 (+)
infixr 3 (::)
infixr <number> <operator>
```

A fixity declaration must appear in the same file as the operator's definition.

<!-- TODO(mctano) confirm this is the default fixity that we we want. Consider requiring a fixity declaration in all cases. -->
If there is no fixity declaration, the operator gets the default fixity and precedence, which is `infixl 9`.

You can define a fixity for a backticked identifier as well, (as long as it is defined in the same file).

```
infixr 3 `cons`
```

- In general, a definition/declaration pair in the current file/module will be used before a definition/declaration pair in an imported module.
<!-- TODO(mctano) Does the claimed consistency rely on the lookup procedures in Scope and in FixityResolution being the same? -->
- If multiple imported files contain definitions for the same identifier, and the current file does not, it is currently unpredictable which definition will be used. However, the fixity declaration is tied to the term definition, so we can expect that the fixity declaration which is ultimately used will be from the same module as the term definition.

## Precedence Rules

- Prefix and postfix operators always take precedence over infix operators.
- Associativity applies when two `infixr` or `infixl` expressions have the same precedence level.
- The precedence level for `prefix` and `postfix` operators only matters when an expression appears between a prefix and postfix operator.
- Expressions containing ambiguous combinations of operators will be rejected. This includes:
  - An expression between a `prefix` and `postfix` operator of the same precedence.
  - An expression between a `infixl` and `infixr` operator of the same precedence.
  - An expression between two `infix` operators of the same precedence.
  - Expressions involving `prefix` and `postfix` operators which, after applying the operators, contain adjacent expressions. e.g.

    ```
    -- $ is a prefix operator which stands for the identity function
    prefix 5 $
    ($) : a -> a
    ($) = id
    
    -- not allowed
    $ f $ g

    -- okay
    ($ f) ($ g)
    ```

- When multiple `prefix` operators appear in front of an expression, and multiple `postfix` operators appear after, they are resolved from the inside out, even if the outer operators have higher precedence than the ones of the same fixity.
  For this example, assume that `$`, `$$`, and `$$$` are `prefix` with precedence 1, 2, and 3, respectively, and the corresponding `%`, `%%`, and `%%%` operators are likewise `postfix`.
  
  ```
    -- first we compare $ with %%. %% has higher precedence
    $$$ $ x %%
    -- then we apply the innermost prefix operator.
    $$$ ($ (x %%))
    -- then finally the remaining prefix operator.
    ($$$ ($ (x %%)))
  ```
