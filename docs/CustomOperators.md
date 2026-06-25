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

If there is no fixity declaration, the operator gets the default fixity and precedence, which is `infixl 9`.

Fixity declarations must appear at the top level. If an operator is bound in a let or lambda binding, it gets the default fixity, even if there is a top-level fixity declaration for the same symbol in the same file.

You can define a fixity for a backticked identifier as well, (as long as it is defined in the same file).

```
infixr 3 `cons`
```

- In general, a definition/declaration pair in the current file/module will be used before a definition/declaration pair in an imported module.
- If multiple imported files contain definitions for the same identifier, and the current file does not, it is currently unpredictable which definition will be used. However, the fixity declaration is tied to the term definition, so we can expect that the fixity declaration which is ultimately used will be from the same module as the term definition.


## Precedence Rules

- Left or right associativity applies when two `infixr` or `infixl` expressions have the same precedence level.



- A prefix always binds tighter than an infix to its left, and vice versa for postfix. So, in `P \/ ! Q`, `!` must apply to `Q`, even if `\/` has higher precedence, but in `! P \/ Q`, the relative precedence determines whether it's `(! P) \/ Q` or `! (P \/ Q)`.

- Expressions containing ambiguous combinations of operators will be rejected. This includes:
  - An expression between a `prefix` and `postfix` operator of the same precedence.
  - An expression between a `infixl` and `infixr` operator of the same precedence.
  - An expression between two `infix` operators of the same precedence.

- When one or more `prefix` operators appear in front of an expression, and one or more `postfix` operators appear after, they are resolved from the inside out, even if the outer operators have higher precedence than the inner ones of the same fixity.
In this example, assume that `$`, `$$`, and `$$$` are `prefix`, while `%`, `%%`, and `%%%` are `postfix`, with each set having precedences 1, 2, and 3, respectively.
  
```
  -- first we compare $ with %%. %% has higher precedence
  $$$ $ x %%
  -- then we apply the innermost prefix operator.
  $$$ ($ (x %%))
  -- then finally the remaining prefix operator.
  ($$$ ($ (x %%)))
```
