# Proof-Oriented Programming in F\*: notes

# I. Introduction

## 1. A Capsule Summary of F\*

# II. Programming and Proving with Total Functions

- the type of a term is a specification of its runtime behavior
- `e : t` means `e` has type `t`
- many terms can have the same type and a term can have many types
- useful read: propositions as types

## 2. Getting off the ground

- Download the latest release of F\*
- VS Code with the fstar-vscode-assistant extension

Basic module structure with some examples syntax:

```fs
(*

    An F* program is a collection of modules,
    with each module represented by a single *.fst file.
    It's possible to define module interfaces
    in separate *.fsti files to hide implementations.

*)
module A // Must correspond with A.fst

// Syntax to use external modules
open FStar.Mul

// The type of natural numbers is defined as
// integers greater than or equal to zero
let natural = x: int { x >= 0 }

// The type of positive numbers is defined as
// natural numbers greater than zero
let positive = x: natural { x > 0 }

// Signature for factorial where
// - the input must be a natural number (at least 0)
// - the output must be a positive number (at least 1)
val factorial (n: natural) : positive
let rec factorial n = // Implementation of factorial
    if n = 0
    then 1
    else n * factorial (n - 1)

val increment (n: natural) : p: int { p = n + 1 }
let increment = fun n -> (n + 1 <: positive)
```

### 2.4. Primitives

- the `False` type has no elements and represents the type of unprovable propositions
- the `unit` type has a single element denoted `()`

#### 2.4.3. Booleans

The `bool` type has two elements: `true` and `false` (note the lowercase).
The following primitive boolean operators are available in F\*:
- `not` (prefix to negate a boolean value)
- `&&` boolean conjuction (logical and)
- `||` boolean disjunction (logical or)

The `factorial` snippet also shows the use of conditionals:
```fs
if b // b: bool
then ... // b = true case
else ... // b = false case

if b then ... else ... // one-line notation
```

#### 2.4.4. Integers

The type `int` represents the infinite set of integers, which includes all negative and positive whole numbers, as well as zero itself.
The following primitive integer operations are available in F\*:
- `-` negation (prefix)
- `-` subtraction (infix)
- `+` addition
- `/` Euclidean division
- `%` Euclidean modulus
- `op_Multiply` multiplication (open the `FStar.Mul` module to use `*` for multiplication)
- `<` less than
- `<=` less than or equal to
- `>` greater than
- `>=` greater than or equal to
- `=` equals

### 2.5. Boolean refinement types

In the factorial snippet, the syntax `x: t { e }` denotes a *boolean refinement*, which you can think of as type constraints or as propositions.
The `natural` type refines the `int` type such that all integers `x` which satisfy the condition `x >= 0` are valid elements of `natural`.
The `positive` type further refines the `natural` type such that all naturals `x` which satisfy the condition `x > 0` are valid elements of `positive`.
Boolean refinements are a special case of a more powerful form of *propositional refinement* in F\*.

### 2.6. Functions

The syntax snippet also features several functions.
The `factorial` and `increment` functions are *named*, but the `increment` function is implemented using a *lambda term*.
The `factorial` function has a *recursive* definition, which means that it calls itself in the implementation.
The `e <: t` operator denotes a *type ascription*, which tells the F\* compiler to check if the expression `e` has the type `t`.

### 2.7. Arrow types

As F\* is a functional programming language, functions are its main strength.
But functions themselves are also *types* of the shape `x: t0 -> t1`.
This denotes a type of function that receives an argument `e` of type `t0` and which returns a value of type `t1[e/x]` (meaning the type of the returned value depends on the argument).

It's important to note that F\* is a *dependently typed* programming language, so `t1[e/x]` allows a function to return a `bool` when the argument is an even number and returns a `string` when the argument is an odd number.
Moreover, all functions in F\* are *total*, which means that a function call always terminates after consuming a finite but unbounded amount of resources.
Concretely, this means that a function will never need an *infinite* amount of memory to execute, even though it could theoretically exhaust all the memory of your machine or even that of the entire cloud infrastructure on Earth.

#### 2.7.1. Some examples and common notation

```fs
// Currying
val (+): int -> int -> int

// Refinements
val (/): int -> (divisor: int { divisor <> 0 }) -> int
val f_verbose : x: (x: int { x >= 1 }) -> y: (y: int { y > x }) -> z: int { z > x + y }
val f_concise : x: int { x >= 1 } -> y: { y > x } -> z: int { z > x + y }

// Dependence between input and output values
val increment_simple: int -> int
val increment_stricter: x: int -> y: int { y > x }
val increment_strictest: x: int -> y: int { y = x + 1 }

// Function totality (no side-effects) implied by default
val f_total : x: int { x >= 1 } -> y: int { y > x } -> Tot (z: int { z > x + y })
```

Functions are *curried*, which means that a function of type `t0 -> t1 -> t2` is equivalent to a function of type `t0 -> (t1 -> t2)`.
In other words, a function with multiple inputs is like a chain of single-argument functions which themselves return a function.

```fs
// Currying intuition
val add : int -> int -> int
let add x y = x + y
let addFive = add 5 // f(x) = x + 5
let eight = addFive 3 // f(3) = 3 + 5 = 8
```

### 2.8. Exercises

1. Download the latest binaries from [GitHub](https://github.com/FStarLang/FStar/releases)
2. 

See file `Part1.GettingOffTheGround.fst`.

## 3. Polymorphism and type inference

### 3.1. Type: The type of types

F\*, like many other dependently typed languages, treats programs and their types uniformly within a single syntactic class.
A type system like this is sometimes called a *Pure Type System* (PTS).
Types themselves have types too, functions can take types as arguments and return types as results and so on.
The most fundamental type is `Type`, the type which every type has.

### 3.2. Parametric polymorphism or generics

F\* lets you write so called generic or polymorphic functions by allowing types themselves to be used in the arrow notation.
For example, the identity function which simply returns its argument, can be written generically to include type information.

```fs
// A few ways to write the identity function
let id: a: Type -> a -> a = fun a x -> x
let id (a: Type) (x: a) : a = x

// Example usages
let _ : bool = id bool true
let _ : nat = id nat 5
let _ : int -> int = id (int -> int) (id int)
```

### 3.3. Exercises

Type arguments can be used to indicate the type of other arguments.
Consider the following exercises:

```fs
// Apply returns a function which:
// - accepts an input of type a
// - yields an output of type b
// For this, Apply expects the type arguments for a and b
// as well as an appropriately typed function from a to b.
val apply (a b: Type) (f: a -> b) : a -> b
let apply a b f = fun x -> f x

// Compose return a function which:
// - accepts an input of type a
// - yields an output of type c
// For this, Compose expects the type arguments for a, b and c,
// where b is an intermediate type to allow composition,
// as well as two appropriately typed functions to be composed.
val compose (a b c: Type) (f: b -> c) (g: a - > b) : a -> c
let compose a b c f g = fun x -> f (g x)

// Applying the same function twice on one argument
val twice (a: Type) (f: a -> a) (x: a) : a
let twice a f x = compose a a a f f x
```

### 3.4. Type inference: Basics

F\* has *type inference* like many other languages, but it uses [*higher-order unification*](https://en.wikipedia.org/wiki/Unification_(computer_science)#Higher-order_unification) to fill in even more gaps than just type annotations.

Consider the `id` function again:

```fs
let id (a: Type) (x: a) : a = x

let _ : bool = id bool true
let _ : bool = id _ true    // 'true' implies 'bool' type
let _ : nat = id _ 5        // 5 implies 'nat' type
let _ : string = id _ "x"   // "x" implies 'string' type
```

The underscore represents a "hole" in the program to be filled in by the compiler.

### 3.5. Implicit arguments

It's possible to clean up the function definition so that you can omit those underscores using *implicit arguments*.
Let's revisit the `id` function and see what difference implicit arguments can make.

```fs
let id (#a: Type) (x: a) : a = x // # means implicit

// No more underscores for 'a'
let _ : bool = id true
let _ : nat = id 5
let _ : string = id "x"

// But you can still specify if you want
let _ = id #nat 0
let _ = id #(x: int { x == 0 }) 0
let _ = id #(x: int { x <> 1 }) 0
```

## 4. Equality

Two main types of equality which are important when writing F\* programs are *decidable equality* and *propositional equality*.
There are more types of equality, but they are covered in a later chapter and in more depth.

### 4.1. Decidable equality and `eqtype`

Decidable equality is written using the *boolean equality* operator, like so: `(e1 = e2) : bool`.
Not all types support decidable equality; if you have two functions `f1 f2: nat -> nat`, you would have to check if they evaluate to the same result for all natural numbers.
Since this would require checking an infinite number of elements, this is not feasible, or more specifically, not decidable.

Types that do support decidable equality all have the `eqtype` type.
This means that if `e1 e2: t`, it only makes sense to write `e1 = e2` if `t : eqtype`.
The decidable equality operator is therefore defined as: `val ( = ) (#a: eqtype) (x: a) (y: a) : bool`.

### 4.2. Propositional equality

Another type of equality in F\* is *propositional equality*, which is written using the `==` operator.
Rather than returning a boolean, propositional equality returns a proposition that `e1 e2: t` might be equal.
Unlike decidable equality, propositional equality is defined for all types, and it is defined as: `val ( == ) (#a: Type) (x: a) (y: a) : prop`.

## 5. Interfacing with an SMT solver

In academia, if you treat *propositions as types*, then a term of a certain type is a proof of the proposition.
F\* is no different, but it is not the only way to prove such theorems.
Consider the expression `17 : x: int { x >= 0 }`, which you can think of as proving the proposition "17 is an integer greater than or equal to 0."
Mathematically speaking, this would usually require proving the existence of integers and proving that comparisons can exist on them, yet the compiler does not complain.

In fact, F\* relies on an *SMT (Satisfiability modulo theories) solver* to prove if the formula `17 >= 0` is true given some context and facts about the program.
If the solver is able to prove it to be valid, F\* accepts it as true without needing an explicit proof.

Decoupling the proof term from a type using an SMT solver has a few consequences:

- **trust**: SMT logic is mathematically sound
- **proof irrelevance**: if the SMT solver can prove a fact in one way, any other proofs are lumped together
- **subtyping**: since no proof term is constructed, a term can have multiple types, which leads to refinement types
- **undecidability**: formulas to be checked in F\* do not have to be simple booleans or integers, as long as the SMT solver can type check the terms

Propositional logic comes with a few additional operators:

- `p /\ q` Conjunction (and)
- `p \/ q` Disjunction (or)
- `~p` Negation (not)
- `p ==> q` Implication
- `p <==> q` Bi-implication
- `forall` Universal quantifier
- `exists` Existential quantifier

```fs
// Proposition:
// For all natural numbers x and y
// such that the modulus x % y equals 0
// there exists a natural number z
// such that x * y = z.
forall (x: nat) (y: nat). x % y = 0 ==> (exists (z: nat). x = z * y)
//                      ^                               ^
//                      such that                       such that
```

### 5.1. Propositions

The proposition type `prop` is an F\* primitive, which represents the type of facts which are provable using the SMT solver (proof-irrelevant propositions).
Propositions, unlike booleans, do not need to be decidable.
This means that F\* will sometimes convert booleans into propositions, for example when a proposition requires you to define things that cannot be defined in booleans, such as *quantified formulas*.

### 5.2. Propositional connectives

Here are a few ways to describe properties about the factorial function:

```fs
// Refinement type
val factorial (n: nat) : x: nat { x > 0}

// Universal quantifier (proposition)
forall (n: nat). factorial n > 0

// Existential quantifier:
// There exists a natural number
// for which factorial n
// is greater than n * n
exists (n: nat). factorial n > n * n
```

#### 5.2.1. Quantifiers

The universal quantifier `forall (x1: t1) ... (xn: tn). p` only holds if the proposition `p` is valid for all `v_i` of type `t_i`, i.e. all values which can be passed into the function as arguments.

The existential quantifier `exists (x1: t1) ... (xn: tn). p` only holds if the proposition `p` is valid for some `v_i` of type `t_i`.

The validity of a proposition can change depending on the types used.
F\* has type inference, but in some cases, you might want to be more explicit to ensure correctness.

```fs
exists (x: int). x < 0 // Proposition holds for all values < 0
exists (x: nat). x < 0 // Proposition does not hold, because 0 is the smallest nat
```

It is also possible to quantify over any F\* type to create higher order and dependent quantifiers:

```fs
// Here, p is a function
// that takes a nat and
// returns a prop
forall (n: nat) (p: (x: nat { x >= n } -> prop)). p n
```

#### 5.2.2. Conjunction, Disjunction, Negation, Implication

| Name | Operator | Usage | Boolean equivalent |
| ---- | -------- | ----- | ------------------ |
| Negation | `~` | `~p` | `not` |
| Conjunction | `/\` | `p /\ q` | `&&` |
| Disjunction | `\/` | `p \/ q` | `\|\|` |
| Implication | `==>` | `p ==> q` | n/a |
| Double Implication | `<==>` | `p <==> q` | n/a |

### 5.3. Atomic propositions

You can use connectives to build propositions, but what are some basic propositions to be combined?

- `False` is always invalid
- `True` is always valid
- `==` will yield a proposition rather than a boolean

In some cases, F\* will automatically convert booleans into propositions.

#### 5.3.4. `Type` vs. `prop`

Another atomic proposition is to convert a type into a proposition.
F\* sometimes does this automatically through a process called *type squashing*.
This is so common that F\* allows you to use types instead of propositions using connectives (e.g. `t1 /\ t2` where `t1 t2: type`).
You can also open the `FStar.Squash` module, which provides several utilities to manipulate squashed types.

### 5.4. Assertions

With all the tools to build propositions, we need a way to ask F\* to check if the propositions are valid.
There are several ways to do this, but the most common way is to use an *assertion*.

```fs
let sqr_is_nat (x: int) : unit = assert (x * x >= 0)
```

This function takes an `int` and returns `()`, so it doesn't really do anything.
But it contains an assertion that `x * x >= 0`.
Unlike many other languages, F\* supports compile-time assertions, they're checked before even running your program.
In the case of `sqr_is_nat`, F\* will ask the SMT solver if the assertion holds for any arbitrary integer (and says it's true).

If an assertion is rejected because it's false or otherwise cannot be proved correct, the program will not compile:

```fs
// Change the assertion to x² > 0 (strictly greater!)
let sqr_is_at_least_one (x: int) : unit = assert (x * x > 0)

// Error: Assertion failed; the SMT solver could not prove the query, try to spell your proof in more detail or increase fuel/ifuel
```

This is because `0 * 0 = 0` and therefore not `0 * 0 > 0`, meaning the proposition does not hold.

You can us assertions with any proposition:

```fs
let max x y = if x > y then x else y
let _ = assert (max 0 1 = 1)
let _ = assert (forall x y. max x y >= x /\                 // Max is bigger than x or is x itself
                            max x y >= y /\                 // Max is bigger than y or is y itself
                            (max x y = x \/ max x y = y))   // One or the other must be max
```

### 5.5. Assumptions

Using assertions, you ask the SMT solver to prove a fact.
But using assumptions, you can tell the SMT solver to accept a certain proposition to be valid.
However, it's easy to make assumptions which do not actually hold, so use them only if you're absolutely sure.

For example, here's an **erroneous** way to to 'prove' `sqr_is_at_least_one`:

```fs
// Now the assert will succeed
let sqr_is_at_least_one (x: int) = assume (x <> 0); assert (x * x > 0)
```

Another form of relaxation or assumption is called `admit`.
The term `admit()` can be given any type you like:

```fs
let sqr_is_at_least_one (x:int) : y:nat{y > 0} = admit()
```

Both `assume` and `admit` can be helpful when you're working through a proof, but a proof isn't done until it no longer contains them!

## 6. Inductive types and pattern matching

We've already seen quite a few types throughout the previous chapters, but ideally we'd like to be able to create our own.

### 6.1. Enumerations

*Enumerations* are types where you can define any number of elements.
The `unit` type, for example, only has one element `()`, while `bool` has two elements: `true` and `false`.

```fs
type three =
    | One_of_three : three
    | Two_of_three : three
    | Three_of_three : three
```

The type `three` consists of three distinct constants, which are also called *(data) constructors*.
Each constructor must start with an uppercase letter.
The type annotation `: three` for each constructor is a bit redundant in this case, so you may omit them.
However, a later chapter will cover *indexed types*, where a constructor may have a different type from its defined type.

With the current definition of `three`, F\* can now prove that `three` has only three types of terms and that they are all distinct:

```fs
let distinct = assert (One_of_three <> Two_of_three /\
                       Two_of_three <> Three_of_three /\
                       Three_of_three <> One_of_three)

let exhaustive (x: three) = assert (x = One_of_three \/
                                    x = Two_of_three \/
                                    x = Three_of_three)
```

When you write a function on an enumeration type, you can use the `match` construct to target specific elements:

```fs
let is_one (x: three) : bool =
    match x with
    | One_of_three -> true
    | _ -> false // _ means 'everything else'

let is_two (x: three) : bool =
    match x with
    | Two_of_three -> true
    | _ -> false

let is_three (x: three) : bool =
    match x with
    | Three_of_three -> true
    | _ -> false
```

#### 6.1.1. Discriminators

Using the functions defined above, it's possible to map terms of type `three` into other types.

```fs
let three_to_int (x: three) : int =
    if is_one x then 1
    else if is_two x then 2
    else 3
```

These so-called *discriminators* are very common, so F\* lets you do this:

```fs
let three_to_int (x: three) : int =
    if One_of_three? x then 1
    else if Two_of_three? x then 2
    else 3
```

#### 6.1.2. Exhaustiveness

It is of course possible to directly use the `match` construct with each term:

```fs
let three_to_int_match (x: three) : int =
    match x with
    | One_of_three -> 1
    | Two_of_three -> 2
    | Three_of_three -> 3 // Alternatively, _
```

F\* will make sure to prove that you've covered every enumeration term (or used a discard).

### 6.2. Tuples

Enumerations allow you to create types with terms, but the next step is to create composite types.

```fs
type tup2 (a: Type) (b: Type) =
    | Tup2: first: a -> second: b -> tup2 a b

type tup3 (a: Type) (b: Type) =
    | Tup3 : first: a -> second: b -> third: c -> tup3 a b c
```

For the two-element tuple `tup2`, the constructor `Tup2` accepts any `x: a` and any `y: b` such that `Tup2 x y: tup2 a b`.
Note how the type itself is defined with types as arguments, while the constructor accepts terms of said types!
Other types like `tup3` and `tup4` and so on are very similar, and the types can usually be inferred.

Since these types only have one constructor, discriminators aren't very useful here.
Ideally, you'd like to get the elements from the tuple instead of its matching constructor.
This way of extracting the components of a tuple is called *projecting*.

```fs
let tup2_first #a #b (x: tup2 a b) : a =
    match x with
    | Tup2 first _ -> first

let tup2_second #a #b (x: tup2 a b) : b =
    match x with
    | Tup2 _ second -> second
```

#### 6.2.1. Projectors

These projections are so common that F\* automatically generates them for you whenever you define a tuple type.
For any constructor `T: x1:t1 -> ... -> xn:tn -> t`, F\* generates the function `T?.xi: y:t { T? y } -> ti`.
In other words, `T?.xi` is a funcion that returns the i-th component of a tuple.
For `tup2`, you automatically get `Tup2?.first` and `Tup2?.second`, and `tup3` has `Tup3?.third` as well.

#### 6.2.2. Syntax for tuples

Tuples are so common that the module `FStar.Pervasives.Native.fst` defines tuples up to arity 14 (i.e. with up to 14 elements).
You can describe a tuple type using `&`, for example `a & b` is short for `tup2 a b` where `a` and `b` are types.
You can also describe the value of a tuple using `,`, for example `x, y` means the same as `Tup2 x y`, where `x: a` and `y: b`.
To project the i-th field on a tuple, you can write `x._1`, `x._2` and so on.

While tuples are powerful, sometimes you will want to use a *record*, which is like a tuple but with named fields.

#### 6.2.3. Records

A record is a tuple with user-chosen names for its fields and with a slightly different syntax for constructing them.

```fs
type point3D = { 
    x: int;
    y: int;
    z: int
}
let origin = { x = 0; y = 0; z = 0 }
let dot (p0 p1: point3D) = p0.x * p1.x + p0.y + p1.y + p0.z * p1.z
let translate_x (p: point3D) (shift: int) = { p with x = p.x + shift } // p.y and p.z are copied over
let is_origin (x: point3D) =
    match x with
    | { z = 0; x = 0; y = 0 } -> true // Order does not matter here
    | _ -> false
```

A record type is defined as a collection of type fields separated by semicolons, all enclosed in curly braces.
You can project a field by using the dot notation `.field_name`.
The `with` notation lets you construct a new record whose fields are identical to the old record, except those you change after `with`.

### 6.3. Options

The `option` type in F\* is a standard type which is used to represent a value that could possibly be missing or undefined or what have you.
A common example is using integer division, like so:

```fs
let try_divide (x: int) (y: int) : option int =
    if y = 0 then None
    else Some (x / y)

let divide (x: int) (y: int { y <> 0 }) = x / y
```

In a language like F\#, for example, the former is valid but the latter is not.
The option type is therefore a good compromise where compile-time constraints can't be guaranteed.
In F\*, however, these constraints can be checked and asserted, so `option` isn't necessary for this example.

### 6.4. Unions, or the `either` type

The `either` type from the `FStar.Pervasives` module looks like this:

```fs
type either a b =
    | Inl : v: a -> either a b
    | Inr : v: b -> either a b
```

The type `either a b` represents a value that could be either `Inl v` (in the left case) where `v: a` or `Inr v` (in the right case) where `v: b`.
Using `Inl` and `Inr`, you can access the underlying values to use them inside functions.

```fs
let same_case #a #b #c #d (x: either a b) (y: either c d) : bool =
    match x, y with
    | Inl _, Inl _
    | Inr _, Inr _ -> true
    | _ -> false
```

The `same_case` function takes two `either`s, and sees if their values are either both the left case or both the right case.
This can be useful when applying functions that may work on more than one type, but not across the possible types.
For example, here's a `sum` function that either adds two booleans or two integers:

```fs
let sum (x: either bool int) (y: either bool int { same_case x y })
    : z: either bool int { Inl? z <==> Inl? x }
    = match x, y with
    | Inl xl,  Inl yl -> Inl (xl || yl)
    | Inr xr,  Inr yr -> Inr (xl + yl)
```

The `sum` function accepts two `either`s, with `y` being refined such that `x` and `y` must share a commonly typed left or right branch.
The function also returns an `either`, refined by the proposition that the result has the same case as `x` (and therefore also as `y`).
The return type could also have been refined as `z: either bool int { same_case z x }`.
From this refinement, it may become more clear that if `same_case x y` and `same_case z x`, then `same_case z y` must also hold.

In fact, this is a great case to check with `assert`:

```fs
let zx_and_xy_implies_zy #a #b #c #d #e #f (x: either a b) (y: either c d) (z: either e f) : unit =
    assert same_case z x /\ same_case x y ==> same_case z y
```

Since the compiler does not complain, the proposition holds!

### 6.5. Lists

So far, all the types we've seen so far do not refer to the types they construct.
Lists, however, are a so-called *inductive type*.
It is defined inside the `Prims` module as follows:

```fs
type list (a: Type) =
    | Nil : list a
    | Cons : head: a -> tail: list a -> list a
```

How does this type represent a list exactly?
The `Nil` constructor represents an empty list, whereas `Cons` represents the "concatenation" of the first element of a list (the head) and the rest of the list (the tail).
Using this representation, a single element list of type `int` can be expressed as `Cons 1 Nil`, two elements as `Cons 2 (Cons 1 Nil)` and so on.

In F\*, there's a special syntax to write lists:
- `[]` is the empty list
- `[v1; ... ; vn]` is a list containing the values `v1` through `vn`
- `head :: tail` is a concatenation of an element `head: a` and `tail: list a`

It's possible to get the length of a list:

```fs
let rec length #a (l: list a) : nat =
    match l with
    | [] -> 0
    | _ :: tail -> 1 + length tail
```

And as per the exercise, it's possible to append two lists:

```fs
val append (#a: Type) (l1 l2: list a) : l: list a { length l = length l1 + length l2 }
let rec append l1 l2 =
    match l1 with
    | [] -> l2
    | head :: tail -> head :: append tail l2
```

## 7. Proofs of termination

F\* functions must terminate.
If termination is not guaranteed, you could write something like this:

```fs
let rec loop (x: unit) : False = loop x
```

Recall that `False` represents anything that cannot be proved, but without termination, `loop` itself would be considered a valid proof, which is a contradiction!
So how does F\* determine whether or not a function terminates?

### 7.1. A well-founded partial order on terms

> **Maths review: Partial Orders**
> 
> A weak partial order relation *R* on a set *S* is a relation that is:
> 
> - reflexive: $\forall x \in S:\; x \mathrel{R} x$
> - anti-symmetric: $\forall a,b \in S:\; (a \mathrel{R} b \land b \mathrel{R} a) \Rightarrow a = b$
> - transitive: $\forall a,b,c \in S:\; (a \mathrel{R} b \land b \mathrel{R} c) \Rightarrow a \mathrel{R} c$
> 
> This relation is not necessarily restricted to mathematics.
> For example, given the set of people who are related to you (including yourself), the relation *x is an ancestor of y or x is y* is a partial ordering.
> - reflexive: you are you (matches the second condition)
> - anti-symmetric: an ancestor cannot be a descendant of itself, so if $a \mathrel{R} b$ and $b \mathrel{R} a$ both hold, $a$ and $b$ must be the same person
> - transitive: a grandparent is an ancestor of your parent, and a parent is an ancestor of you, therefore a grandparent is an ancestor of you
>
> A strict partial order relation *R* on a set *S*, on the other hand, is a relation that is:
>
> - irreflexive: $\forall x \in S:\; \neg(x \mathrel{R} x)$
> - transitive: $\forall a,b,c \in S:\; (a \mathrel{R} b \land b \mathrel{R} c) \Rightarrow a \mathrel{R} c$
>
> Unlike the weak partial order relation, a strict partial order is asymmetric.
> This means that for any $a$ and $b$, $a \mathrel{R} b \Rightarrow \neg(b \mathrel{R} a)$.
>
> A *well-founded* partial order relation $R$ on a set $S$ is a strict partial order relation that applies to every non-empty subset $X$ of the set,
> and where every subset contains a minimal element $m$ with relation to $R$ (i.e. an element for which $x \mathrel{R} m$ never holds).
>
> $\forall X \subseteq S,\; X \neq \emptyset:\; \forall x \in X:\; \exists m \in X:\; \neg(m \mathrel{R} x)$
>
> A good example is the "strictly less than" $<$ relation on the set of all natural numbers.
> For any subset of the natural numbers, there is a "least" number such that no other number is "strictly less than" it.
> Even if that subset is *all* of the natural numbers, an infinitely large set, there is no number less than 0.


In order to prove that a function terminates in F\*, you can provide a *measure*, which is a pure expression depending on the function's arguments.
F\* checks that this measure strictly decreases on each recursive call, by comparing each measure to the measure of the previous call according to a well-founded partial order on F\* terms.
If `v1` comes before `v2`, it is written as `v1 << v2`.
Having a well-founded partial order guarantees that there is a minimal `vi` for a given measure, which means that there are no infinite descending chains, and that the function should therefore terminate at some point.

#### 7.1.1. The precedes relation

Given two terms `v1: t1` and `v2: t2`, we can prove `v1 << v2` if any of the following are true:

1. The ordering on integers:

If `t1 = nat` and `t2 = nat`, then `v1 < v2` (strictly less than) implies `v1 << v2`.

2. The sub-term ordering on inductive types:

If `v2 = D u1 ... un` where `D` is a constructor of an inductive type fully applied to arguments `u1 ... un`, then `v1 << v2` holds if `v1` is one of the arguments or a *sub-term* of `v2` (i.e. some `ui = v1`) or if `v1 = ui x` for some sub-term of `v2` applied to some argument `x`.

### 7.2. Why `length` terminates

Recall how to calculate the length of a list in F\*:

```fs
let rec length (#a: Type) (l: list a) : nat =
    match l with
    | [] -> 0
    | _ :: tail -> 1 + length tail
```

This definition actually uses various syntactic shorthands to hide some details.
The full definition actually looks like this:

```fs
let rec length (#a: Type) (l: list a) : Tot nat (decreases l) =
    match l with
    | [] -> 0
    | _ :: tail -> 1 + length tail
```

The `Tot nat` part states that `length` is a total function returning a `nat` (i.e. it returns a `nat` for every possible combination of inputs for `a` and `list a`).
The `additional (decreases l)` part specifies the measure which decreases at each recursive call according to the precedence relation `<<`.
The body of the function therefore implies the following output: `#a: Type -> m: list a { m << l } -> nat`.
In other words, the recursive call can only be made on an argument `m` that precedes the current argument `l`, where eventually some `m` will reach a minimal value (i.e. the empty list).
To prove this for `length`, the recursive call `length tail` must satisfy `tail: (m: list a { m << l })` or, equivalently, that `tail << l` is valid.
From the sub-term ordering `l = Cons _ tail` so `tail << l` holds.

### 7.3. Lexicographic orderings

F\* also provides a way to enhance the well-founded ordering `<<` to lexicographic combinations of `<<`.
Given two lists of terms `v1 ... vn` and `u1 ... un`, F\* accepts the following ordering:

```fs
// Proposition form
v1 << u1 \/ (v1 == u1 /\ (v2 << u2 \/ (v2 == u2 /\ (... vn << un))))

// F* shorthand
%[v1; ... ; vn] << %[u1; ... ; un]
```

Consider the example for the `ackermann` function:

```fs
let rec ackermann (m n: nat) : Tot nat (decreases %[m; n]) =
    if m = 0 then n + 1
    else if n = 0 then ackermann (m - 1) 1
    else ackermann (m - 1) (ackermann m (n - 1))
```

The `decreases %[m; n]` says that subsequent calls of `ackermann m' n'` must satisfy `%[m'; n'] << %[m; n]`.
In other words, either `m' << m` or `m' = m /\ n' << n` must hold.

Considering each possible recursive call:
- `ackermann (m - 1) 1` is valid because `m - 1 << m` (no need to compare `n'` and `n`)
- `ackermann m (n - 1)` is valid because `m` is unchanged, but `n - 1 << n` since they are both `nat`
- `ackermann (m - 1) (ackermann m (n - 1))` is valid because `m - 1 << m` (no need to compare `n'` and `n`)

This function is notorious for taking extremely long to compute, but despite the execution time, the measure lets us prove that it theoretically will finish computing eventually for any `m` and `n`.

### 7.4. Default measures

As with `length`, you can leave out the `decreases %[m; n]` clause from `ackermann` and F\* would still accept it.
This is because F\* uses a simple heuristic to choose a decrease clause if the user didn't provide one.
The *default* decreases clause for a total, recursive function is the lexicographic ordering of all the non-function-typed arguments from left to right.
So for `ackermann`, the default is exactly `decreases %[m; n]`, while for `length`, it is `decreases %[a; l]` (which simplifies to just `decreases l`).
This means that the same function as `ackermann` but with the arguments flipped would need some extra help:

```fs
// For arguments in order (m n: nat),
// the default would be (decreases %[n; m])
let rec ackermann_flipped (n m: nat) : Tot nat (decreases %[m; n]) =
    if m = 0 then n + 1
    else if n = 0 then ackermann_flipped (m - 1) 1
    else ackermann_flipped (m - 1) (ackermann_flipped m (n - 1))
```

With the arguments flipped, the first recursive call `ackermann (m - 1) 1` is only valid when `m - 1 << n` or if `m - 1 = n /\ 1 << n`.
But in that branch, `n = 0` and `m > 0`, so `m - 1 << 0` is never true.
This leaves the `m - 1 = n /\ 1 << m` case, or with the expected values plugged in: `m - 1 = 0 /\ 1 << m`.
If `m > 1`, then this fails, but even if `m = 1` and therefore `m - 1 = 0`, the other condition `1 << 1` does not hold, so this branch is never possible!

### 7.5. Mutual recursion

F\* supports mutual recursion and tries to check if the measure of the arguments decreases on each mutually recursive call.
For example, consider the following code to define a binary tree:

```fs
type tree =
    | Terminal : tree
    | Internal : node -> tree

and node = {
    left: tree;
    data: int;
    right: tree
}

let rec incr_tree (x: tree) : tree =
    match x with
    | Terminal -> Terminal
    | Internal node -> Internal (incr_node node)

and inc_node (n: node) : node =
    {
        left = incr_tree n.left;
        data = n.data + 1;
        right = incr_tree n.right
    }
```

The functions `incr_tree` and `incr_node` mutually depend on each other to increment the data on each internal node in a binary tree.
F\* is able to prove that these functions terminate using the default measure.
This is because the recursive call to `incr_tree` only happens for the `Internal` branch, which makes the call chain look like: `incr_tree (Internal n) -> incr_node n -> incr_tree n.left`.
This is equivalent to checking if `n.left << Internal n`, which we can prove by applying sub-term ordering twice:
- `n.left << n` holds because `left` is a subterm of the node `n`
- `n << Internal n` holds because `n` is a constructor argument of `Internal`

By the transitivity property of the well-founded partial order relation `<<`, `n.left << n << Internal n ==> n.left << Internal n`.

> Note: using lexicographic orderings to prove mutually recursive functions correct
>
> ```fs
> let rec foo (l: list int) : Tot int (decreases %[l; 0]) =
>     match l with
>     | [] -> 0
>     | x :: xs -> bar xs
> and bar (l: list int) : Tot int (decreases %[l; 1]) =
>     foo l
> ```
>
> F\* can't prove that these mutually recursive functions terminate, because `bar` simply returns `foo` without decreasing `l`.
> However, `foo` itself always calls `bar` with a decreasing `l`, so you can convince F\* that even though `l` doesn't decrease, `0 << 1` validates the lexicographical order.

### 7.6. The termination check, precisely

First, some notation:

```fs
// This notation represents a set of functions f_k
// where each function has the arguments x_{k,i}: t_{k,i}
// returning some return value r_k
// satisfying a measure m_k
// which is proved by some expression e
//
// For example: f1 (x1,1: t1,1) (x1,2: t1,2) ... (x1,n: t1,n) : Tot r1 (decreases m1) = e
let f_k (x_{k,i}: t_{k, i}) : Tot r_k (decreases m_k) = e
```
#### Set of mutually recursive functions

- $f_k \left( \overline{x:t} \right) : \text{Tot } r_k \left( \text{decreases } m_k \right) = e$
- $p \left[e/x\right]$

The first notation represents a set of mutually recursive functions `f1` through `f_n` with arguments, a return type, a measure and an expression that follows.
The second notation represents a term `p` that depends on some parameter `x: t` into which the expression `e: t` is substituted for `x`.
To prove that all mutually recursive functions terminate, each measure must decrease.

Therefore, the expanded type definition requires that:

$f_k : \left( \overline{y:t} \left\{ m \left[\overline{y} / \overline{x} \right] \ll m_k \right\} \rightarrow r_k \left[\overline{y} / \overline{x} \right] \right)$

In other words, each function in the mutually recursive group can only be applied to arguments which precede the current formal parameters according to the measures of each function.

### 7.7. Exercise: Fibonacci in linear time

Naive Fibonacci:

```fs
let rec fib n =
    if n <= 1
    then 1
    else fib (n - 1) + fib (n - 2)
```

Tail-recursive Fibonacci:

```fs
let rec fib a b (n: nat) : Tot nat (decreases n) =
  match n with
  | 0 -> a
  | _ -> fib b (a + b) (n - 1)

let fibonacci n = fib 1 1 n
```

### 7.8. Exercise: Tail-recursive reversal

Naive reverse:

```fs
let rec rev (#a: Type) (l: list a) =
    match l with
    | [] -> []
    | head :: tail -> appendOne (rev tail) head
```

Tail-recursive:

```fs
let rec rev_accumulator (#a: Type) (reversed original: list a) : Tot (list a) (decreases original) =
    match original with
    | [] -> reversed
    | head :: tail -> rev_accumulator (head :: reversed) tail

let rev (#a: Type) (l: list a) =
    rev_accumulator [] l
```

## 8. Lemmas and proofs by induction

Previously, the `factorial` function was defined to be of type `nat -> nat`.
But let's say you want to prove a property about `factorial`, for example that `x > 2 ==> factorial x > x` or that `x > 3 ==> factorial x > 2 * x`.
You could put more and more refinements into the function, but this quickly pollutes the code.

You can ask F\* to check for these properties using assertions, such as:

```fs
let greater_than_two = assert (forall (x: nat). x > 2 ==> factorial x > 2)
let greater_than_three = assert (forall (x: nat). x > 3 ==> factorial x > 2 * x)
```

But F\* complains that it cannot prove this fact.
This does not necessarily mean that the fact isn't true, but it could be a sign that the SMT solver needs more help to prove it.
Recall that checking the validity of assertions in F\* is undecidable, so there are facts that F\* might not be able to prove without help.

In this case, proving the `greater_than_two` property requires a proof by induction.
F\* and the Z3 SMT solver cannot do these automatically, so you need to write a *lemma*.

### 8.1. Introducing lemmas

A lemma is a function that returns `() : unit` but which carries provable information inside the body.

```fs
let rec factorial_is_positive (x: nat) : u: unit { factorial x > 0 } =
    if x = 0 then ()
    else factorial_is_positive (x - 1)
```

This total, recursive function returns a refinement of `unit`, which means that the function always returns and that `factorial x > 0` always holds.
The body of the function proves the lemma by induction on `x`.

#### 8.1.1. Some syntactic shorthands for Lemmas

Since lemmas are so commonplace in F\* code, there's a special syntax to write them:

```fs
let rec factorial_is_positive (x: int) : Lemma (requires x >= 0) (ensures factorial x > 0) =
    if x = 0 then ()
    else factorial_is_positive (x - 1)
```

The function type `x: t -> Lemma (requires pre) (ensures post)` is has the following characteristics:
- it is called with an argument `v: t`
- the argument must satisfy the precondition `pre[v/x]`
- it always returns a `unit`
- and ensures that the postcondition `post[v/x]` is valid

It is equivalent to `x: t { pre } -> u: unit { post }`.
When the precondition is trivial, it can be omitted: `Lemma (ensures post)` or even `Lemma post`.

#### 8.1.2. A proof by induction, explained in detail

Let's look at the lemma in detail and see why it convinces F\* that `factorial x > 0`.

```fs
let rec factorial_is_pos (x: int) : Lemma (requires x >= 0) (ensures factorial x > 0) =
    if x = 0 then ()
    else factorial_is_pos (x - 1)
```

This is a proof by induction on `x`, represented as a total recursive function.
The fact that the proof is a total function ensures that the inductive argument is well-founded and therefore that the induction hypothesis is applied correctly on strictly smaller arguments.

The proof works like this:

1. the base case `x = 0` is valid because F\* can compute `factorial 0 = 1` and `1 > 0`
2. the inductive case `x > 0` works as follows
    - it is represented as `y: int { y < x } -> Lemma (requires y >= 0) (ensures factorial y > 0)`
    - this represents the *induction hypothesis* that for `y ∈ (0,x]`, `factorial y > 0` holds
    - the argument `x - 1` is allowed as the inductive case asserts that `x >= 1`

Since the induction hypothesis and the base case both yield a positive value, the general factorial definition `factorial x = x * factorial (x - 1)` is necessarily a product of two positive numbers, therefore completing the proof.

### 8.2. Exercises: Lemmas about integer functions

#### 8.2.1. Exercise 1

Prove the following lemmas about `factorial`:

```fs
val factorial_is_greater_than_arg (x: int) : Lemma (requires x > 2) (ensures factorial x > x)
```

Proof: [`factorial_is_greater_than_arg`](/Proofs.md#factorial_is_greater_than_arg)

#### 8.2.2. Exercise 2

Prove the following lemmas about `fibonacci`:

```fs
val fibonacci_greater_than_arg (n: nat { n >= 2 }) : Lemma (fibonacci n >= n)
```

Proof 1: [`fibonacci_greater_than_arg` (two base cases)](/Proofs.md#fibonacci_greater_than_arg-1)

Proof 2: [`fibonacci_greater_than_arg` (one base case)](/Proofs.md#fibonacci_greater_than_arg-2)

##### Answer 1

```fs
let rec fibonacci_greater_than_arg n =
    if n <= 3 then ()
    else (
        fibonacci_greater_than_arg (n - 1);
        fibonacci_greater_than_arg (n - 2)
    )
```

For the base cases $n=2$ and $n=3$, computing the values is sufficient to check that $\texttt{fibonacci n} \geq n$.
Next, instead of checking for every natural number, we assume that for a fixed arbitrary value $n \geq 4$ that $\forall k: n \gt k \geq 2:\; \texttt{fibonacci k} \geq k$.
This is called the *induction hypothesis*, and we use it to prove that the statement holds for a general $n$, so that we don't have to check every natural number.

$$
\begin{align*}
&           &\texttt{fibonacci n}   &= \texttt{fibonacci (n - 1)} + \texttt{fibonacci (n - 2)},     && \text{By definition} \\
&\implies   &\texttt{fibonacci n}   &\geq \texttt{fibonacci (n - 1)} + \left(n - 2\right),          && \text{Apply the induction hypothesis for } n - 2 \\
&\implies   &\texttt{fibonacci n}   &\geq \left(n - 1\right) + \left(n - 2\right),                  && \text{Apply the induction hypothesis for } n - 1 \\
&\implies   &\texttt{fibonacci n}   &\geq 2n - 3,                                                   && \text{Simplify RHS}
\end{align*}
$$

So far, we've only applied induction hypothesis.
This is allowed because both $n-1$ and $n-2$ are strictly less than $n$, and the lower bound of $2$ is also respected.
The goal of the proof is to show that $\texttt{fibonacci n} \geq n$.
If we can show that $2n - 3 \geq n$ given the conditions, then we can show that $\texttt{fibonacci n} \geq 2n - 3 \geq n$, and therefore that $\texttt{fibonacci n} \geq n$ by transitivity.

$$
\begin{align*}
&        &2n - 3 \geq n \\
&\iff    &n - 3 \geq 0 \\
&\iff    &n \geq 3 \\
\end{align*}
$$

Recall that we've already checked that $\texttt{fibonacci n} \geq n$ holds for $n=2$ and $n=3$, and that the induction hypothesis is assumed for some $n \geq 4$.
Since $n \geq 4 \gt 3$, this always holds, therefore proving the statement for any general $n \geq 4$ by induction.
We've shown that the statement holds for $n \geq 4$, and we've checked that it also holds for $n=3$ and $n=2$.
Therefore, we can safely say that $\forall n \geq 2: \texttt{fibonacci n} \geq n$, concluding the proof.

##### Answer 2

```fs
let rec fibonacci_greater_than_arg n =
    if n = 2 then ()
    else fibonacci_greater_than_arg (n - 1)
```

This time, we only use one base case for $n=2$.
The induction hypothesis this time is as follows: let some fixed $n \gt 2$ such that $\forall k: n \geq k \gt 2: \texttt{fibonacci k} \geq k$.

We start by applying the induction hypothesis:

$$
\begin{align*}
&           &\texttt{fibonacci n}   &= \texttt{fibonacci (n - 1)} + \texttt{fibonacci (n - 2)},     && \text{By definition} \\
&\implies   &\texttt{fibonacci n}   &\geq (n - 1) + \texttt{fibonacci (n - 2)},                     && \text{Apply the induction hypothesis for } n - 1 \\
\end{align*}
$$

We must prove this expression is greater than or equal to $n$, since $\texttt{fibonacci n} \geq n$:

$$
\begin{align*}
&       &(n - 1) + \texttt{fibonacci (n - 2)}   &\geq n,                && \text{We must show that this holds} \\
&\iff   &\texttt{fibonacci (n - 2)}             &\geq n - (n - 1),      && \text{Rearrange and simplify} \\
&\iff   &\texttt{fibonacci (n - 2)}             &\geq 1
\end{align*}
$$

We also have:

$$
\begin{align*}
&           &\texttt{fibonacci (n - 1)}                                 &= \texttt{fibonacci (n - 2)} + \texttt{fibonacci (n - 3)},     && \text{By definition, for } n \geq 3 \\
&\implies   &\texttt{fibonacci (n - 2)} + \texttt{fibonacci (n - 3)}    &\geq n - 1,                                                    && \text{Apply the induction hypothesis for } n - 1 \\
&\implies   &\texttt{fibonacci (n - 2)} + \texttt{fibonacci (n - 3)}    &\geq 3 - 1,                                                    && \text{Since the recursive step starts at } n = 3 \\
&\implies   &\texttt{fibonacci (n - 2)} + \texttt{fibonacci (n - 3)}    &\geq 2
\end{align*}
$$

From these findings, we must show that $\boxed{\texttt{fibonacci (n - 2)} \geq 1}$ holds under the assumption that $\boxed{\texttt{fibonacci (n - 2)} + \texttt{fibonacci (n - 3)} \geq 2}$ is true. To do this, let us falsely assume that $\texttt{fibonacci (n - 2) = 0}$ to show a contradiction with $\texttt{fibonacci (n - 3)} \geq 2$. Since we are assuming that $n \geq 3$, we must show that this assumption fails for the case where $n = 3$ and for the case where $n \gt 3$ to achieve a contradiction.

For $n = 3$:

$$
\begin{align*}
&                           &\texttt{fibonacci (n - 3)}     &= \texttt{fibonacci 0},    &&\text{IF } n = 3 \text{, by substituting } 3 \text{ for } n \\
&\implies                   &\texttt{fibonacci 0}           &\geq 2,                    &&\text{Because we assumed that } \texttt{fibonacci (n - 3)} \geq 2 \\
&\implies                   &1                              &\stackrel{↯}{\geq} 2,      && \textbf{Contradiction}
\end{align*}
$$

For $n \gt 3$:

$$
\begin{align*}
&               &\texttt{fibonacci (n - 2)}                                 &= \texttt{fibonacci (n - 3)} + \texttt{fibonacci (n - 4)},     &&\text{IF } n \gt 3 \text{, by definition} \\
&\implies       &\texttt{fibonacci (n - 2)}                                 &\geq \texttt{fibonacci (n - 3)},                               &&\text{Because } \texttt{fibonacci (n - 4)} \geq 0 \\
&\implies       &\texttt{fibonacci (n - 2)}                                 &\geq 2,                                                        &&\text{Because we assumed that } \texttt{fibonacci (n - 3)} \geq 2 \\
&\implies       &0                                                          &\stackrel{↯}{\geq} 2,                                          &&\textbf{Contradiction}
\end{align*}
$$

In all cases, assuming $\texttt{fibonacci (n - 2)} = 0$ leads to a contradiction. Therefore, if $\texttt{fibonacci (n - 2)} \in \mathbb{N}$ and $\texttt{fibonacci (n - 2)} \not = 0$, it must be at least $1$, concluding the proof.

### 8.3. Exercises: A lemma about append

Recall the type definition of the `append` function:

```fs
val append (#a: Type) (l1 l2: list a) : l: list a { length l = length l1 + length l2 }
```

Suppose we define a function called `app` with a *weaker* type:

```fs
let rec app #a (l1 l2: list a) : list a =
    match l1 with
    | [] -> l2
    | hd :: tl -> hd :: app tl l2
```

Is it possible to prove the following lemma?

```fs
val app_length (#a: Type) (l1 l2: list a) : Lemma (length (app l1 l2) = length l1 + length l2)
let rec app_length (l1 l2: list a) =
    match l1 with
    | [] -> ()
    | _ :: tl -> app_length (tl l2)
```

Given the definition of `length`, we can set up a proof that uses induction once again:

```fs
let rec length (#a: Type) (l: list a) : nat =
    match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl
```

For the empty list `[]`, F\* can compute that the length of the appended list is the same as that of the second.
Instead of setting a hypothetical range of numerical values, as was the case with `factorial` and `fibonacci`, let's consider instead some fixed non-empty list $L$ and suppose that for its tail $tl$ of $L$ that $\texttt{length (app tl l2)} = \texttt{length tl} + \texttt{length l2}$.

$$
\begin{align*}
&           &\texttt{length (app (hd :: tl) l2)}    &= 1 + \texttt{length (app tl l2)},                                     && \text{By definition, where } \texttt{L := hd :: tl} \\
&\iff       &\texttt{length (app (hd :: tl) l2)}    &= 1 + \texttt{length tl} + \texttt{length l2},                         && \text{Apply the induction hypothesis} \\
&\iff       &\texttt{length (app (hd :: tl) l2)}    &= \texttt{length (hd :: tl)} + \texttt{length l2},                     && \text{By definition, } \texttt{length (hd :: tl) := 1 + length tl} \quad \square
\end{align*}
$$

Since we found an expression that matches what we wanted to prove for `hd :: tl`, we've shown that the length of an appended *whole* list with another equals the sum of the individual lengths, rather than just for the tail of a list.

### 8.4. Intrinsic vs extrinsic proofs

As shown by the previous example, you can prove properties by enriching the type of a function or by writing a separate lemma about it.
These proof styles are called *intrinsic* and *extrinsic* respectively.
*Intrinsic* proofs are commonly used to show generally useful properties about a function, while more specific or case-by-case properties are more often stated proved *extrinsically* as lemmas.
In some cases, it is impossible to prove a property of a function *intrinsically*, in which case you must write a lemma.

```fs
let rec reverse (#a: Type) (l: list a) : list a =
    match l with
    | [] -> []
    | hd :: tl -> append (reverse tl) [hd]
```

Let's try to prove that reversing a list twice yields the original list using a refinement type:

```fs
// Propositional equality since list equality is not decidable
val reverse (#a: Type) : f: (list a -> list a) { forall l. l == f (f l) }
```

However, F\* cannot prove this directly, so we need to help the SMT solver with an additional lemma.

```fs
// Define 'snoc' (cons backwards) to add an element to a list
let snoc (#a: Type) (l: list a) (h: a) : list a = append l [h]

// Prove that reversing snoc is the same as cons'ing a reversed list
let rec snoc_cons (#a: Type) (l: list a) (h: a) : Lemma (reverse (snoc l h) == h :: reverse l) =
    match l with
    | [] -> ()
    | hd :: tl -> snoc_cons tl h
```

For the base case, we can show that both expressions converge when evaluated for `[]`:

$$
\begin{align*}
&(a)    &\texttt{reverse (snoc l h)}    &= \texttt{reverse (snoc [] h)},            && \text{By plugging in [] for l} \\
&       &                               &= \texttt{reverse (append [] [h])},        && \text{By definition of } \texttt{snoc} \\
&       &                               &= \texttt{reverse [h]},                    && \text{By definition of } \texttt{append} \text{ (base case)} \\
&       &                               &= \texttt{append (reverse []) [h]},        && \text{By definition of } \texttt{reverse} \text{ (recursive case)} \\
&       &                               &= \texttt{append [] [h]},                  && \text{By definition of } \texttt{reverse} \text{ (base case)} \\
&       &                               &= \texttt{[h]}                             && \text{By definition of } \texttt{append} \text{ (base case)} \\ \\
&(b)    &\texttt{h :: reverse l}        &= \texttt{h :: reverse []},                && \text{By plugging in [] for l} \\
&       &                               &= \texttt{h :: []},                        && \text{By definition of } \texttt{reverse} \text{ (base case)} \\
&       &                               &= \texttt{[h]},                            && \text{By definition of the list constructor} \texttt{ :: } \text{(} \texttt{Cons} \text{)} \\
\end{align*}
$$

So for the empty list, $\texttt{reverse (snoc l h) == h :: reverse l}$ does indeed hold. For the induction hypothesis, we'll try to prove that *if* for some $l := hd :: tl$, it is true that $\texttt{reverse (snoc tl h) == h :: reverse tl}$, it will also hold for $l$.

$$
\begin{align*}
&(a)        &\texttt{reverse (snoc l h)}            &= \texttt{reverse (snoc (hd :: tl) h)},            && \text{By plugging in hd :: tl for l} \\
&           &                                       &= \texttt{reverse (append (hd :: tl) [h])},        && \text{By definition of } \texttt{snoc} \\
&           &                                       &= \texttt{reverse (hd :: (append tl [h]))},        && \text{By definition of } \texttt{append} \\
&           &                                       &= \texttt{reverse (hd :: (snoc tl h))},            && \text{By definition of } \texttt{snoc} \\
&           &                                       &= \texttt{append (reverse (snoc tl h)) [hd]},      && \text{By definition of } \texttt{reverse} \\
&           &                                       &= \texttt{append (h :: reverse tl) [hd]},          && \text{Apply the induction hypothesis} \\
&           &                                       &= \boxed{\texttt{h :: (append (reverse tl) [hd])}} && \text{By definition of } \texttt{append} \\ \\

&(b)        &\texttt{h :: reverse l}                &= \texttt{h :: reverse (hd :: tl)},                && \text{By plugging in hd :: tl for l} \\
&           &                                       &= \boxed{\texttt{h :: (append (reverse tl) [hd])}} && \text{By definition of } \texttt{reverse}
\end{align*}
$$

By exploring various substitutions and rewritings, we conclude that for any arbitrary $l := hd :: tl$, both $\texttt{reverse (snoc l h)}$ and $\texttt{h :: reverse l}$ are equivalent to the expression $\texttt{h :: (append (reverse tl) [hd])}$. With the base case of `[]` being true, and with the equality holding for any list constructor `hd :: tl`, we can conclude that it holds for any list, whether empty or constructed as `hd :: tl`.

With the `snoc_cons` lemma fully proved, it's now possible to show that `reverse` is an *involutive* function, i.e. a function that is its own inverse.
Which is to say that applying `reverse` twice on an argument will yield the argument itself, like the *identity* function.

```fs
let rec reverse_involutive (#a: Type) (l: list a) : Lemma (reverse (reverse l) == l) =
    match l with
    | [] -> ()
    | hd :: tl ->
        reverse_involutive tl;
        snoc_cons (reverse tl) hd
```

For the base case, reversing the empty list simply yields itself, so that checks out. For the inductive case, we start again with some `l := hd :: tl` and try to prove that if `reverse (reverse tl) == tl` is true, then `reverse (reverse l) == l` is also true. We also use the earlier lemma `snoc_cons` to help F\* with the proof.

$$
\begin{align*}
&           &\texttt{reverse (reverse l)}       &= \texttt{reverse (reverse (hd :: tl))},           && \text{By plugging in hd :: tl for l} \\
&           &                                   &= \texttt{reverse (append (reverse tl) [hd])},     && \text{By definition of } \texttt{reverse} \\
&           &                                   &= \texttt{reverse (snoc (reverse tl) hd)},         && \text{By definition of } \texttt{snoc} \\
&           &                                   &= \texttt{hd :: reverse (reverse tl)},             && \text{Apply the } \texttt{snoc\_{}cons} \text{ lemma} \\
&           &                                   &= \texttt{hd :: tl}                                && \text{Apply the induction hypothesis} \\
&           &                                   &= \texttt{l}                                       && \text{By definition of } \texttt{l}
\end{align*}
$$

Once again, we've shown that `reverse (reverse l) == l` for both the empty list and for a general list of the form `hd :: tl`, therefore concluding the proof.

#### 8.4.1. Exercises: Reverse is injective

Prove the following lemma that shows that `reverse` is injective.

```fs
val reverse_injective (#a: Type) (l1 l2: list a) : Lemma (requires reverse l1 == reverse l2) (ensures l1 == l2)
let reverse_injective l1 l2 =
    reverse_involutive l1;
    reverse_involutive l2
```

This time, the proof does not require induction, but it does tell F\* to use the `reverse_involutive` lemma for both lists to help it prove the lemma:

$$
\begin{align*}
&           &\texttt{reverse l1}                &= \texttt{reverse l2},                 && \text{Precondition for the } \texttt{reverse\_{}injective} \text{ lemma} \\
&\iff       &\texttt{reverse (reverse l1)}      &= \texttt{reverse (reverse l2)}        && \text{Since } \texttt{reverse} \text{ is a pure function, applying it to both sides should preserve equality} \\
&\iff       &\texttt{l1}                        &= \texttt{reverse (reverse l2)}        && \text{Apply the } \texttt{reverse\_{}involutive} \text{ lemma to } \texttt{l1} \\
&\iff       &\texttt{l1}                        &= \texttt{l2}                          && \text{Apply the } \texttt{reverse\_{}involutive} \text{ lemma to } \texttt{l2} \quad \square \\
\end{align*}
$$

Alternatively, it's possible to prove first that `snoc` is injective, and then use a proof by induction to prove that `reverse` is injective as well:

```fs
let rec snoc_injective (#a: Type) (l1 l2: list a) (h1 h2: a) : Lemma (requires snoc l1 h1 == snoc l2 h2) (ensures h1 == h2 /\ l1 == l2) =
    match l1, l2 with
    | [], [] -> ()
    | _ :: tl1, _ :: tl2 -> snoc_injective tl1 tl2 h1 h2
```

To see how this works, we'll consider both paths of the pattern match. For the base case, both `l1` and `l2` are empty.

$$
\begin{align*}
&(a)        &\texttt{snoc l1 h1}        &= \texttt{snoc [] h1},         && \text{By plugging in } \texttt{[]} \text{ for } \texttt{l1} \\
&           &                           &= \texttt{append [] [h1]},     && \text{By definition of } \texttt{snoc} \\
&           &                           &= \texttt{[h1]},               && \text{By definition of } \texttt{append} \text{ (base case)} \\ \\

&(b)        &\texttt{snoc l2 h2}        &= \texttt{snoc [] h2},         && \text{By plugging in } \texttt{[]} \text{ for } \texttt{l2} \\
&           &                           &= \texttt{append [] [h2]},     && \text{By definition of } \texttt{snoc} \\
&           &                           &= \texttt{[h2]},               && \text{By definition of } \texttt{append} \text{ (base case)} \\ \\

&(c)        &\texttt{snoc l1 h1}        &= \texttt{snoc l2 h2},         && \text{Precondition for the lemma} \\
&\iff       &\texttt{[h1]}              &= \texttt{[h2]},               && \text{Use } (a) \text{ and } (b) \\
&\iff       &\texttt{h1 :: []}          &= \texttt{h2 :: []},           && \text{By injectivity of } \texttt{::} \\
&\iff       &\texttt{h1}                &= \texttt{h2},                 && \text{Since } \texttt{[]} \text{ is equal to itself}
\end{align*}
$$

For the base case, we can leverage the precondition to show that `h1 == h2` holds.
Since in the base case, `l1 = []` and `l2 = []`, they're equal by definition.
Together, it means that `h1 == h2 /\ l1 == l2` holds.

For the inductive case, we assume that for the tails `t1` and `t2` of the inputs `l1` and `l2` respectively, that if `snoc tl1 h1 == snoc tl2 h2` holds, then `h1 == h2 /\ tl1 == tl2` holds.
Then, using that assumption, we must show that `h1 == h2 /\ l1 == l2` holds.

$$
\begin{align*}
&           &\texttt{snoc l1 h1}                    &= \texttt{snoc l2 h2},                                                 && \text{Precondition for the lemma} \\
&\iff       &\texttt{snoc (hd1 :: tl1) h1}          &= \texttt{snoc (hd2 :: tl2) h2},                                       && \text{Expand } \texttt{l1} \text{ and } \texttt{l2} \\
&\iff       &\texttt{append (hd1 :: tl1) [h1]}      &= \texttt{append (hd2 :: tl2) [h2]}                                    && \text{By definition of } \texttt{snoc} \\
&\iff       &\texttt{hd1 :: (append tl1 [h1])}      &= \texttt{hd2 :: (append tl2 [h2])}                                    && \text{By definition of } \texttt{append} \\
&\iff       &\texttt{hd1 :: (snoc tl1 h1)}          &= \texttt{hd2 :: (snoc tl2 h2)},                                       && \text{By definition of } \texttt{snoc} \\
&\iff       &\texttt{hd1} = \texttt{hd2}            &\land \texttt{snoc tl1 h1} = \texttt{snoc tl2 h2},                     && \text{By injectivity of } \texttt{::} \\
&\implies   &\texttt{hd1} = \texttt{hd2}            &\land \texttt{h1} = \texttt{h2} \land \texttt{tl1} = \texttt{tl2},     && \text{Apply the induction hypothesis} \\
&\iff       &\texttt{h1} = \texttt{h2}              &\land \texttt{hd1 :: tl1} = \texttt{hd2 :: tl2},                       && \text{By definition of } \texttt{::} \\
&\iff       &\texttt{h1} = \texttt{h2}              &\land \texttt{l1} = \texttt{l2},                                       && \text{By definition of } \texttt{l1} \text{ and } \texttt{l2} \quad \square
\end{align*}
$$

This shows that $\texttt{snoc l1 h1} = \texttt{snoc l2 h2} \implies \texttt{h1} = \texttt{h2} \land \texttt{l1} = \texttt{l2}$ for both the empty list and a general `hd :: tl` list, concluding the proof.

Using this lemma, let's prove `reverse_injective` recursively:

```fs
let rec reverse_injective (#a: Type) (l1 l2: list a) : Lemma (requires reverse l1 == reverse l2) (ensures l1 == l2) =
    match l1, l2 with
    | [], [] -> ()
    | hd1 :: tl1, hd2 :: tl2 ->
        snoc_injective (reverse tl1) (reverse tl2) hd1 hd2;
        reverse_injective tl1 tl2
```

For the base case, where `l1 = []` and `l2 = []`, we can use the definition of `reverse` to see that they evaluate to be equal.
For the inductive case, we formulate the induction hypothesis to be: assume for the tails `tl1` and `tl2` for the two respective input lists that if `reverse tl1 == reverse tl2` holds, it also holds that `tl1 == tl2`.
Using the induction hypothesis and the `snoc_injective` lemma, we then try to prove that this holds for the input lists themselves.

$$
\begin{align*}
&           &\texttt{reverse l1}                            &= \texttt{reverse l2},                         && \text{Precondition of the lemma} \\
&\iff       &\texttt{reverse (hd1 :: tl1)}                  &= \texttt{reverse (hd2 :: tl2)},               && \text{Fill in the definitions of } \texttt{l1} \text{ and } \texttt{l2} \\
&\iff       &\texttt{append (reverse tl1) [hd1]}            &= \texttt{append (reverse tl2) [hd2]},         && \text{By definition of } \texttt{reverse} \\
&\iff       &\texttt{snoc (reverse tl1) hd1}                &= \texttt{snoc (reverse tl2) hd2},             && \text{By definition of } \texttt{snoc} \\
&\iff       &\texttt{reverse tl1} = \texttt{reverse tl2}    &\land \texttt{hd1} = \texttt{hd2},             && \text{Apply the } \texttt{snoc\_{}injective} \text{ lemma} \\
&\implies   &\texttt{tl1} = \texttt{tl2}                    &\land \texttt{hd1} = \texttt{hd2}              && \text{Apply the induction hypothesis} \\
&\iff       &\texttt{hd1 :: tl1}                            &= \texttt{hd2 :: tl2},                         && \text{By definition of } \texttt{::} \\
&\iff       &\texttt{l1}                                    &= \texttt{l2}                                  && \text{By definition of } \texttt{l1} \text{ and } \texttt{l2} \quad \square
\end{align*}
$$

By doing the proof manually, it becomes clear why the F\* code needed to call `snoc_injective` on the *reverse* tails.
With just one cleverly used lemma and the induction hypothesis, we've shown that $\texttt{reverse l1} = \texttt{reverse l2} \implies \texttt{l1} = \texttt{l2}$ for the inductive case.
With both cases covered, we show that it holds for any list, whether empty or `hd :: tl`, concluding the proof.

#### 8.4.2. Exercise: Optimizing reverse

It is possible to implement a tail-recursive variant of `reverse` like so:

```fs
let rec rev_aux (#a: Type) (l1 l2: list a) : Tot (list a) (decreases l2) =
    match l2 with
    | [] -> l1
    | hd :: tl -> rev_aux (hd :: l1) tl
let rev (#a: Type) (l: list a) : list a = rev_aux [] l
```

Prove the following lemma:

```fs
val rev_reverse_equivalent (#a: Type) (l: list a) : Lemma (rev l == reverse l)
```



---

# Notes

- define *total function* properly and check occurrences for correct usage