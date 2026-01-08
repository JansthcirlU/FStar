# Proofs with annotations and comments

## Misc

### `append_empty`

#### F\* lemma:

```fs
let rec append_empty (#a: Type) (l: list a) : Lemma (ensures append l [] == l) =
    match l with
    | [] -> ()
    | _ :: tl -> append_empty tl
```

#### Proof: by induction

##### Base case: `l = []`

- given: $\texttt{l} = \texttt{[]}$

$$
\begin{align*}
&                           &\texttt{append l []}       &= \texttt{append [] []}        && \text{Base case: } \texttt{l = []} \\
&                           &                           &= \texttt{[]}                  && \text{By definition of } \texttt{append} \\
&                           &                           &= \texttt{l}                   && \text{The empty list is equal to itself}
\end{align*}
$$

##### Inductive case

- given some $\texttt{l} := \texttt{hd :: tl}$
- assume $\texttt{append tl []} = \texttt{tl}$

$$
\begin{align*}
&                           &\texttt{append l []}       &= \texttt{append (hd :: tl) []}        && \text{Inductive case} \\
&                           &                           &= \texttt{hd :: append tl []}          && \text{By definition of } \texttt{append} \\
&                           &                           &= \texttt{hd :: tl}                    && \text{Apply the induction hypothesis} \\
&                           &                           &= \texttt{l}                           && \text{By definition of } \texttt{l} \quad \square
\end{align*}
$$

### `append_associative`

#### F\* lemma:

```fs
let rec append_associative (#a: Type) (l1 l2 l3: list a) : Lemma (ensures append (append l1 l2) l3 == append l1 (append l2 l3)) =
  match l1 with
  | [] -> ()
  | hd1 :: tl1 -> append_associative tl1 l2 l3
```

#### Proof: by induction

##### Base case: `l1 = []`

- given: $\texttt{l1} = \texttt{[]}, \texttt{l2} = \texttt{l2}, \texttt{l3} = \texttt{l3}$

$$
\begin{align*}
&                           &\texttt{append (append l1 l2) l3}      &= \texttt{append (append [] l2) l3}       && \text{Base case: } \texttt{l1} = \texttt{[]} \\
&                           &                                       &= \texttt{append l2 l3}                   && \text{By definition of } \texttt{append} \text{ (base case)} \\ \\
&                           &\texttt{append l1 (append l2 l3)}      &= \texttt{append [] (append l2 l3)}       && \text{Base case: } \texttt{l1} = \texttt{[]} \\
&                           &                                       &= \texttt{append l2 l3}                   && \text{By definition of } \texttt{append} \text{ (base case)}
\end{align*}
$$

##### Inductive case:

- given: $\texttt{l1} = \texttt{hd1 :: tl1}, \texttt{l2} = \texttt{l2}, \texttt{l3} = \texttt{l3}$
- assume: $\texttt{append (append tl1 l2) l3} = \texttt{append tl1 (append l2 l3)}$

$$
\begin{align*}
&                           &\texttt{append (append l1 l2) l3}      &= \texttt{append (append (hd1 :: tl1) l2) l3}     && \text{Inductive case} \\
&                           &                                       &= \texttt{append (hd1 :: append tl1 l2) l3}       && \text{By definition of } \texttt{append} \\
&                           &                                       &= \texttt{hd1 :: append (append tl1 l2) l3}       && \text{By definition of } \texttt{append} \\
&                           &                                       &= \texttt{hd1 :: append tl1 (append l2 l3)}       && \text{Apply the induction hypothesis} \\
&                           &                                       &= \texttt{append (hd1 :: tl1) (append l2 l3)}     && \text{By definition of } \texttt{append} \\
&                           &                                       &= \texttt{append l1 (append l2 l3)}               && \text{By definition of } \texttt{l1} \quad \square
\end{align*}
$$

### `factorial_is_greater_than_arg`

#### F\* lemma

```fs
let rec factorial_is_greater_than_arg (x: int) : Lemma (requires x > 2) (ensures factorial x > x) =
    if x = 3 then ()
    else factorial_is_greater_than_arg (x - 1)
```

#### Proof: by induction

##### Base case: $x = 3$

- given: $x = 3$

$$
\begin{align*}
&           &\texttt{factorial x}       &= \texttt{factorial 3},                            && \text{Base case} \\
&           &                           &= 3 \cdot \texttt{factorial 2},                    && \text{By definition of } \texttt{factorial} \text{ (recursive case)} \\
&           &                           &= 3 \cdot 2 \cdot \texttt{factorial 1},            && \text{By definition of } \texttt{factorial} \text{ (recursive case)} \\
&           &                           &= 3 \cdot 2 \cdot 1 \cdot \texttt{factorial 0},    && \text{By definition of } \texttt{factorial} \text{ (recursive case)} \\
&           &                           &= 3 \cdot 2 \cdot 1 \cdot 1,                       && \text{By definition of } \texttt{factorial} \text{ (base case)} \\
&           &                           &= 6,                                               && \text{By computation} \\
&           &                           &\gt 3,                                             && \text{Holds for the base case}
\end{align*}
$$

##### Inductive case

- given: $x \gt 3$
- assume: $\texttt{factorial (x - 1)} \gt \texttt{x - 1}$

$$
\begin{align*}
&                           &\texttt{factorial x}         &= \texttt{x} \cdot \texttt{factorial (x - 1)}     && \text{By definition of } \texttt{factorial} \tag{a} \\
&                           &                              &\gt \texttt{x} \cdot \texttt{(x - 1)}             && \text{Apply the induction hypothesis} \tag{a'} \\ \\

&                           &\texttt{x} \cdot \texttt{x - 1}  &\gt \texttt{x}     && \text{To show that } (a') \text{ holds} \tag{b} \\
&\iff                       &\texttt{x - 1}              &\gt \texttt{1}     && \text{Divide by positive number on both sides} \\
&\iff                       &\texttt{x}                  &\gt \texttt{2}     && \text{Holds since the inductive case assumes } \texttt{x} \gt 3 \quad \square
\end{align*}
$$

### `fibonacci_greater_than_arg-1`

#### F\* lemma

```fs
// Given the recursive definition of fibonacci
let rec fibonacci n =
  if n < 2 then 1
  else fibonacci (n - 1) + fibonacci (n - 2)

// Prove that for n >= 2, fibonacci n >= n
let rec fibonacci_greater_than_arg (n: nat) : Lemma (requires n >= 2) (ensures fibonacci n >= n) =
  if n <= 3 then ()
  else (
    fibonacci_greater_than_arg (n - 1);
    fibonacci_greater_than_arg (n - 2);
  )
```

#### Proof: by induction

##### Base cases: $n = 2$ and $n = 3$

- given: $n \leq 3$ (base case) and $n \geq 2$ (precondition)

For the base cases $n=2$ and $n=3$, computing the values is sufficient to check that $\texttt{fibonacci n} \geq n$.

##### Inductive case

- given: $n \geq 4$
- assume: $\forall k: n > k \geq 2:\; \texttt{fibonacci k} \geq k$ (strong induction hypothesis)

$$
\begin{align*}
&                           &\texttt{fibonacci n}   &= \texttt{fibonacci (n - 1)} + \texttt{fibonacci (n - 2)}     && \text{By definition} \\
&                           &                       &\geq \texttt{fibonacci (n - 1)} + \left(n - 2\right)          && \text{Apply the induction hypothesis for } n - 2 \\
&                           &                       &\geq \left(n - 1\right) + \left(n - 2\right)                  && \text{Apply the induction hypothesis for } n - 1 \\
&                           &                       &\geq 2n - 3                                                    && \text{Simplify RHS}
\end{align*}
$$

The goal of the proof is to show that $\texttt{fibonacci n} \geq n$. If we can show that $2n - 3 \geq n$ given the conditions, then we can show that $\texttt{fibonacci n} \geq 2n - 3 \geq n$, and therefore that $\texttt{fibonacci n} \geq n$ by transitivity.

$$
\begin{align*}
&                           &2n - 3 &\geq n \\
&\iff                       &n - 3 &\geq 0 \\
&\iff                       &n &\geq 3
\end{align*}
$$

Recall that the induction hypothesis assumes $n \geq 4$. Since $n \geq 4 > 3$, this always holds, therefore proving the statement for any general $n \geq 4$ by induction. We've shown that the statement holds for $n \geq 4$, and we've checked that it also holds for $n=3$ and $n=2$. Therefore, we can safely say that $\forall n \geq 2: \texttt{fibonacci n} \geq n$. $\square$

### `fibonacci_greater_than_arg-2`

#### F\* lemma

```fs
// Given the recursive definition of fibonacci
let rec fibonacci n =
  if n < 2 then 1
  else fibonacci (n - 1) + fibonacci (n - 2)

// Prove that for n >= 2, fibonacci n >= n (alternative approach)
let rec fibonacci_greater_than_arg (n: nat) : Lemma (requires n >= 2) (ensures fibonacci n >= n) =
  if n = 2 then ()
  else fibonacci_greater_than_arg (n - 1)
```

#### Proof: by induction

##### Base case: $n = 2$

- given: $n = 2$

Computing the value is sufficient to check that $\texttt{fibonacci 2} \geq 2$.

##### Inductive case

- given: $n > 2$
- assume: $\forall k: n \geq k > 2:\; \texttt{fibonacci k} \geq k$ (strong induction hypothesis)

We start by applying the induction hypothesis:

$$
\begin{align*}
&                           &\texttt{fibonacci n}   &= \texttt{fibonacci (n - 1)} + \texttt{fibonacci (n - 2)}     && \text{By definition} \\
&                           &                       &\geq (n - 1) + \texttt{fibonacci (n - 2)}                     && \text{Apply the induction hypothesis for } n - 1
\end{align*}
$$

We must prove this expression is greater than or equal to $n$, since $\texttt{fibonacci n} \geq n$:

$$
\begin{align*}
&                           &(n - 1) + \texttt{fibonacci (n - 2)}   &\geq n                && \text{We must show that this holds} \\
&\iff                       &\texttt{fibonacci (n - 2)}       &\geq n - (n - 1)      && \text{Rearrange and simplify} \\
&\iff                       &\texttt{fibonacci (n - 2)}       &\geq 1
\end{align*}
$$

We also have:

$$
\begin{align*}
&                           &\texttt{fibonacci (n - 1)}                                 &= \texttt{fibonacci (n - 2)} + \texttt{fibonacci (n - 3)}     && \text{By definition, for } n \geq 3 \\
&                           &\texttt{fibonacci (n - 2)} + \texttt{fibonacci (n - 3)}    &\geq n - 1                                                    && \text{Apply the induction hypothesis for } n - 1 \\
&                           &\texttt{fibonacci (n - 2)} + \texttt{fibonacci (n - 3)}    &\geq 3 - 1                                                    && \text{Since the recursive step starts at } n = 3 \\
&                           &\texttt{fibonacci (n - 2)} + \texttt{fibonacci (n - 3)}    &\geq 2
\end{align*}
$$

From these findings, we must show that $\boxed{\texttt{fibonacci (n - 2)} \geq 1}$ holds under the assumption that $\boxed{\texttt{fibonacci (n - 2)} + \texttt{fibonacci (n - 3)} \geq 2}$ is true. To do this, let us falsely assume that $\texttt{fibonacci (n - 2)} = 0$ to show a contradiction with $\texttt{fibonacci (n - 3)} \geq 2$. Since we are assuming that $n \geq 3$, we must show that this assumption fails for the case where $n = 3$ and for the case where $n > 3$ to achieve a contradiction.

For $n = 3$:

$$
\begin{align*}
&                           &\texttt{fibonacci (n - 3)}     &= \texttt{fibonacci 0}    && \text{IF } n = 3 \text{, by substituting } 3 \text{ for } n \\
&                           &\texttt{fibonacci 0}           &\geq 2                    && \text{Because we assumed that } \texttt{fibonacci (n - 3)} \geq 2 \\
&                           &1                              &\stackrel{↯}{\geq} 2      && \textbf{Contradiction}
\end{align*}
$$

For $n > 3$:

$$
\begin{align*}
&                           &\texttt{fibonacci (n - 2)}                                 &= \texttt{fibonacci (n - 3)} + \texttt{fibonacci (n - 4)}     && \text{IF } n > 3 \text{, by definition} \\
&                           &\texttt{fibonacci (n - 2)}                                 &\geq \texttt{fibonacci (n - 3)}                               && \text{Because } \texttt{fibonacci (n - 4)} \geq 0 \\
&                           &\texttt{fibonacci (n - 2)}                                 &\geq 2                                                        && \text{Because we assumed that } \texttt{fibonacci (n - 3)} \geq 2 \\
&                           &0                                                          &\stackrel{↯}{\geq} 2                                          && \textbf{Contradiction}
\end{align*}
$$

In all cases, assuming $\texttt{fibonacci (n - 2)} = 0$ leads to a contradiction. Therefore, if $\texttt{fibonacci (n - 2)} \in \mathbb{N}$ and $\texttt{fibonacci (n - 2)} \not = 0$, it must be at least $1$, concluding the proof. $\square$

### `snoc_cons`

#### F\* lemma

```fs
// Define 'snoc' (cons backwards) to add an element to a list
let snoc (#a: Type) (l: list a) (h: a) : list a = append l [h]

// Prove that reversing snoc is the same as cons'ing a reversed list
let rec snoc_cons (#a: Type) (l: list a) (h: a) : Lemma (reverse (snoc l h) == h :: reverse l) =
    match l with
    | [] -> ()
    | hd :: tl -> snoc_cons tl h
```

#### Proof: by induction

##### Base case: `l = []`

- given: $\texttt{l} = \texttt{[]}$

$$
\begin{align*}
&                           &\texttt{reverse (snoc l h)}    &= \texttt{reverse (snoc [] h)}             && \text{By plugging in [] for l} \tag{a} \\
&                           &                               &= \texttt{reverse (append [] [h])}         && \text{By definition of } \texttt{snoc} \\
&                           &                               &= \texttt{reverse [h]}                     && \text{By definition of } \texttt{append} \text{ (base case)} \\
&                           &                               &= \texttt{append (reverse []) [h]}         && \text{By definition of } \texttt{reverse} \text{ (recursive case)} \\
&                           &                               &= \texttt{append [] [h]}                   && \text{By definition of } \texttt{reverse} \text{ (base case)} \\
&                           &                               &= \texttt{[h]}                             && \text{By definition of } \texttt{append} \text{ (base case)}
\end{align*}
$$

$$
\begin{align*}
&                           &\texttt{h :: reverse l}        &= \texttt{h :: reverse []}                 && \text{By plugging in [] for l} \tag{b} \\
&                           &                               &= \texttt{h :: []}                         && \text{By definition of } \texttt{reverse} \text{ (base case)} \\
&                           &                               &= \texttt{[h]}                             && \text{By definition of the list constructor} \texttt{ :: } \text{(} \texttt{Cons} \text{)}
\end{align*}
$$

##### Inductive case

- given: $\texttt{l} = \texttt{hd :: tl}$
- assume: $\texttt{reverse (snoc tl h)} = \texttt{h :: reverse tl}$

$$
\begin{align*}
&                           &\texttt{reverse (snoc l h)}             &= \texttt{reverse (snoc (hd :: tl) h)}             && \text{By plugging in hd :: tl for l} \tag{a} \\
&                           &                                        &= \texttt{reverse (append (hd :: tl) [h])}         && \text{By definition of } \texttt{snoc} \\
&                           &                                        &= \texttt{reverse (hd :: (append tl [h]))}         && \text{By definition of } \texttt{append} \\
&                           &                                        &= \texttt{reverse (hd :: (snoc tl h))}             && \text{By definition of } \texttt{snoc} \\
&                           &                                        &= \texttt{append (reverse (snoc tl h)) [hd]}       && \text{By definition of } \texttt{reverse} \\
&                           &                                        &= \texttt{append (h :: reverse tl) [hd]}           && \text{Apply the induction hypothesis} \\
&                           &                                        &= \boxed{\texttt{h :: (append (reverse tl) [hd])}} && \text{By definition of } \texttt{append}
\end{align*}
$$

$$
\begin{align*}
&                           &\texttt{h :: reverse l}                 &= \texttt{h :: reverse (hd :: tl)}                 && \text{By plugging in hd :: tl for l} \tag{b} \\
&                           &                                        &= \boxed{\texttt{h :: (append (reverse tl) [hd])}} && \text{By definition of } \texttt{reverse}
\end{align*}
$$

For any arbitrary $\texttt{l} := \texttt{hd :: tl}$, both $\texttt{reverse (snoc l h)}$ and $\texttt{h :: reverse l}$ are equivalent to the expression $\texttt{h :: (append (reverse tl) [hd])}$. With the base case of `[]` being true, and with the equality holding for any list constructor `hd :: tl`, we can conclude that it holds for any list, whether empty or constructed as `hd :: tl`. $\square$

### `reverse_involutive`

#### F\* lemma

```fs
let rec reverse_involutive (#a: Type) (l: list a) : Lemma (reverse (reverse l) == l) =
    match l with
    | [] -> ()
    | hd :: tl ->
        reverse_involutive tl;
        snoc_cons (reverse tl) hd
```

#### Proof: by induction

##### Base case: `l = []`

- given: $\texttt{l} = \texttt{[]}$

Reversing the empty list simply yields itself, so that checks out.

##### Inductive case

- given: $\texttt{l} = \texttt{hd :: tl}$
- assume: $\texttt{reverse (reverse tl)} = \texttt{tl}$

$$
\begin{align*}
&                           &\texttt{reverse (reverse l)}       &= \texttt{reverse (reverse (hd :: tl))}           && \text{By plugging in hd :: tl for l} \\
&                           &                                   &= \texttt{reverse (append (reverse tl) [hd])}     && \text{By definition of } \texttt{reverse} \\
&                           &                                   &= \texttt{reverse (snoc (reverse tl) hd)}         && \text{By definition of } \texttt{snoc} \\
&                           &                                   &= \texttt{hd :: reverse (reverse tl)}             && \text{Apply the } \texttt{snoc\_{}cons} \text{ lemma} \\
&                           &                                   &= \texttt{hd :: tl}                                && \text{Apply the induction hypothesis} \\
&                           &                                   &= \texttt{l}                                       && \text{By definition of } \texttt{l} \quad \square
\end{align*}
$$

### `reverse_injective`

#### F\* lemma (non-recursive version)

```fs
val reverse_injective (#a: Type) (l1 l2: list a) : Lemma (requires reverse l1 == reverse l2) (ensures l1 == l2)
let reverse_injective l1 l2 =
    reverse_involutive l1;
    reverse_involutive l2
```

#### Proof: direct (no induction required)

$$
\begin{align*}
&                           &\texttt{reverse l1}                &= \texttt{reverse l2}                 && \text{Precondition for the } \texttt{reverse\_{}injective} \text{ lemma} \\
&\iff                       &\texttt{reverse (reverse l1)}      &= \texttt{reverse (reverse l2)}        && \text{Since } \texttt{reverse} \text{ is a pure function, applying it to both sides should preserve equality} \\
&\iff                       &\texttt{l1}                        &= \texttt{reverse (reverse l2)}        && \text{Apply the } \texttt{reverse\_{}involutive} \text{ lemma to } \texttt{l1} \\
&\iff                       &\texttt{l1}                        &= \texttt{l2}                          && \text{Apply the } \texttt{reverse\_{}involutive} \text{ lemma to } \texttt{l2} \quad \square
\end{align*}
$$

### `snoc_injective`

#### F\* lemma

```fs
let rec snoc_injective (#a: Type) (l1 l2: list a) (h1 h2: a) : Lemma (requires snoc l1 h1 == snoc l2 h2) (ensures h1 == h2 /\ l1 == l2) =
    match l1, l2 with
    | [], [] -> ()
    | _ :: tl1, _ :: tl2 -> snoc_injective tl1 tl2 h1 h2
```

#### Proof: by induction

##### Base case: `l1 = []` and `l2 = []`

- given: $\texttt{l1} = \texttt{[]}, \texttt{l2} = \texttt{[]}$

$$
\begin{align*}
&                           &\texttt{snoc l1 h1}        &= \texttt{snoc [] h1}          && \text{By plugging in } \texttt{[]} \text{ for } \texttt{l1} \tag{a} \\
&                           &                           &= \texttt{append [] [h1]}      && \text{By definition of } \texttt{snoc} \\
&                           &                           &= \texttt{[h1]}                && \text{By definition of } \texttt{append} \text{ (base case)} \\ \\

&                           &\texttt{snoc l2 h2}        &= \texttt{snoc [] h2}          && \text{By plugging in } \texttt{[]} \text{ for } \texttt{l2} \tag{b} \\
&                           &                           &= \texttt{append [] [h2]}      && \text{By definition of } \texttt{snoc} \\
&                           &                           &= \texttt{[h2]}                && \text{By definition of } \texttt{append} \text{ (base case)} \\ \\

&                           &\texttt{snoc l1 h1}        &= \texttt{snoc l2 h2}          && \text{Precondition for the lemma} \tag{c} \\
&\iff                       &\texttt{[h1]}              &= \texttt{[h2]}                && \text{Use } (a) \text{ and } (b) \\
&\iff                       &\texttt{h1 :: []}          &= \texttt{h2 :: []}            && \text{By injectivity of } \texttt{::} \\
&\iff                       &\texttt{h1}                &= \texttt{h2}                  && \text{Since } \texttt{[]} \text{ is equal to itself}
\end{align*}
$$

For the base case, we can leverage the precondition to show that `h1 == h2` holds. Since in the base case, `l1 = []` and `l2 = []`, they're equal by definition. Together, it means that `h1 == h2 /\ l1 == l2` holds.

##### Inductive case

- given: $\texttt{l1} = \texttt{hd1 :: tl1}, \texttt{l2} = \texttt{hd2 :: tl2}$
- assume: $\texttt{snoc tl1 h1} = \texttt{snoc tl2 h2} \implies \texttt{h1} = \texttt{h2} \land \texttt{tl1} = \texttt{tl2}$

$$
\begin{align*}
&                           &\texttt{snoc l1 h1}                    &= \texttt{snoc l2 h2}                                                  && \text{Precondition} \tag{a} \\
&\iff                       &\texttt{snoc (hd1 :: tl1) h1}     &= \texttt{snoc (hd2 :: tl2) h2}                                        && \text{Expand } \texttt{l1}, \texttt{l2} \\
&\iff                       &\texttt{append (hd1 :: tl1) [h1]} &= \texttt{append (hd2 :: tl2) [h2]}                                    && \text{By definition of } \texttt{snoc} \\
&\iff                       &\texttt{hd1 :: (append tl1 [h1])} &= \texttt{hd2 :: (append tl2 [h2])}                                    && \text{By definition of } \texttt{append} \\
&\iff                       &\texttt{hd1 :: (snoc tl1 h1)}     &= \texttt{hd2 :: (snoc tl2 h2)}                                        && \text{By definition of } \texttt{snoc} \\
&\implies                   &\texttt{hd1} = \texttt{hd2}   &\land \texttt{snoc tl1 h1} = \texttt{snoc tl2 h2}                      && \text{By injectivity of } \texttt{::} \\ \\

&                           &\texttt{snoc tl1 h1}                   &= \texttt{snoc tl2 h2}                                                  && \text{From } (a) \tag{b} \\
&\implies                   &\texttt{h1} = \texttt{h2}     &\land \texttt{tl1} = \texttt{tl2}                                       && \text{Apply the induction hypothesis} \\ \\

&                           &\texttt{h1} = \texttt{h2}              &\land \texttt{hd1} = \texttt{hd2} \land \texttt{tl1} = \texttt{tl2}    && \text{Combine } (a) \text{ and } (b) \tag{c} \\
&\iff                       &\texttt{h1} = \texttt{h2}         &\land \texttt{hd1 :: tl1} = \texttt{hd2 :: tl2}                         && \text{By definition of } \texttt{::} \\
&\iff                       &\texttt{h1} = \texttt{h2}         &\land \texttt{l1} = \texttt{l2}                                         && \text{By definition of } \texttt{l1}, \texttt{l2} \quad \square
\end{align*}
$$

### `reverse_injective` (recursive version)

#### F\* lemma

```fs
let rec reverse_injective (#a: Type) (l1 l2: list a) : Lemma (requires reverse l1 == reverse l2) (ensures l1 == l2) =
    match l1, l2 with
    | [], [] -> ()
    | hd1 :: tl1, hd2 :: tl2 ->
        snoc_injective (reverse tl1) (reverse tl2) hd1 hd2;
        reverse_injective tl1 tl2
```

#### Proof: by induction

##### Base case: `l1 = []` and `l2 = []`

- given: $\texttt{l1} = \texttt{[]}, \texttt{l2} = \texttt{[]}$

By the definition of `reverse`, both evaluate to `[]`, so they're equal.

##### Inductive case

- given: $\texttt{l1} = \texttt{hd1 :: tl1}, \texttt{l2} = \texttt{hd2 :: tl2}$
- assume: $\texttt{reverse tl1} = \texttt{reverse tl2} \implies \texttt{tl1} = \texttt{tl2}$

$$
\begin{align*}
&                           &\texttt{reverse l1}                            &= \texttt{reverse l2}                          && \text{Precondition} \tag{a} \\
&\iff                       &\texttt{reverse (hd1 :: tl1)}             &= \texttt{reverse (hd2 :: tl2)}                && \text{Expand } \texttt{l1}, \texttt{l2} \\
&\iff                       &\texttt{append (reverse tl1) [hd1]}       &= \texttt{append (reverse tl2) [hd2]}          && \text{By definition of } \texttt{reverse} \\
&\iff                       &\texttt{snoc (reverse tl1) hd1}           &= \texttt{snoc (reverse tl2) hd2}              && \text{By definition of } \texttt{snoc} \\
&\implies                   &\texttt{reverse tl1} = \texttt{reverse tl2} &\land \texttt{hd1} = \texttt{hd2}         && \text{Apply the } \texttt{snoc\_{}injective} \text{ lemma} \\ \\

&                           &\texttt{reverse tl1}                           &= \texttt{reverse tl2}                          && \text{From } (a) \tag{b} \\
&\implies                   &\texttt{tl1}                          &= \texttt{tl2}                                  && \text{Apply the induction hypothesis} \\ \\

&                           &\texttt{tl1} = \texttt{tl2}                    &\land \texttt{hd1} = \texttt{hd2}               && \text{Combine } (a) \text{ and } (b) \tag{c} \\
&\iff                       &\texttt{hd1 :: tl1}                       &= \texttt{hd2 :: tl2}                           && \text{By definition of } \texttt{::} \\
&\iff                       &\texttt{l1}                               &= \texttt{l2}                                   && \text{By definition of } \texttt{l1}, \texttt{l2} \quad \square
\end{align*}
$$

### `rev_aux_appends_to_reverse`

#### Function definitions

```fs
let rec append (#a: Type) (l1 l2: list a) = 
    match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append tl l2

let rec rev_aux (#a: Type) (acc: list a) (original: list a) : Tot (list a) (decreases original) =
    match original with
    | [] -> acc
    | hd :: tl -> rev_aux (hd :: acc) tl

let rec reverse (#a: Type) (l: list) : list a =
    match l with
    | [] -> []
    | hd :: tl -> append (reverse tl) [hd]
```

#### F\* lemma

```fs
let rec rev_aux_appends_to_reverse (#a: Type) (acc: list a) (original: list a)
    : Lemma (ensures (rev_aux acc original == append (reverse original) acc))
            (decreases original) =
    match original with
    | [] -> ()
    | hd :: tl ->
        rev_aux_appends_to_reverse (hd :: acc) tl;
        append_associative (reverse tl) [hd] acc
```

See also:

- [`append_associative`](Proofs.md#append_associative)

#### Proof: by induction

##### Base case: `original = []`

- given: $\texttt{original} = \texttt{[]}$

$$
\begin{align*}
&           &\texttt{rev\_{}aux acc original}                   &= \texttt{rev\_{}aux acc []}               && \text{Base case} \tag{a} \\
&           &                                                   &= \texttt{acc}                             && \text{By definition of } \texttt{rev\_{}aux} \text{ (base case)} \\ \\

&           &\texttt{append (reverse original) acc}             &= \texttt{append (reverse []) acc}         && \text{Base case} \tag{b} \\
&           &                                                   &= \texttt{append [] acc}                   && \text{By definition of } \texttt{reverse} \text{ (base case)} \\
&           &                                                   &= \texttt{acc}                             && \text{By definition of } \texttt{append} \text{ (base case)}
\end{align*}
$$

#### Inductive case: `original = hd :: tl`

- given: $\texttt{original} = \texttt{hd :: tl}$
- given: $\texttt{append (append l1 l2) l2} = \texttt{append l1 (append l2 l3)}$
- assume: $\texttt{rev\_{}aux (hd :: acc) tl} = \texttt{append (reverse tl) (hd :: acc)}$

$$
\begin{align*}
&       &\texttt{rev\_{}aux acc original}                   &= \texttt{rev\_{}aux acc (hd :: tl)}                   && \text{Inductive case} \\
&       &                                                   &= \texttt{rev\_{}aux (hd :: acc) tl}                   && \text{By definition of } \texttt{rev\_{}aux} \text{ (recursive case)} \\
&       &                                                   &= \texttt{append (reverse tl) (hd :: acc)}             && \text{Apply the induction hypothesis} \\
&       &                                                   &= \texttt{append (reverse tl) (append [hd] acc)}       && \text{By definition of } \texttt{append} \\
&       &                                                   &= \texttt{append (append (reverse tl) [hd]) acc}       && \text{Apply the } \texttt{append\_{}associative} \text{ lemma} \\
&       &                                                   &= \texttt{append (reverse (hd :: tl)) acc}             && \text{By definition of } \texttt{reverse} \text{ (recursive case)} \quad \square \\
\end{align*}
$$

### `rev_reverse_equivalent`

#### Function definitions

```fs
// Recursive function to reverse a list
let rec reverse (#a: Type) (l: list) : list a =
    match l with
    | [] -> []
    | hd :: tl -> append (reverse tl) hd

// Tail-recursive helper function to reverse a list
let rec rev_aux (#a: Type) (acc: list a) (original: list a) : Tot (list a) (decreases original) =
    match original with
    | [] -> acc
    | hd :: tl -> rev_aux (hd :: acc) tl

// Reverse with tail recursion
let rev (#a: Type) (l: list a) : list a = rev_aux [] l
```

#### F\* lemma

```fs
let rec rev_reverse_equivalent (#a: Type) (l: list a) : Lemma (rev l == reverse l) =
    rev_aux_appends_to_reverse [] l;
    append_empty (reverse l)
```

See also:

- [`append_empty`](Proofs.md#append_empty)
- [`rev_aux_appends_to_reverse`](Proofs.md#rev_aux_appends_to_reverse)

#### Proof

- given: $\texttt{rev\_{}aux [] l} = \texttt{append (reverse l) []}$
- given: $\texttt{append (reverse l) []} = \texttt{reverse l}$

$$
\begin{align*}
&           &\texttt{rev l}             &= \texttt{rev\_{}aux [] l}             && \text{By definition of } \texttt{rev} \\
&           &                           &= \texttt{append (reverse l [])}       && \text{Apply the } \texttt{rev\_{}aux\_{}appends\_{}to\_{}reverse} \text{ lemma} \\
&           &                           &= \texttt{reverse l}                   && \text{Apply the } \texttt{append\_{}empty} \text{ lemma} \quad \square
\end{align*}
$$

### `fib_aux_of_successive_fibonacci_yields_next_fibonacci`

#### Function definitions

```fs
// Recursive Fibonacci sequence (1, 1, 2, 3, 5, ...)
let rec fibonacci (n: nat) : nat =
    if n < 2 then 1
    else fibonacci (n - 1) + fibonacci (n - 2)

// Tail-recursive Fibonacci helper
let rec fib_aux (a b n: nat) : Tot nat (decreases n) =
    match n with
    | 0 -> a
    | _ -> fib_aux b (a + b) (n - 1)
```

#### F\* lemma

```fs
let rec fib_aux_of_successive_fibonacci_yields_next_fibonacci (n: nat) (k: nat)
    : Lemma (fib_aux (fibonacci k) (fibonacci (k + 1)) n == fibonacci (k + n)) =
    if n = 0 then ()
    else fib_aux_of_successive_fibonacci_yields_next_fibonacci (n - 1) (k + 1)
```

#### Proof: by induction

##### Base case: `n = 0`

- given: $\texttt{n} = 0$

$$
\begin{align*}
&           &\texttt{fib\_{}aux (fibonacci k) (fibonacci (k + 1)) n}        &= \texttt{fib\_{}aux (fibonacci k) (fibonacci (k + 1)) 0}      && \text{Base case} \\
&           &                                                               &= \texttt{fibonacci k}                                         && \text{By definition of } \texttt{fib} \\
&           &                                                               &= \texttt{fibonacci (k + 0)}                                   && \text{Additive identity} \\
&           &                                                               &= \texttt{fibonacci (k + n)}                                   && \text{Base case}
\end{align*}
$$

##### Inductive case: `n > 0`

- given: $\texttt{n} \gt 0$
- assume: $\texttt{fib\_{}aux (fibonacci (k + 1)) (fibonacci (k + 2)) (n - 1)} = \texttt{fibonacci ((k + 1) + (n - 1))}$

$$
\begin{align*}
&           &\texttt{fib\_{}aux (fibonacci k) (fibonacci (k + 1)) n}        &= \texttt{fib\_{}aux (fibonacci (k + 1)) (fibonacci k + fibonacci (k + 1)) (n - 1)}            && \text{By definition of } \texttt{fib\_{}aux} \\
&           &                                                               &= \texttt{fib\_{}aux (fibonacci (k + 1)) (fibonacci (k + 1) + fibonacci k) (n - 1)}            && \text{By commutativity of } + \\
&           &                                                               &= \texttt{fib\_{}aux (fibonacci (k + 1)) (fibonacci (n' - 1) + fibonacci (n' - 2)) (n - 1)}    && \text{By substituting } n' \text{ to match the definition of } \texttt{fibonacci n'} \\
&           &                                                               &= \texttt{fib\_{}aux (fibonacci (k + 1)) (fibonacci (k + 2)) (n - 1)}                          && \text{By solving for } n' \\
&           &                                                               &= \texttt{fibonacci ((k + 1) + (n - 1))}                                                       && \text{Apply the induction hypothesis} \\
&           &                                                               &= \texttt{fibonacci (k + n)}                                                                   && \text{Simplify} \quad \square
\end{align*}
$$

### `fib_fibonacci_equivalent`

#### Function definitions

```fs
// Recursive Fibonacci sequence (1, 1, 2, 3, 5, ...)
let rec fibonacci (n: nat) : nat =
    if n < 2 then 1
    else fibonacci (n - 1) + fibonacci (n - 2)

// Tail-recursive Fibonacci helper
let rec fib_aux (a b n: nat) : Tot nat (decreases n) =
    match n with
    | 0 -> a
    | _ -> fib_aux b (a + b) (n - 1)

// Fibonacci with tail recursion
let fib (n: nat) : nat = fib_aux 1 1 n
```

#### F\* lemma

```fs
let rec fib_fibonacci_equivalent (n: nat) : Lemma (ensures fib n == fibonacci n) =
    fib_aux_of_successive_fibonacci_yields_next_fibonacci n 0
```

See also:

- [`fib_aux_of_successive_fibonacci_yields_next_fibonacci`](Proofs.md#fib_aux_of_successive_fibonacci_yields_next_fibonacci)

#### Proof

- given: $\texttt{fib\_{}aux (fibonacci 0) (fibonacci 1) n} = \texttt{fibonacci n}$

$$
\begin{align*}
&                   &\texttt{fib n}                 &= \texttt{fib\_{}aux 1 1 n}                            && \text{By definition of } \texttt{fib} \\
&                   &                               &= \texttt{fib\_{}aux (fibonacci 0) (fibonacci 1) n}    && \text{Since } \texttt{fibonacci 0} = \texttt{fibonacci 1} = 1 \\
&                   &                               &= \texttt{fibonacci n}                                 && \text{Apply the } \texttt{fib\_{}aux\_{}of\_{}successive\_{}fibonacci\_{}yields\_{}next\_{}fibonacci} \text{ lemma} \quad \square
\end{align*}
$$

### `find_some_implies_true`

#### Function definitions

```fs
let rec find (#a: Type) (f: a -> bool) (l: list a) : option a =
    match l with
    | [] -> None
    | hd :: tl -> if f hd then Some hd else find f tl
```

#### F\* lemma

```fs
let test_element (#a: Type) (f: a -> bool) (o: option a) =
    match o with
    | Some x -> f x
    | _ -> true

let rec find_some_implies_true (#a: Type) (f: a -> bool) (l: list a) : Lemma (test_element f (find f l)) =
    match l with
    | [] -> ()
    | _ :: tl -> find_some_implies_true f tl
```

#### Proof: by induction

##### Base case: `l = []`

- given: $\texttt{l} = \texttt{[]}$

$$
\begin{align*}
&               &\texttt{test\_{}element f (find f l)}      &= \texttt{test\_{}element f (find f [])}       && \text{Base case} \\
&               &                                           &= \texttt{test\_{}element f None}              && \text{By definition of } \texttt{find} \\
&               &                                           &= \texttt{true}                                && \text{By definition of } \texttt{test\_{}element}
\end{align*}
$$

##### Inductive case: `l = hd :: tl`

- given: $\texttt{l} = \texttt{hd :: tl}$
- assume: $\texttt{test\_{}element f (find f tl) = \texttt{true}}$

$$
\begin{align*}
&               &\texttt{test\_{}element f (find f l)}              &= \texttt{test\_{}element f (find f (hd :: tl))}   && \text{Inductive case} \\ \\

&               &\texttt{test\_{}element f (find (hd :: tl))}       &= \texttt{test\_{}element f (Some hd)}             && \text{By definition of } \texttt{find} \text{ when } \texttt{f hd} = \texttt{true} \tag{a} \\
&               &                                                   &= \texttt{true}                                    && \text{By evaluating } \texttt{f hd} \\ \\

&               &\texttt{test\_{}element f (find (hd :: tl))}       &= \texttt{test\_{}element f (find f tl)}           && \text{By definition of } \texttt{find} \text{ when } \texttt{f hd} = \texttt{false} \tag{b} \\
&               &                                                   &= \texttt{true}                                    && \text{Apply the inductive hypothesis} \quad \square
\end{align*}
$$