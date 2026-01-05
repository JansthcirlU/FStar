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
&           &\texttt{append l []}       &= \texttt{append [] []},       && \text{Base case: } \texttt{l = []} \\
&           &                           &= \texttt{[]},                 && \text{By definition of } \texttt{append} \\
&           &                           &= \texttt{l},                  && \text{The empty list is equal to itself}
\end{align*}
$$

##### Inductive case

- given some $\texttt{l} := \texttt{hd :: tl}$
- assume $\texttt{append tl []} = \texttt{tl}$

$$
\begin{align*}
&           &\texttt{append l []}       &= \texttt{append (hd :: tl) []},       && \text{Inductive case} \\
&           &                           &= \texttt{hd :: append tl []},         && \text{By definition of } \texttt{append} \\
&           &                           &= \texttt{hd :: tl},                   && \text{Apply the induction hypothesis} \\
&           &                           &= \texttt{l},                          && \text{By definition of } \texttt{l} \quad \square
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
&(a)        &\texttt{append (append l1 l2) l3}      &= \texttt{append (append [] l2) l3},       && \text{Base case: } \texttt{l1} = \texttt{[]} \\
&           &                                       &= \texttt{append l2 l3},                   && \text{By definition of } \texttt{append} \text{ (base case)} \\ \\
&(b)        &\texttt{append l1 (append l2 l3)}      &= \texttt{append [] (append l2 l3)},       && \text{Base case: } \texttt{l1} = \texttt{[]} \\
&           &                                       &= \texttt{append l2 l3},                   && \text{By definition of } \texttt{append} \text{ (base case)}
\end{align*}
$$

##### Inductive case:

- given: $\texttt{l1} = \texttt{hd1 :: tl1}, \texttt{l2} = \texttt{l2}, \texttt{l3} = \texttt{l3}$
- assume: $\texttt{append (append tl1 l2) l3} = \texttt{append tl1 (append l2 l3)}$

$$
\begin{align*}
&           &\texttt{append (append l1 l2) l3}      &= \texttt{append (append (hd1 :: tl1) l2) l3},     && \text{Inductive case} \\
&           &                                       &= \texttt{append (hd1 :: append tl1 l2) l3},       && \text{By definition of } \texttt{append} \\
&           &                                       &= \texttt{hd1 :: append (append tl1 l2) l3},       && \text{By definition of } \texttt{append} \\
&           &                                       &= \texttt{hd1 :: append tl1 (append l2 l3)},       && \text{Apply the induction hypothesis} \\
&           &                                       &= \texttt{append (hd1 :: tl1) (append l2 l3)},     && \text{By definition of } \texttt{append} \\
&           &                                       &= \texttt{append l1 (append l2 l3)},               && \text{By definition of } \texttt{l1} \quad \square
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
&(a)        &\texttt{factorial x}                   &= \texttt{x} \cdot \texttt{factorial (x - 1)},     && \text{By definition of } \texttt{factorial} \\
&           &                                       &\gt \texttt{x} \cdot \texttt{(x - 1)},             && \text{Apply the induction hypothesis} \\ \\

&(b)        &\texttt{x} \cdot \texttt{x - 1}        &\gt \texttt{x},                                    && \text{To show that } (a) \text{ holds} \\
&\iff       &\texttt{x - 1}                         &\gt \texttt{1},                                    && \text{Divide by positive number on both sides} \\
&\iff       &\texttt{x}                             &\gt \texttt{2},                                    && \text{Holds since the inductive case assumes } \texttt{x} \gt 3 \quad \square
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

##### Base case: $n \leq 3$

Given:

- $n \leq 3$ (base case)
- $n \geq 2$ (precondition)

This means that the base cases are $n = 2$ and $n = 3$.

$$
\begin{align*}
&     &\texttt{fibonacci n}   &= \texttt{fibonacci } 2      && \text{Base case}
\end{align*}
$$

##### Inductive case

- given: $n \geq 3$
- assume: $\texttt{fibonacci (n - 1)} \geq \texttt{(n - 1)} \land \texttt{fibonacci (n - 2)} \geq \texttt{(n - 2)}$

$$
\begin{align*}
% Proof for inductive case
\end{align*}
$$

### `fibonacci_greater_than_arg-2`

#### F\* lemma

```fs
// F* lemma
```

#### Proof: by induction

##### Base case: base case description

- given: given by the base case

$$
\begin{align*}
% Proof for base case
\end{align*}
$$

##### Inductive case

- given: given by the inductive case
- assume: <induction hypothesis>

$$
\begin{align*}
% Proof for inductive case
\end{align*}
$$

