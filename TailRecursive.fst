module TailRecursive

open FStar.Mul

// Reverse
let rec rev_aux (#a: Type) (reverse original: list a) : Tot (list a) (decreases original) =
  match original with
  | [] -> reverse
  | hd :: tl -> rev_aux (hd :: reverse) tl

let rev (#a: Type) (l: list a) = rev_aux [] l

// Factorial
let rec factorial_aux (b: nat) (n: nat) : Tot nat (decreases n) =
  if n < 1 then b
  else factorial_aux (b * n) (n - 1)
let factorial (n: nat) = factorial_aux 1 n

// Sum of a list
let rec sum_aux (acc: nat) (l: list nat) : Tot nat (decreases l) =
  match l with
  | [] -> acc
  | hd :: tl -> sum_aux (acc + hd) tl
let sum (l: list nat) : nat = sum_aux 0 l

// Length of a list
let rec length_aux (#a: Type) (acc: nat) (l: list a) : Tot nat (decreases l) =
  match l with
  | [] -> acc
  | _ :: tl -> length_aux (acc + 1) tl
let length (#a: Type) (l: list a) = length_aux 0 l

// Fibonacci
let rec fib_aux (start: nat) (next: nat) (n: nat) : Tot nat (decreases n) =
  match n with
  | 0 -> start
  | 1 -> next
  | _ -> fib_aux next (start + next) (n - 1)
let fib (n: nat) = fib_aux 0 1 n

// Sigma notation
let rec sigma_aux (acc: nat) (f: nat -> nat) (start: nat) (stop: nat { start <= stop }) : Tot nat (decreases stop) =
  if stop = start then acc + f start
  else sigma_aux (acc + f stop) f start (stop - 1)
let sigma (f: nat -> nat) (m: nat) (n: nat { m <= n }) = sigma_aux 0 f m n

// Map
let rec map_aux (#a #b: Type) (acc: list b) (f: a -> b) (l: list a) : Tot (list b) (decreases l) =
  match l with
  | [] -> acc
  | hd :: tl -> map_aux (f hd :: acc) f tl
let map (#a #b: Type) (f: a -> b) (l: list a) : list b = map_aux [] f (rev l)