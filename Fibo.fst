module Fibo

// let rec fibonacci (n: nat) : nat =
//   if n <= 1 then 1
//   else fibonacci (n - 1) + fibonacci (n - 2)

let rec fib (t: (nat * nat)) (n: nat) : Tot nat (decreases n) =
  match n with
  | 0 -> t._1
  | _ -> fib (t._2, (t._1 + t._2)) (n - 1)

let fibonacci_tl n = fib (1, 1) n

let rec fibonacci (n: nat) =
  match n with
  | 0 -> 1
  | 1 -> 1
  | _ -> fibonacci (n - 1) + fibonacci (n - 2)

let rec fibonacci_greater_than_arg (n: nat) : Lemma (ensures fibonacci n >= n) =
  if n < 2 then ()
  else (
    fibonacci_greater_than_arg (n - 1);
    fibonacci_greater_than_arg (n - 2)
  )