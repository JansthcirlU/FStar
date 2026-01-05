module A

open FStar.Mul

let natural = x: int { x >= 0 }
let positive = x: natural { x > 0 }

val factorial (n: natural) : bang: positive { bang >= n /\ bang > 0 }
let rec factorial n =
  if n = 0
  then 1
  else n * factorial (n - 1)

val increment (n: natural) : p: int { p = n + 1 }
let increment = fun n -> (n + 1 <: positive)

val add : int -> int -> int
let add x y = x + y

let test = add 5
let result = test 3

let rec sum (x: nat) : nat =
  if x > 1 then x + sum (x - 1)
  else x

let sum_fast (x: nat) : nat = x * (x + 1) / 2

val factorial_is_greater_than_arg (x: int) : Lemma (requires x > 2) (ensures factorial x > x)
let rec factorial_is_greater_than_arg (x: int) =
  if x = 3 then ()
  else factorial_is_greater_than_arg (x - 1)

// 0 1 2 3 4 5
// 1 1 
//   1 2
//     2 3
//       3 5
//         5 8
let rec fibonacci (n: nat) : nat =
  if n <= 1 then 1
  else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_greater_than_arg (n: nat { n >= 2 }) : Lemma (fibonacci n >= n)
let rec fibonacci_greater_than_arg n =
  if n = 2 then ()
  else fibonacci_greater_than_arg (n - 1)

let text = assert (fibonacci 0 = 1)