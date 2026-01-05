module Part1.GettingOffTheGround

open FStar.Mul

let incr (x: int) : int = x + 1
let incr1 (x: int) : y: int { y > x } = x + 1
// let incr2 (x: int) : nat = x + 1
let incr3 (x: nat) : nat = x + 1

val max (x: int) (y: int) : int
let max x y = if x > y then x else y

val max1 (x: int) (y: int) : z: int { z >= x && z >= y && (z = x || z = y )}
let max1 x y =
  if x > y then x else y

val factorial (n: nat) : nat //replace this `val` with some others
let rec factorial n =
  if n = 0 
  then 1
  else n * factorial (n - 1 <: nat)

val fibonacci (n:nat) : nat //replace this `val` with some others
let rec fibonacci n
  = if n <= 1
    then 1
    else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci1 : x: int -> y: int { y >= 1 /\ y >= x /\ (if x >= 3 then y >= 2 else true) }
let rec fibonacci1 n =
  if n <= 1 then 1
  else fibonacci1 (n - 1) + fibonacci1 (n - 2)

val apply (a b: Type) (f: a -> b) : a -> b
let apply a b f = fun x -> f x

val compose (a b c: Type) (f: b -> c) (g: a -> b) : a -> c
let compose a b c f g = fun x -> f (g x)

val twice (a: Type) (f: a -> a) (x: a) : a
let twice a f x = compose a a a f f x