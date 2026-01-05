module Reverse

type list (a: Type) =
  | Nil
  | Cons: head: a -> tail: list a -> list a

// Try to make tail-recursive?
let rec appendOne (#a: Type) (l: list a) (x: a) : list a =
  match l with
  | Nil -> Cons x Nil
  | Cons head tail -> Cons head (appendOne tail x)

// Try to make tail-recursive?
let rec append (#a: Type) (l1: list a) (l2: list a) : list a =
  match l1 with
  | Nil -> l2
  | Cons head tail -> Cons head (append tail l2)

// Try to make tail-recursive?
let rec rev (#a: Type) (l: list a) =
  match l with
  | Nil -> Nil
  | Cons head tail -> appendOne (rev tail) head

let rec rev_acc (#a: Type) (reverse original: list a) : Tot (list a) (decreases original) =
  match original with
  | Nil -> reverse
  | Cons head tail -> rev_acc (Cons head reverse) tail

let rev2 (#a: Type) (l: list a) =
  rev_acc Nil l