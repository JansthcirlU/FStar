module Records

open FStar.Mul
open FStar.Pervasives

type point3D = { 
    x: int;
    y: int;
    z: int
}

let dot (p0 p1: point3D) = p0.x * p1.x + p0.y + p1.y + p0.z * p1.z
let translate_x (p: point3D) (shift: int) = { p with x = p.x + shift }

let origin = { x = 0; y = 0; z = 0 }
let is_origin (x: point3D) =
    match x with
    | origin -> true
    | _ -> false

let same_case #a #b #c #d (x: either a b) (y: either c d) : bool =
    match x, y with
    | Inl _, Inl _
    | Inr _, Inr _ -> true
    | _ -> false

let sum (x: either bool int) (y: (either bool int) { same_case x y })
    : z: (either bool int) { Inl? z <==> Inl? x }
    =
    match x, y with
    | Inl xl,  Inl yl -> Inl (xl || yl)
    | Inr xr,  Inr yr -> Inr (xr + yr)

let zx_and_xy_implies_zy #a #b #c #d #e #f (x: either a b) (y: either c d) (z: either e f) : unit =
    assert same_case z x /\ same_case x y ==> same_case z y

type list (a: Type) =
    | Nil : list a
    | Cons : head: a -> tail: list a -> list a

let one_element_list : list int = Cons 1 Nil

let rec length #a (l: list a) : nat =
    match l with
    | Nil -> 0
    | Cons _ tail -> 1 + length tail

val append (#a: Type) (l1 l2: list a) : l: list a { length l = length l1 + length l2 }
let rec append l1 l2 =
    match l1 with
    | Nil -> l2
    | Cons head tail -> Cons head (append tail l2)