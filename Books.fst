module Books

// Length of a list
val length (#a: Type) (l: list a) : nat
let rec length l =
    match l with
    | [] -> 0
    | head :: tail -> 1 + length tail

// See if a list contains a value
let rec contains (#a: eqtype) (l: list a) (x: a) : bool =
    match l with
    | [] -> false
    | head :: tail -> if head = x then true else contains tail x

// Minimum of two naturals
val min2 (x y: nat) : res: nat { (res = x || res = y) && res <= x && res <= y }
let min2 x y =
    if x < y then x else y

// Maximum of two naturals
val max2 (x y: nat) : res: nat { (res = x || res = y) && res >= x && res >= y }
let max2 x y =
    if x > y then x else y

// Minimum value in a list
val minlist (l: list nat { length l > 0 }) : minimum: nat { forall (x: nat { contains l x }). minimum <= x }
let rec minlist l =
    match l with
    | head :: [] -> head
    | first :: (second :: []) -> min2 first second
    | first :: (second :: rest) -> min2 (min2 first second) (minlist rest)

// Maximum value in a list
val maxlist (l: list nat { length l > 0 }) : maximum: nat { forall (x: nat { contains l x }). maximum >= x }
let rec maxlist l =
    match l with
    | head :: [] -> head
    | first :: (second :: []) -> max2 first second
    | first :: (second :: rest) -> max2 (max2 first second) (maxlist rest)

// Zero-indexed list element access
type elementaccess (a: eqtype) =
    | Element : value: a -> elementaccess a
    | OutOfBounds : elementaccess a

val at (#a: eqtype) (l: list a) (i: nat) : element: elementaccess a { if Element? element then contains l (Element?.value element) else true }
let rec at l i =
    if i >= length l then OutOfBounds
    else
        match l with
        | head :: tail ->
            match tail with
            | [] -> assert (i = 0); Element head
            | _ -> if i = 0 then Element head else at tail (i - 1)

// Positional equality for the first n elements
val poseqn (#a: eqtype) (l1 l2: list a) (n: nat) : égalité: bool { (n = 0 ==> égalité = true) /\ 
                                                                   ((length l1 = 0 /\ length l2 = 0) ==> égalité = true) /\
                                                                   (length l1 <> length l2 /\ n > min2 (length l1) (length l2) ==> égalité = false) /\
                                                                   (length l1 <> length l2 /\ n <= min2 (length l1) (length l2) ==> forall (index: nat { index < n }). at l1 index = at l2 index) }
let rec poseqn l1 l2 n =
    if n = 0 then true
    else
        match l1, l2 with
        | [], [] -> true
        | [], _ :: _
        | _ :: _, [] -> false
        | h1 :: t1, h2 :: t2 -> 
            let huh = h1 = h2 && poseqn t1 t2 (n - 1) in
            assert (n <> 0);
            assert (length l1 <> 0);
            assert (length l2 <> 0);
            huh

// Positional equality
val poseq (#a: eqtype) (l1 l2: list a) : égalité: bool { (length l1 <> length l2 ==> égalité = false) /\
                                                         (length l1 = length l2) /\
                                                         (length l1 = 0 \/ forall (index: nat { index < length l1 }). at l1 index = at l2 index) }
let poseq l1 l2 =
    length l1 = length l2 && poseqn l1 l2 (length l1)

// Skip n elements
val skip (#a: Type) (l: list a) (n: nat { n <= length l }) : lijst: list a { length lijst = length l - n }
let rec skip l n =
    if n = 0 then l
    else
        match l with
        | head :: tail -> skip tail (n - 1)

val skip_zero_equals_input (#a: eqtype) (l: list a) : Lemma (ensures (skip l 0) = l)
let skip_zero_equals_input l =
    assert (skip l 0 = l)

val list_eqtype_equality_implies_poseq (#a: eqtype) (l1 l2: list a) : Lemma (ensures (l1 = l2 <==> poseq l1 l2))
let rec list_eqtype_equality_implies_poseq l1 l2 =
    if l1 <> l2 then ()
    else
        match l1, l2 with
        | h1 :: t1, h2 :: t2 ->
            assert (h1 = h2);
            list_eqtype_equality_implies_poseq t1 t2

// Add element to list
val appendOne (#a: eqtype) (l: list a) (x: a) : langer: list a { length langer = 1 + length l /\
                                                              at langer (length l) = Element x /\
                                                              (length l = 0 ==> langer = [x]) /\
                                                              length l > 0 ==> poseqn langer l (length l) }
let rec appendOne l x =
    match l with
    | head :: tail -> head :: (appendOne tail x)
    | head :: [] -> head :: [x]
    | [] -> [x]

// Append two lists
val append (#a: eqtype) (l1 l2: list a)
    : lijst: list a { (length l1 = 0 ==> lijst = l2) /\
                      (length l2 = 0 ==> lijst = l1) /\
                      length lijst = length l1 + length l2 /\
                      poseqn lijst l1 (length l1) /\
                      poseq (skip lijst (length l1)) l2 }
let rec append l1 l2 =
    match l1, l2 with
    | [], [] -> []
    | [], second -> 
        assert (length l1 = 0);
        assert (length l2 <> 0);
        assert (length l2 = length l1 + length l2);
        assert (poseqn second l1 0);
        let skipped = skip second (length l1) in
        assert (poseq skipped second);
        second
    | first, [] -> first
    | head :: tail, second -> head :: (append tail second)

// Take n elements

// Slice a list

// // Remove duplicates
// val dedupe (#a: eqtype) (l: list a) : lijst: list a { length lijst <= length l /\ 
//                                                       forall (x: a). (contains l x <==> contains lijst x /\
//                                                                       ~(contains l x) <==> ~(contains lijst x)) }
// let dedupe l =
//     match l with
//     | [] -> []
//     | head :: tail -> []

// type book = {
//     chapters: list nat;
// }