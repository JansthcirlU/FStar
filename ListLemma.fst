module ListLemma

open FStar.List

let rec app #a (l1 l2: list a) : list a =
  match l1 with
  | [] -> l2
  | hd :: tl -> hd :: app tl l2

// val app_length (#a:Type) (l1 l2:list a) : Lemma (length (app l1 l2) = length l1 + length l2)
// let rec app_length #a (l1 l2: list a) =
//   match l1 with
//   | [] -> assert (length l1 = 0)
//   | _ :: tl -> (
//       assert (length l1 = 1 + length tl);
//       app_length tl l2
//     )

let rec append_empty (#a: Type) (l: list a) : Lemma (ensures append l [] == l) =
  match l with
  | [] -> ()
  | _ :: tl -> append_empty tl

let rec append_associative (#a: Type) (l1 l2 l3: list a) : Lemma (ensures append (append l1 l2) l3 == append l1 (append l2 l3)) =
  match l1 with
  | [] -> ()
  | hd1 :: tl1 -> append_associative tl1 l2 l3

let rec reverse (#a: Type) (l: list a) : list a =
  match l with
  | [] -> []
  | hd :: tl -> append (reverse tl) [hd]

// Rev tail-recursive
let rec rev_aux (#a: Type) (l1 l2: list a) : Tot (list a) (decreases l2) =
    match l2 with
    | [] -> l1
    | hd :: tl -> rev_aux (hd :: l1) tl
let rev (#a: Type) (l: list a) : list a = rev_aux [] l
let rec rev_aux_appends_to_reverse (#a: Type) (l1 l2: list a)
  : Lemma (ensures (rev_aux l1 l2 == append (reverse l2) l1))
          (decreases l2) =
  match l2 with
  | [] -> ()
  | hd :: tl ->
    rev_aux_appends_to_reverse (hd :: l1) tl;
    append_associative (reverse tl) [hd] l1

let append_single_elem (#a: Type) (x: a) (l: list a) : Lemma (append [x] l == x :: l) = ()

let snoc (#a: Type) (l: list a) (h: a) = append l [h]
let rec snoc_cons (#a: Type) (l: list a) (h: a) : Lemma (reverse (snoc l h) == h :: reverse l) =
  match l with
  | [] -> ()
  | hd :: tl -> snoc_cons tl h

let rec reverse_reverse (#a: Type) (l: list a) : Lemma (reverse (reverse l) == l) =
  match l with
  | [] -> ()
  | hd :: tl -> (
    snoc_cons (reverse tl) hd;
    reverse_reverse tl
  )

let rec snoc_injective (#a: Type) (l1 l2: list a) (h1 h2: a) : Lemma (requires snoc l1 h1 == snoc l2 h2) (ensures h1 == h2 /\ l1 == l2) =
    match l1, l2 with
    | [], [] -> ()
    | _ :: tl1, _ :: tl2 -> snoc_injective tl1 tl2 h1 h2

val rev_injective (#a: Type) (l1 l2: list a) : Lemma (requires reverse l1 == reverse l2) (ensures l1 == l2)
let rec rev_injective l1 l2 =
  match l1,l2 with
  | h1::t1, h2::t2 ->
    assert(reverse (h1::t1) == reverse (h2::t2));
    assert(snoc (reverse t1) h1 == snoc (reverse t2) h2);
    snoc_injective (reverse t1) (reverse t2) h1 h2;
    assert(h1 == h2 /\ reverse t1 == reverse t2);
    rev_injective t1 t2;
    assert(t1 == t2 /\ h1::t1 == h2::t2)
  | _, _ -> ()