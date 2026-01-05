module Taml

open FStar.Char
open FStar.List.Tot
open FStar.Mul
open FStar.String

let lowercaseLetters = "abcdefghijklmnopqrstuvwxyz"
let uppercaseLetters = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let digits = "0123456789"
let all = String.concat "" [lowercaseLetters; uppercaseLetters; digits]

type keyString = s: string { forall (c: char). List.length (filter (fun x -> x = c) (list_of_string s)) > 0 ==> index_of all c > -1 }
type valueString = s: string { forall (c: char). List.length (filter (fun x -> x = c) (list_of_string s)) > 0 ==> index_of all c > -1 }
type tamlValue =
    | Empty
    | Null
    | Text: valueString -> tamlValue
    | Boolean: bool -> tamlValue
