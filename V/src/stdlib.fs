﻿module stdlib

open Compiler
open compiledStdlib

let content = """

// ============
// Type Aliases
// ============

type alias String = [Char];

// =======================
// Miscellaneous functions
// =======================

let id x = x;

let const x _ = x;

// ==================
// Function functions
// ==================

let flip f x y = f y x;
let apply f x = f x;
let compose f g x = f (g x);

let infixr 1 ($) = apply;
let infixr 9 (.) = compose;

// ====================
// Arithmetic functions
// ====================

let remainder x y = x - (x/y)*y;
let infixl 8 (%) = remainder;

let negate x = -x;

let abs x =
    if x < 0 then
        -x
    else
        x
;

// =================
// Logical functions
// =================

let not t =
    if t then
        False
    else
        True
;

let xor t1 t2 =
    if t1 then
        not t2
    else
        t2
;

// ===============
// Tuple Functions
// ===============

let fst (x, _) = x;
let snd (_, y) = y;

let swap (x, y) = (y, x);

// ================
// Record Functions
// ================

// let get acc r = fst $ acc raise r;
// let set acc v r = snd $ acc v r;

let modify acc f r =
    let oldV = get acc r;
    set acc (f oldV) r
;

let infixl 8 (^.) = flip get;
let infixr 8 (^=) = set;
let infixr 8 (^~) = modify;

let infixl 1 (&) = flip apply;

let infixl 9 (:.) = stack;
let infixl 9 (~.) acc (getter, setter) = distort acc getter setter;

// ====================
// Basic List functions
// ====================

let head (x :: xs) = x;
let tail (x :: xs) = xs;

let empty? x =
    match x with
    | [] -> True
    | _ -> False
;

let rec append x ls =
    match ls with
    | [] -> [x]
    | l :: ls -> l :: append x ls 
;

let rec concat ls1 ls2 =
    match ls1 with
    | [] -> ls2
    | x :: xs -> x :: concat xs ls2
;
let infixr 5 (@) = concat;

let rec last ls =
    match ls with
    | [x] -> x
    | _ :: xs -> last xs
;

let rec init ls =
    match ls with
    | [x] -> []
    | x :: xs -> x :: init xs
;

let rec length ls =
    match ls with
    | [] -> 0
    | _ :: xs -> 1 + length xs
;


// =========================
// List generation functions
// =========================

let rec range start finish inc =
    if (inc > 0 && start <= finish) || (inc < 0 && start >= finish) then
        start::(range (start+inc) finish inc)
    else
        []
;

let rec repeat n x =
  match n with
  | 0 -> []
  | n -> x :: (repeat (n-1) x)
;

// =============================
// List transformation functions
// =============================

let reverse ls =
    let rec f lsOld lsNew =
        match lsOld with
        | [] -> lsNew
        | x :: xs -> f xs $ x :: lsNew
    ;
    f ls []
;

let rec map f ls =
    match ls with
    | [] -> []
    | x :: xs -> f x :: map f xs
;


// ========================
// List reduction functions
// ========================

let rec fold f acc ls =
    match ls with
    | [] -> acc
    | x :: xs -> fold f (f acc x) xs
;

let reduce f (x :: xs) = fold f x xs;

let rec all pred ls =
    match ls with
    | [] -> True
    | x :: _ when not $ pred x -> False
    | _ :: xs -> all pred xs
;

let rec any pred ls =
    match ls with
    | [] -> False
    | x :: _ when pred x -> True
    | _ :: xs -> any pred xs
;

let maximum ls =
    reduce (\acc x -> if acc < x then x else acc) ls
;

let minimum ls =
    reduce (\acc x -> if acc > x then x else acc) ls
;

// =================
// Sublist functions
// =================

let rec take n ls =
    match (n, ls) with
    | (0, _) -> []
    | (n, []) when n > 0 -> []
    | (n, x :: xs) when n > 0 -> x :: take (n-1) xs 
;

let rec drop n ls =
    match (n, ls) with
    | (0, ls) -> ls
    | (n, []) when n > 0 -> []
    | (n, x :: xs) when n > 0 -> drop (n-1) xs
;

let rec takeWhile pred ls =
    match ls with
    | [] -> []
    | x :: xs when not $ pred x -> []
    | x :: xs -> x :: takeWhile pred xs
;

let rec dropWhile pred ls =
    match ls with
    | [] -> []
    | x :: xs when not $ pred x -> ls
    | _ :: xs -> dropWhile pred xs
;

let sublist start size ls =
    if start < 0 || size > length ls then
        raise
    else
        take size $ drop start ls 
;

let rec deleteN n ls =
    match ls with
    | [] -> []
    | x :: xs ->
        match n with
        | 0 -> xs
        | n -> x :: deleteN (n-1) xs
;

// =====================
// List search functions
// =====================

let rec exists t ls =
    match ls with
    | [] -> False
    | x :: _ when x = t -> True
    | _ :: xs -> exists t xs
;

let rec filter pred ls =
    match ls with
    | [] -> []
    | x :: xs when pred x -> x :: filter pred xs
    | _ :: xs -> filter pred xs
;

// =======================
// List indexing functions
// =======================

let indexOf t ls =
    let rec f index ls =
        match ls with
        | [] -> -1
        | x :: _ when t = x -> index
        | _ :: xs -> f (index + 1) xs
    ;
    f 0 ls
;

let rec nth index ls =
    match (index, ls) with
    | (0, x :: _) -> x
    | (n, _ :: xs) when n > 0 -> nth (n-1) xs
;
let infixl 9 (!!) = flip nth;

// ======================
// List sorting functions
// ======================

let rec sort ls =
    match ls with
    | [] -> []
    | pivot :: xs ->
        (sort $ filter ((>) pivot) xs)
        @ [pivot] @
        (sort $ filter ((<=) pivot) xs)
;

// ======================
// List zipping functions
// ======================

let rec zip x y =
    match (x, y) with
    | ([], _) -> []
    | (_, []) -> []
    | (x :: xs, y :: ys) -> (x, y) :: zip xs ys
;

let rec zipWith f x y =
    match (x, y) with
    | ([], _) -> []
    | (_, []) -> []
    | (x :: xs, y :: ys) -> f x y :: zipWith f xs ys
;

let unzip ls =
    let x = map (\(x, _) -> x) ls;
    let y = map (\(_, y) -> y) ls;
    (x, y)
;

// ===========================
// String conversion functions
// ===========================

let parseInt (s: String): Int =
    match s with
    | x :: xs ->
        let rec f (s: String): Int =
            match s with
            | [] -> 0
            | x :: xs ->
                let n = 
                    match x with
                    | '0' -> 0
                    | '1' -> 1
                    | '2' -> 2
                    | '3' -> 3
                    | '4' -> 4
                    | '5' -> 5
                    | '6' -> 6
                    | '7' -> 7
                    | '8' -> 8
                    | '9' -> 9;
                n + 10 * f xs
        ;
        if x = '-' then
            negate . f . reverse $ xs
        else
            f (reverse s)
;

let rec printInt (i: Int): String =
    let printDigit d =
        match d with
        | 0 -> "0"
        | 1 -> "1"
        | 2 -> "2"
        | 3 -> "3"
        | 4 -> "4"
        | 5 -> "5"
        | 6 -> "6"
        | 7 -> "7"
        | 8 -> "8"
        | 9 -> "9"
    ;
    if i < 0 then   
        '-' :: printInt (-i)
    else if i < 10 then
        printDigit i
    else 
        let c = printDigit (i % 10);
        printInt (i/10) @ c
;

let parseBool (s: String): Bool =
    if s = "True" then
        True
    else if s = "False" then
        False
    else 
        raise
;

let printBool (b: Bool): String =
    if b then
        "True"
    else
        "False"
;
"""

let compiled = compiled

//let loadCompiled term =
//   let lib = loadArray compiled
//   replaceXLib lib term

let loadCompiled unit = loadCompiledLib compiled

let stdEnv = (loadCompiled ()).translationEnv