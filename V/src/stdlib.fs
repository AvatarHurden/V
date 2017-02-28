module stdlib

open Compiler
open compiledStdlib

let content = """

// ====================
// Arithmetic functions
// ====================

let rec remainder x y =
    if y = 0 then  
        raise
    else if x<y then
        x
    else
        remainder (x-y) y
;

let negate x = 0 - x;

let abs x =
    if x < 0 then
        negate x
    else
        x
;

// =================
// Logical functions
// =================

let not t =
    if t then
        false
    else
        true
;

let xor t1 t2 =
    if t1 then
        not t2
    else
        t2
;

// ====================
// Basic List functions
// ====================

let rec append x ls =
    if empty? ls then
        x::ls
    else
        (head ls)::(append x (tail ls))
;

let rec concat ls1 ls2 =
    if empty? ls1 then
        ls2
    else
        (head ls1)::(concat (tail ls1) ls2)
;

let rec last ls =
    if empty? ls then
        raise
    else if empty? (tail ls) then
        head ls
    else
        last (tail ls)
;

let rec init ls =
    if empty? ls then
        raise
    else if empty? (tail ls) then
        nil
    else
        (head ls)::(init (tail ls))
;

let rec length ls =
    if empty? ls then
        0
    else
        1 + length (tail ls)
;


// =========================
// List generation functions
// =========================

let rec range start finish inc =
    if (inc > 0 && start <= finish) || (inc < 0 && start >= finish) then
        start::(range (start+inc) finish inc)
    else
        nil
;

// =============================
// List transformation functions
// =============================

let reverse ls =
    let rec f lsOld lsNew =
        if empty? lsOld then
            lsNew
        else
            f (tail lsOld) ((head lsOld)::lsNew)
    ;
    f ls []
;

let rec map f ls =
    if empty? ls then
        nil
    else
        (f (head ls))::(map f (tail ls))
;


// ========================
// List reduction functions
// ========================

let rec fold f acc ls =
    if empty? ls then
        acc
    else
        fold f (f acc (head ls)) (tail ls)
;

let reduce f ls =
    if empty? ls then
        raise
    else
        fold f (head ls) (tail ls)
;

let rec all pred ls =
    if empty? ls then
        true
    else if not . pred $ head ls then
        false
    else
        all pred $ tail ls 
;

let rec any pred ls =
    if empty? ls then
        false
    else if pred $ head ls then
        true
    else
        any pred $ tail ls
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

let rec take x ls =
    if x < 0 then
        raise
    else if (x = 0) || (empty? ls) then
        nil
    else
        (head ls)::(take (x-1) $ tail ls)
;

let rec drop x ls =
    if x < 0 then
        raise
    else if empty? ls || x = 0 then
        ls    
    else
        drop (x-1) (tail ls)
;

let rec takeWhile pred ls =
    if empty? ls then
        nil
    else if not . pred $ head ls then
        nil
    else
        (head ls)::(takeWhile pred $ tail ls)
;

let rec dropWhile pred ls =
    if empty? ls then
        []
    else if not . pred $ head ls then
        ls
    else
        dropWhile pred $ tail ls
;

let sublist start size ls =
    if start < 0 || size > length ls then
        raise
    else
        take size $ drop start ls 
;

// =====================
// List search functions
// =====================

let rec exists t ls =
    if empty? ls then
        false
    else if t = (head ls) then
        true
    else
        exists t $ tail ls
;

let rec filter pred ls =
    if empty? ls then
        nil
    else if pred $ head ls then
        head ls::(filter pred $ tail ls)
    else
        filter pred $ tail ls
;

// =======================
// List indexing functions
// =======================

let indexOf t ls =
    let rec f index ls =
        if empty? ls then
            -1
        else if t = (head ls) then
            index
        else
            f (index+1) (tail ls)
    ;
    f 0 ls
;

let rec nth index ls =
    if empty? ls || index < 0 then 
        raise
    else if index = 0 then
        head ls
    else
        nth (index - 1) (tail ls)
;

// ======================
// List sorting functions
// ======================

let rec sort ls =
    if empty? ls then
        nil
    else
        let first = head ls;
        let rest = tail ls;
        (sort $ filter (\x -> x <= first) rest) 
        @ [first] @ 
        (sort $ filter (\x -> x > first) rest)
;

// ======================
// List zipping functions
// ======================

let rec zip x y =
    if empty? x || empty? y then
        nil
    else
        (head x, head y) :: zip (tail x) (tail y)
;

let rec zipWith f x y =
    if empty? x || empty? y then
        nil
    else
        f (head x) (head y) :: zipWith f (tail x) (tail y)
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
    if empty? s then
        raise
    else
        let rec f (s: String): Int =
            if empty? s then
                0
            else 
                let x = 
                    if head s = '0' then 0
                    else if head s = '1' then 1
                    else if head s = '2' then 2
                    else if head s = '3' then 3
                    else if head s = '4' then 4
                    else if head s = '5' then 5
                    else if head s = '6' then 6
                    else if head s = '7' then 7
                    else if head s = '8' then 8
                    else if head s = '9' then 9
                    else raise;
            x + 10 * f (tail s)
        ;
        if head s = '-' then
            negate (f (reverse (tail s)))
        else
            f (reverse s)
;

let rec printInt (i: Int): String =
    let printDigit d =
        if d = 0 then "0"
        else if d = 1 then "1"
        else if d = 2 then "2"
        else if d = 3 then "3"
        else if d = 4 then "4"
        else if d = 5 then "5"
        else if d = 6 then "6"
        else if d = 7 then "7"
        else if d = 8 then "8"
        else "9"
    ;
    if i < 0 then   
        '-' :: printInt (-i)
    else if i < 10 then
        printDigit i
    else 
        let c = printDigit (i % 10);
        (printInt (i/10)) @ c
;

let parseBool (s: String): Bool =
    if s = "true" then
        true
    else if s = "false" then
        false
    else 
        raise
;

let printBool (b: Bool): String =
    if b then
        "true"
    else
        "false"
;

"""

let compiled = compiled

let loadCompiled term =
   let lib = loadArray compiled
   replaceXLib lib term