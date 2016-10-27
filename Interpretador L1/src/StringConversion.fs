module StringConversion

open Definition
open System

let rec toString term =
    match term with
    | I i -> sprintf "%A" i
    | True -> "true"
    | False -> "false"
    | Nil -> "[]"
    | OP(_, Cons, _) -> "[" + (toStringList term) + "]"
    | t ->
        printfn "Unexpected term at %A" t
        ""

and toStringList term =
    match term with
    | OP(t1, Cons, Nil) -> toString t1
    | OP(t1, Cons, t2) -> toString t1 + "," + toStringList t2
    | t ->
        printfn "Unexpected term at %A" t
        ""

let rec fromString (string: string) =
    let string = string.TrimStart()
    if string.StartsWith "-" || Char.IsDigit(string.Chars(0)) then
        ""
    elif string.StartsWith "[" then
        ""
    elif string.StartsWith "true" then
        ""
    elif string.StartsWith "false" then
        ""
    else
        ""
    