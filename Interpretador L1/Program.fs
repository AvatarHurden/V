// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

type Type =
    | X of string
    | Int
    | Bool
    | Function of Type * Type

type n =
    | N of int

type b =
    | True
    | False
    
type op =
    | Add
    | Subtract
    | Multiply
    | Divide
    | LessThan
    | LessOrEqual
    | Equal
    | Different
    | GreaterOrEqual
    | GreaterThan

type Ident =
    | X of string

type term =
    | N of n
    | B of b
    | OP of term * op * term
    | Cond of term * term * term
    | X of Ident
    | App of term * term
    | Fn of Ident * Type * term
    | Let of Ident * Type * term * term
    | LetRec of Type * Type * Ident * term * term
    | Nil
    | Cons of term * term
    | IsEmpty of term
    | Head of term
    | Tail of term
    | Raise
    | Try of term * term

[<EntryPoint>]
let main argv = 
    printfn "%A" argv
    0 // return an integer exit code
