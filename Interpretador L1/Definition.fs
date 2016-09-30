module Definition

type Type =
    | X of string
    | Int
    | Bool
    | Function of Type * Type
    | List of Type

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
    | Application
    | Cons

type Ident = string
    
type term =
    | True
    | False
    | I of int
    | OP of term * op * term
    | Cond of term * term * term
    | X of Ident
    | Fn of Ident * Type * term
    | Let of Ident * Type * term * term
    | LetRec of Ident * Type * Type * Ident * term * term
    | Nil
    | IsEmpty of term
    | Head of term
    | Tail of term
    | Raise
    | Try of term * term

let V(term) =
    match term with
    | True | False | I(_) | Fn(_, _, _) 
    | Nil | OP(_, Cons, _) -> true
    | _ -> false

exception WrongExpression of string
