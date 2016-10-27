module Definition

type Type =
    | X of string
    | Int
    | Bool
    | Char
    | Function of Type * Type
    | List of Type

type Trait =
    | Equatable
    | Orderable

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
    | C of char
    | OP of term * op * term
    | Cond of term * term * term
    | X of Ident
    | Fn of Ident * (Type option) * term
    | Let of Ident * (Type option) * term * term
    | LetRec of Ident * (Type option) * (Type option) * Ident * term * term
    | Nil
    | IsEmpty of term
    | Head of term
    | Tail of term
    | Raise
    | Try of term * term

    | Closure of Ident * term * env
    | RecClosure of Ident * Ident * term * env
and
    env = Map<Ident, term>

let V(term) =
    match term with
    | True | False | I(_) | Nil | OP(_, Cons, _) 
    | C _
    | Closure(_, _, _) | RecClosure(_, _, _, _) -> true
    | _ -> false

exception WrongExpression of string
