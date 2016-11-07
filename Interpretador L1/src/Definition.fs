module Definition

type Type =
    | VarType of string
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

let rec V(term) =
    match term with
    | True | False |  I _ | Nil | Raise 
    | Closure (_, _, _) | RecClosure (_, _, _, _) -> true
    | OP(t1, Cons, t2) -> V(t1) && V(t2)
    | _ -> false

exception WrongExpression of string
