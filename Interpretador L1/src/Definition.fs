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
    | RecFn of Ident * (Type option) * Ident * (Type option) * term
    | Let of Ident * (Type option) * term * term
    | Nil
    | IsEmpty of term
    | Head of term
    | Tail of term
    | Raise
    | Try of term * term

type result =
    | ResTrue
    | ResFalse
    | ResI of int
    | ResRaise
    | ResNil
    | ResCons of result * result
    | ResClosure of Ident * term * env
    | ResRecClosure of Ident * Ident * term * env
and
    env = Map<Ident, result>

exception WrongExpression of string
