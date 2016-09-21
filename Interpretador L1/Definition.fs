module Definition

type Type =
    | X of string
    | Int
    | Bool
    | Function of Type * Type

type n =
    | I of int

type b =
    | True
    | False

type v =
    | B of b
    | N of n

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
    | V of v
    | OP of term * op * term
    | Cond of term * term * term
    | X of Ident
    | App of term * term
    | Fn of Ident * Type * term
    | Let of Ident * Type * term * term
    | LetRec of Ident * Type * Type * Ident * term * term
    | Nil
    | Cons of term * term
    | IsEmpty of term
    | Head of term
    | Tail of term
    | Raise
    | Try of term * term

exception WrongExpression