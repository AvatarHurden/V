module Definition

type Type =
    | VarType of string
    | Int
    | Bool
    | Char
    | Unit
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
    | Sequence
    | And
    | Or

type Ident = string
    
type term =
    | True
    | False
    | Skip
    | I of int
    | C of char
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
    | Output of term
    | Input

type result =
    | ResTrue
    | ResFalse
    | ResSkip
    | ResI of int
    | ResC of char
    | ResRaise
    | ResNil
    | ResCons of result * result
    | ResClosure of Ident * term * env
    | ResRecClosure of Ident * Ident * term * env
and
    env = Map<Ident, result>

exception WrongExpression of string
