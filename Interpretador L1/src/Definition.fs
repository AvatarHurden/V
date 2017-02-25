module Definition

exception ParseException of string
exception EvalException of string
exception TypeException of string

type Trait =
    | Equatable
    | Orderable
    | TuplePosition of int * Type
    | RecordLabel of string * Type

and Type =
    | VarType of string * Trait list
    | Int
    | Bool
    | Char
    | Unit
    | Function of Type * Type
    | List of Type
    | Tuple of Type list
    | Record of (string * Type) list

let rec mapOption f ls =
    match ls with
    | [] -> Some []
    | x :: rest ->
        match f x with
        | Some x' -> 
            match mapOption f rest with
            | None -> None
            | Some rest' -> Some <| x' :: rest'
        | None -> None

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
    
type VarPattern = Var of Pattern * Type option

and Pattern =
    | XPattern of Ident
    | IgnorePattern
    | TuplePattern of VarPattern list
    | RecordPattern of (string * VarPattern) list
    | NilPattern
    | ConsPattern of VarPattern * VarPattern

type term =
    | B of bool
    | Skip
    | I of int
    | C of char
    | OP of term * op * term
    | Cond of term * term * term
    | X of Ident
    | Fn of VarPattern * term
    | RecFn of Ident * (Type option) * VarPattern * term
    | Let of VarPattern * term * term
    | Nil
    | IsEmpty of term
    | Head of term
    | Tail of term
    | Raise
    | Try of term * term
    | Output of term
    | Input
    | Tuple of term list
    | Record of (string * term) list
    | ProjectIndex of int * term
    | ProjectName of string * term

type result =
    | ResB of bool
    | ResSkip
    | ResI of int
    | ResC of char
    | ResRaise
    | ResNil
    | ResCons of result * result
    | ResClosure of VarPattern * term * env
    | ResRecClosure of Ident * VarPattern * term * env
    | ResTuple of result list
    | ResRecord of (string * result) list
and
    env = Map<Ident, result>

