module Definition

exception ParseException of string
exception EvalException of string
exception TypeException of string

exception LibNotFound of string
exception UncompiledLib of string

type Trait =
    | Equatable
    | Orderable
    | RecordLabel of string * Type

and Type =
    | VarType of string * Trait list
    | Int
    | Bool
    | Char
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
    
type Ident = string
    
type VarPattern = Pat of Pattern * Type option

and Pattern =
    | XPat of Ident
    | IgnorePat
    | BPat of bool
    | IPat of int
    | CPat of char
    | TuplePat of VarPattern list
    | RecordPat of (string * VarPattern) list
    | NilPat
    | ConsPat of VarPattern * VarPattern

type term =
    | B of bool
    | I of int
    | C of char
    | OP of term * op * term
    | Cond of term * term * term
    | X of Ident
    | Fn of VarPattern * term
    | RecFn of Ident * (Type option) * VarPattern * term
    | Match of term * (VarPattern * term option * term) list
    | Let of VarPattern * term * term
    | Nil
    | Raise
    | Tuple of term list
    | Record of (string * term) list
    | ProjectName of string * term
    | RecordAccess of string * term * term

type result =
    | ResB of bool
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


type extendedOP =
    | Def of op
    | Custom of string

type Assoc =
    | Left
    | Right
    | Non

type Fixity =
    | Prefix of int * func:string
    | Infix of int * Assoc * extendedOP

type OperatorSpec =
    | OpSpec of fix:Fixity * string:string

type LibComponent = VarPattern * term

type Library =
    {terms: LibComponent list;
    operators: OperatorSpec list}

let emptyLib = {terms = []; operators = []}