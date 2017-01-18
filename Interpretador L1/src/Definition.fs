module Definition

type Trait =
    | Equatable
    | Orderable

type Type =
    | VarType of string * Var
    | Int
    | Bool
    | Char
    | Unit
    | Function of Type * Type
    | List of Type

and Var =
    struct 
     val traits: Trait list
     val superTypes: Type list
     val subTypes: Type list
     new (traits, superTypes, subTypes) = {
        traits = traits
        superTypes = superTypes
        subTypes = subTypes
     }
    end

    new (traits) = Var (traits, [], [])

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

let rec validateTrait trt typ =
    match typ with
    | Int ->
        match trt with
        | Orderable | Equatable -> Some Int
    | Bool ->
        match trt with
        | Equatable -> Some Bool
        | Orderable -> None
    | Char ->
        match trt with
        | Orderable | Equatable -> Some Char
    | Unit ->
        match trt with
        | Orderable | Equatable -> None
    | Function (typ1, typ2) ->
        match trt with
        | Orderable | Equatable -> None
    | List typ1 ->
        match trt with
        | Orderable | Equatable ->
            match validateTrait trt typ1 with
            | None -> None
            | Some typ1 -> Some <| List typ1
    | VarType (x, {traits = traits}) ->
        if List.exists ((=) trt) traits then
            Some typ
        else
            Some <| VarType (x, Var <| trt::traits)

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
    | B of bool
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
    | ResClosure of Ident * term * env
    | ResRecClosure of Ident * Ident * term * env
    | ResTuple of result list
    | ResRecord of (string * result) list
and
    env = Map<Ident, result>

exception WrongExpression of string
