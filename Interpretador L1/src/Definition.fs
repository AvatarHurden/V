module Definition

type Trait =
    | Equatable
    | Orderable

type Type =
    | VarType of string * Trait list
    | Int
    | Bool
    | Char
    | Unit
    | Function of Type * Type
    | List of Type
    | Record of string list option * Type list


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
    | Record (names, types) ->
        match trt with
        | Equatable ->
            let foldF (valid, newTypes) typ =
                match valid, validateTrait trt typ with
                | false, _ -> false, []
                | true, Some typ -> valid, typ :: newTypes
                | true, None -> false, []
            let valid, types = List.fold foldF (true, []) types
            if valid then
                Some <| Record (names, List.rev types)
            else
                None 
        | Orderable -> None
    | VarType (x, traits) ->
        if List.exists ((=) trt) traits then
            Some typ
        else
            Some <| VarType (x, trt::traits)

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

type ProjectionType =
    | IntProjection of int
    | StringProjection of string

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
    | Record of string list option * term list
    | Project of ProjectionType * term

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
    | ResRecord of string list option * result list
and
    env = Map<Ident, result>

exception WrongExpression of string
