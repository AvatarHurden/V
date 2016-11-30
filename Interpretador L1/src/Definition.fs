module Definition

type Trait =
    | Equatable
    | Orderable

type Type =
    | VarType of Var
    | Int
    | Bool
    | Char
    | Unit
    | Function of Type * Type
    | List of Type
    | Record of string seq option * Type seq
    
and Var =
    struct 
     val name: string
     val traits: Trait list
     val supertypes: Type list
     new (name, traits, supertypes) = {
        name = name
        traits = traits
        supertypes = supertypes
     }
    end

    new (name) = Var (name, [], [])
    new (name, traits) = Var (name, traits, [])
    new (name, supertypes) = Var (name, [], supertypes)

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
                | false, _ -> false, Seq.empty
                | true, Some typ -> valid, Seq.append newTypes [|typ|]
                | true, None -> false, Seq.empty
            let valid, types = Seq.fold foldF (true, Seq.empty) types
            if valid then
                Some <| Record (names, types)
            else
                None 
        | Orderable -> None
    | VarType {name = x; traits = traits} ->
        if List.exists ((=) trt) traits then
            Some typ
        else
            Var(x, trt::traits) |> VarType |> Some

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
    | Record of string seq option * term seq
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
    | ResRecord of string seq option * result seq
and
    env = Map<Ident, result>

exception WrongExpression of string
