﻿module Definition

exception ParseException of string
exception EvalException of string
exception TypeException of string

exception LibNotFound of string
exception UncompiledLib of string

type Trait =
    | Equatable
    | Orderable
    | RecordLabel of string * Type

and ConstructorType =
    | Int
    | Bool
    | Char
    | List of Type
    //| Custom of string * Type list

and Type =
    | VarType of string * Trait list
    | ConstType of ConstructorType
//    | Int
//    | Bool
//    | Char
    | Function of Type * Type
//    | List of Type
    | Tuple of Type list
    | Record of (string * Type) list

type Ident = string
    
type Constructor =
    | I of int
    | C of char
    | B of bool
    | Nil
    | Cons
    //| Custom of string

type VarPattern = Pat of Pattern * Type option

and Pattern =
    | XPat of Ident
    | IgnorePat
    | ConstructorPat of Constructor * VarPattern list
    | TuplePat of VarPattern list
    | RecordPat of bool * (string * VarPattern) list
    //| ConsPat of VarPattern * VarPattern

type BuiltIn =
    | Get
    | RecordAccess of string

    | Add
    | Subtract
    | Multiply
    | Divide
    | Negate

    | LessThan
    | LessOrEqual
    | Equal
    | Different
    | GreaterOrEqual
    | GreaterThan

    | And
    | Or

let numArgs =
    function
    | Negate -> 1
    | _ -> 2

type Function =
    | Lambda of VarPattern * term
    | Recursive of Ident * (Type option) * VarPattern * term
    
and term =
    | Constructor of Constructor
    | BuiltIn of BuiltIn
    | X of Ident
    | Fn of Function
    | App of term * term
    | Match of term * (VarPattern * term option * term) list
    | Let of VarPattern * term * term
    | Raise
    | Tuple of term list
    | Record of (string * term) list

type ResFunction = Function * Env

and ResPartialApp =
    | AppBuiltIn of BuiltIn
    | AppConstructor of Constructor

and result =
    | ResFn of ResFunction
    | ResPartial of ResPartialApp * result list
    | ResConstructor of Constructor * result list
    | ResRaise
    //| ResCons of result * result
    | ResTuple of result list
    | ResRecord of (string * result) list
and

//#region Evaluation Environment

    Env =
    {numArgs: Map<Constructor, int>;
     groups: Set<Constructor> list;
     ids: Map<Ident, result>}

     member this.areCompatible c1 c2 =
        match c1, c2 with
        | I _, I _ -> true
        | _, I _
        | I _, _ -> false
        | C _, C _ -> true
        | _, C _
        | C _, _ -> false
        | B _, B _ -> true
        | _, B _
        | B _, _ -> false
        | c1, c2 ->
            let f x = fun (s: Set<Constructor>) -> s.Contains x
            match List.tryFind (f c1) this.groups with
            | None -> sprintf "Constructor %A is not in any group" c1 |> EvalException |> raise
            | Some s -> s.Contains c2

    member this.numArgsFor c =
        match c with
        | I _ | B _ | C _ -> 0
        | c -> 
            match this.numArgs.TryFind c with
            | None -> sprintf "Constructor %A does not have a number of arguments" c |> EvalException |> raise
            | Some i -> i

    member this.addId id result =
        let newIds = this.ids.Add(id, result)
        {this with ids = newIds}


let defaultEnv = 
    {numArgs = 
        [Cons, 2; 
        Nil, 0] 
        |> Map.ofList
     groups = 
        [
            [Nil; Cons] |> Set.ofList
        ]
     ids = Map.empty}

//#endregion

//#region Library and Parsing

type Operator =
    | BuiltInOp of BuiltIn
    | CustomOp of string

type Assoc =
    | Left
    | Right
    | Non

type Fixity =
    | Prefix of int * Operator
    | Infix of int * Assoc * Operator

type OperatorSpec =
    | OpSpec of fix:Fixity * string:string

type LibComponent = VarPattern * term

type TranslationEnv = 
    {typeAliases: Map<string, Type>}

    member this.addTypeAlias name typ =
        let aliases = this.typeAliases.Add (name, typ)
        {this with typeAliases = aliases}

let emptyTransEnv = {typeAliases = Map.empty}

type Library =
    {terms: LibComponent list;
    translationEnv: TranslationEnv;
    operators: OperatorSpec list}

let emptyLib = {terms = []; operators = []; translationEnv = emptyTransEnv}

//#endregion


//#region Extended Language

type ExType =
    | ExVarType of string * Trait list
    | ExInt
    | ExBool
    | ExChar
    | ExFunction of ExType * ExType
    | ExList of ExType
    | ExTupleType of ExType list
    | ExRecordType of (string * ExType) list

    | ExTypeAlias of string

type ExVarPattern = ExPattern * ExType option

and ExPattern =
    | ExXPat of Ident
    | ExIgnorePat
    | ExBPat of bool
    | ExIPat of int
    | ExCPat of char
    | ExTuplePat of ExVarPattern list
    | ExRecordPat of bool * (string * ExVarPattern) list
    | ExNilPat
    | ExConsPat of ExVarPattern * ExVarPattern
    | ExListPat of ExVarPattern list
    
type ExConstructor =
    | ExI of int
    | ExC of char
    | ExB of bool
    | ExNil
    | ExCons

type ExFunction =
    | ExBuiltIn of BuiltIn
    | ExLambda of ExVarPattern list * ExTerm
    | ExRecursive of Ident * ExVarPattern list * ExType option * ExTerm
    | ExConstructor of ExConstructor

and ExTerm = 
    | ExX of Ident
    | ExFn of ExFunction
    | ExApp of ExTerm * ExTerm
    | ExMatch of ExTerm * (ExVarPattern * ExTerm option * ExTerm) list
    | ExLet of ExDeclaration * ExTerm
    | ExRaise
    | ExTuple of ExTerm list
    | ExRecord of (string * ExTerm) list

    | ExListTerm of ExTerm list
    | Cond of ExTerm * ExTerm * ExTerm
    | Range of ExTerm * ExTerm option * ExTerm
    | Comprehension of ExTerm * ExVarPattern * ExTerm

and ExDeclaration =
    | DeclConst of ExVarPattern * ExTerm
    | DeclFunc of isRec:bool * Ident * ExVarPattern list * ExType option * ExTerm
    | DeclImport of LibComponent list
    | DeclAlias of string * ExType

//#endregion

//#region Helper Functions

let flip f a b = f b a

let rec mapOption f ls =
    let f' acc x = 
        match acc with
        | None -> None
        | Some acc -> 
            match f x with
            | Some x -> Some <| x :: acc
            | None -> None
    List.fold f' (Some []) <| List.rev ls

let rec foldOption f acc ls =
    let f' acc x = 
        match acc with
        | None -> None
        | Some acc -> f acc x
    List.fold f' acc ls

//#endregion
