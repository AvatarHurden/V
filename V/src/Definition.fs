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

type Ident = string
    
type VarPattern = Pat of Pattern * Type option

and Pattern =
    | XPat of Ident
    | IgnorePat
    | BPat of bool
    | IPat of int
    | CPat of char
    | TuplePat of VarPattern list
    | RecordPat of bool * (string * VarPattern) list
    | NilPat
    | ConsPat of VarPattern * VarPattern

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

    | Cons

let numArgs =
    function
    | Negate -> 1
    | _ -> 2

type Function =
    | BuiltIn of BuiltIn
    | Lambda of VarPattern * term
    | Recursive of Ident * (Type option) * VarPattern * term

and term =
    | B of bool
    | I of int
    | C of char
    | X of Ident
    | Fn of Function
    | App of term * term
    | Match of term * (VarPattern * term option * term) list
    | Let of VarPattern * term * term
    | Nil
    | Raise
    | Tuple of term list
    | Record of (string * term) list

type ResFunction = Function * env

and result =
    | ResB of bool
    | ResI of int
    | ResC of char
    | ResFn of ResFunction
    | ResPartial of BuiltIn * (term * env) list
    | ResRaise
    | ResNil
    | ResCons of result * result
    | ResTuple of result list
    | ResRecord of (string * result) list
and
    env = Map<Ident, result>


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

type ExFunction =
    | ExBuiltIn of BuiltIn
    | ExLambda of ExVarPattern list * ExTerm
    | ExRecursive of Ident * ExVarPattern list * ExType option * ExTerm

and ExTerm = 
    | ExB of bool
    | ExI of int
    | ExC of char
    //| ExOP of ExTerm * op * ExTerm
    | ExX of Ident
    | ExFn of ExFunction
    | ExApp of ExTerm * ExTerm
    | ExMatch of ExTerm * (ExVarPattern * ExTerm option * ExTerm) list
    | ExLet of ExDeclaration * ExTerm
    | ExNil
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
    match ls with
    | [] -> Some []
    | x :: rest ->
        match f x with
        | Some x' -> 
            match mapOption f rest with
            | None -> None
            | Some rest' -> Some <| x' :: rest'
        | None -> None

//#endregion
