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
    | Monad

and ConstructorType =
    | Int
    | Bool
    | Char
    | List
    | Tuple of components:int
    | IOType
    | Unit
    //| Custom of string * Type list

and Type =
    | VarType of string * Trait list
    | ConstType of ConstructorType * Type list
    | Function of Type * Type
    | Accessor of io:Type * record:Type
    | Record of (string * Type) list

type Ident = string
    
type Constructor =
    | I of int
    | C of char
    | B of bool
    | Nil
    | Cons
    | Tuple of components:int
    | IO
    | Void
    //| Custom of string

type VarPattern = Pat of Pattern * Type option

and Pattern =
    | XPat of Ident
    | IgnorePat
    | ConstructorPat of Constructor * VarPattern list
    | RecordPat of bool * (string * VarPattern) list

type BuiltIn =
    | Id

    | Get
    | Set
    | Stack
    | Distort

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

    | Read
    | Write

    | Return
    | Bind

type Function =
    | Lambda of Ident * term
    | Recursive of Ident * (Type option) * Ident * term

and Path =
    | Component of string
    //| Stacked of Path * Path
    | Joined of term list
    //| Distorted of Path * getter:term * setter:term

and Declaration =
    | Term of VarPattern * term
    | Data of name:string * typeVariables:string list * constructors:(string * Type list) list

and term =
    | Constructor of Constructor
    | BuiltIn of BuiltIn
    | X of Ident
    | RecordAccess of Path
    | Fn of Function
    | App of term * term
    | Match of term * (VarPattern * term option * term) list
    | Let of VarPattern * term * term
    | Raise
    | Record of (string * term) list

type ResFunction = Function * Env

and ResPath = 
    | ResComponent of string
    | ResStacked of ResPath * ResPath
    | ResJoined of ResPath list
    | ResDistorted of ResPath * getter:result * setter:result

and ResPartialApp =
    | AppBuiltIn of BuiltIn
    | AppConstructor of Constructor

and result =
    | ResRecordAcess of ResPath
    | ResFn of ResFunction
    | ResPartial of ResPartialApp * result list
    | ResConstructor of Constructor * result list
    | ResRaise
    | ResRecord of (string * result) list
and

//#region Evaluation Environment
    Env =
    {numArgs: Map<Constructor, int>;
     groups: (Constructor list) list;
     ids: Map<Ident, result>}

let defaultEnv = 
    {numArgs = 
        [Cons, 2 
         Nil, 0 
         Void, 0
         IO, 1]
        |> Map.ofList
     groups = 
        [
            [Nil; Cons]
        ]
     ids = Map.empty}

//#endregion

//#region Library and Parsing

type Operator =
    | BuiltInOp of BuiltIn
    | ConstructorOp of Constructor
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

//#endregion


//#region Extended Language

type ExType =
    | ExVarType of string * Trait list
    | ExConstType of ConstructorType * ExType list
    | ExFunction of ExType * ExType
    | ExAccessor of ExType * ExType
    | ExRecordType of (string * ExType) list

    | ExTypeAlias of string

type ExVarPattern = ExPattern * ExType option

and ExPattern =
    | ExXPat of Ident
    | ExIgnorePat
    | ExRecordPat of bool * (string * ExVarPattern) list
    | ExConstructorPat of Constructor * ExVarPattern list

    | ExListPat of ExVarPattern list
    
type ExConstructor =
    | ExI of int
    | ExC of char
    | ExB of bool
    | ExNil
    | ExCons
    | ExTuple of components: int

type ExFunction =
    | ExLambda of ExVarPattern list * ExTerm
    | ExRecursive of Ident * ExVarPattern list * ExType option * ExTerm

and ExTerm = 
    | ExX of Ident
    | ExRecordAccess of ExDotAccessor
    | ExBuiltIn of BuiltIn
    | ExConstructor of Constructor
    | ExFn of ExFunction
    | ExApp of ExTerm * ExTerm
    | ExMatch of ExTerm * (ExVarPattern * ExTerm option * ExTerm) list
    | ExLet of ExDeclaration * ExTerm
    | ExRaise
    | ExRecord of (string * ExTerm) list
    
    | ExTuple of ExTerm list
    | ExListTerm of ExTerm list
    | Cond of ExTerm * ExTerm * ExTerm
    | Range of ExTerm * ExTerm option * ExTerm
    | Comprehension of ExTerm * ExVarPattern * ExTerm
    
    | DotAccess of string * ExDotAccessor
    | Update of ExUpdateTerm list

    | Do of ExDoTerm list

and ExDoTerm =
    | DoBind of ExVarPattern * ExTerm
    | DoTerm of ExTerm
    | DoDeclaration of ExDeclaration

and ExDeclaration =
    | DeclConst of ExVarPattern * ExTerm
    | DeclFunc of isRec:bool * Ident * ExVarPattern list * ExType option * ExTerm
    | DeclImport of LibComponent list
    | DeclAlias of string * ExType
    
and ExDotAccessor =
    | DotStacked of ExDotAccessor * ExDotAccessor
    | DotLabel of string
    | DotString of string
    | DotJoined of ExDotAccessor list

and ExUpdateTerm =
    | FieldModify of ExDotAccessor * ExTerm
    | FieldSet of ExDotAccessor * ExTerm
    | Declaration of ExDeclaration

//#endregion

//#region Helper Functions

let flip f a b = f b a

let curry f a b = f (a, b)
let uncurry f (a, b) = f a b

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
