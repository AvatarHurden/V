module TypeInference

open System.Collections.Generic
open Definition
open Printer

exception InvalidType of string

// This is a stand-in for VarType, to avoid having to match types
type FreeVar = string * Trait list

type Unified(subs, traits) =
    member that.substitution: Map<string, Type> = subs
    member that.traits: Map<string, Trait list> = traits

type Constraint =
    | Equals of Type * Type

type EnvAssociation =
    | Simple of Type
    | Universal of FreeVar list * Type

let mutable varType = 0
let getVarType traits =
    let newType = varType
    varType <- varType + 1
    VarType (sprintf "VarType%d" newType, traits)

// Polimorphism Functions

let rec getFreeVars typ env: FreeVar list =
    let f typ = 
        match typ with
        | Int -> []
        | Bool -> []
        | Char -> []
        | Unit -> []
        | List(t1) -> getFreeVars t1 env
        | Function(t1, t2) -> getFreeVars t1 env @ getFreeVars t2 env
        | VarType (x, traits) -> 
            let freeChecker = 
                (fun x' assoc -> 
                    match assoc with
                    | Simple (VarType (x1, traits)) -> x1 = x
                    | _ -> false)
            if Map.exists freeChecker env then
                []
            else
                [x, traits]
    in Set(f typ) |> Set.toList

let substituteInType subs typ' =
    let x, typ = subs
    let rec f s =
        match s with
        | Int -> Int
        | Bool -> Bool
        | Char -> Char
        | Unit -> Unit
        | List(s1) -> List(f s1)
        | Function(s1, s2) -> Function(f s1, f s2)
        | VarType(id, traits) ->
            if id = x then
                typ
            else
                s
    in f typ'

let substituteInConstraints subs constraints =
    let x, typ = subs
    let f cons =
        match cons with
        | Equals (s, t) ->
            Equals (substituteInType subs s, substituteInType subs t)
    List.map f constraints

let rec occursIn x typ =
    match typ with
    | Int
    | Bool 
    | Char
    | Unit -> false
    | List(t1) -> occursIn x t1
    | Function(t1, t2) -> occursIn x t1 || occursIn x t2
    | VarType(id, ls) -> id = x

let rec validateTraits traits typ =
    match typ with
    | None -> None
    | Some typ' -> 
        match traits with
        | [] -> Some typ'
        | trt::rest -> validateTraits rest <| validateTrait trt typ'

let rec replaceVarTypes (vars: FreeVar list) constraints =
    match vars with
    | [] -> constraints
    | (x, traits) :: rest ->
        replaceVarTypes rest <| 
            substituteInConstraints (x, VarType (x, traits)) constraints

let rec addTraitsToUnified (vars: FreeVar list) (unified: Unified) =
    match vars with
    | [] -> unified
    | (x, traits) :: rest ->
        new Unified(unified.substitution, unified.traits.Add(x, traits))

let rec unify constraints =
//    for c in constraints do
//        match c with
//        | Equals (s,t) ->
//            printfn "%A = %A" (printType s) (printType t)
//    printfn ""
    match constraints with
    | [] -> new Unified(Map.empty, Map.empty)
    | first::rest ->
        match first with
        | Equals (s, t) ->
            match s, t with
            | s, t when s = t -> unify rest
            | VarType (x, traits), t 
            | t, VarType (x, traits) ->
                if occursIn x t then
                    sprintf "Circular constraints" |> InvalidType |> raise
                else
                    let t' = validateTraits traits <| Some t
                    match t' with
                    | None ->
                        sprintf "Can not satisfy constraints %A for %A" traits t 
                            |> InvalidType |> raise
                    | Some t' ->
                        let replacedX = (substituteInConstraints (x, t') rest)
                        let unified = 
                            if t = t' then
                                unify replacedX
                            else
                                let free = getFreeVars t' Map.empty
                                let unified = unify <| replaceVarTypes free replacedX
                                addTraitsToUnified free unified
                        new Unified(unified.substitution.Add(x, t'), unified.traits) 
            | List s1, List t1 -> 
                unify <| rest @ [Equals (s1, t1)]
            | Function(s1, s2), Function(t1, t2) -> 
                unify <| rest @ [Equals (s1, t1); Equals (s2, t2)]
            | _ -> 
                raise <| InvalidType "Unsolvable constraints"

let rec applyType typ (unified: Unified) =
    match typ with
    | Int -> Int
    | Bool -> Bool
    | Char -> Char
    | Unit -> Unit
    | List(t1) -> 
        List(applyType t1 unified)
    | Function(t1, t2) -> 
        Function(applyType t1 unified, applyType t2 unified)
    | VarType(x, traits) -> 
        if unified.substitution.ContainsKey x then
            applyType (unified.substitution.Item x) unified
        else if unified.traits.ContainsKey x then
            VarType (x, unified.traits.Item x)
        else
            typ
            

let rec applyTypeToEnv env uni: Map<string, EnvAssociation> =
    let f key value =
        match value with
        | Simple typ ->
            Simple <| applyType typ uni
        | Universal _ -> 
            value
    Map.map f env

// Constraint Collection Functions

let findId id (e: Map<string, EnvAssociation>) =
    if e.ContainsKey id then
        match e.[id] with
        | Simple typ ->
            typ, []
        | Universal (freeVars, typ) ->
            let f = (fun (x, traits) -> x, getVarType traits)
            let newVars = List.map f freeVars
            List.fold 
                (fun acc subs -> substituteInType subs acc)
                typ newVars, []
    else
        sprintf "Identifier %A undefined" id |> InvalidType |> raise

// collectConstraints term environment constraints
let rec collectConstraints term (env: Map<string, EnvAssociation>) =
    match term with
    | B true ->
        Bool, []
    | B false ->
        Bool, []
    | I(i) ->
        Int, []
    | C(c) ->
        Char, []
    | Skip ->
        Unit, []
    | OP(t1, Application, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        let x = getVarType []
        x, c1 @ c2 @ [Equals (typ1, Function (typ2, x))]
    | OP(t1, Cons, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        typ1 |> List, c1 @ c2 @ [Equals (List typ1, typ2)]
    | OP(t1, Sequence, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        typ2, c1 @ c2 @ [Equals (typ1, Unit)]
    | OP(t1, Equal, t2) 
    | OP(t1, Different, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        let varTyp = getVarType [Equatable]
        Bool, c1 @ c2 @ [Equals (typ1, typ2); Equals (varTyp, typ2)]
    | OP(t1, LessThan, t2)
    | OP(t1, LessOrEqual, t2)
    | OP(t1, GreaterOrEqual, t2)
    | OP(t1, GreaterThan, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        let varTyp = getVarType [Orderable]
        Bool, c1 @ c2 @ [Equals (typ1, typ2); Equals (varTyp, typ2)]
    | OP(t1, Add, t2)
    | OP(t1, Subtract, t2)
    | OP(t1, Multiply, t2)
    | OP(t1, Divide, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        Int, c1 @ c2 @ [Equals (typ1, Int); Equals (typ2, Int)]
    | OP(t1, And, t2)
    | OP(t1, Or, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        Bool, c1 @ c2 @ [Equals (typ1, Bool); Equals (typ2, Bool)]
    | Cond(t1, t2, t3) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        let typ3, c3 = collectConstraints t3 env
        typ2, c1 @ c2 @ c3 @ [Equals (typ1, Bool); Equals (typ2, typ3)]
    | X(id) ->
        findId id env
    | Fn(id, Some typ, t1) ->
        let typ1, c1 = collectConstraints t1 <| env.Add(id, Simple typ)
        Function(typ, typ1), c1
    | Fn(id, None, t1) ->
        let paramTyp = getVarType []
        let typ1, c1 = collectConstraints t1 <| env.Add(id, Simple paramTyp)
        Function(paramTyp, typ1), c1
    | RecFn(id1, Some typ1, id2, Some typ2, t1) ->
        let env1 = env.Add(id1, Simple <| Function(typ2, typ1)).Add(id2, Simple typ2)
        let typ1', c1 = collectConstraints t1 env1
        Function (typ2, typ1), c1 @ [Equals (typ1', typ1)]
    | RecFn(id1, None, id2, None, t1) ->
        let fType = getVarType []
        let paramTyp = getVarType []
        let typ1, c1 = collectConstraints t1 <| env.Add(id1, Simple fType).Add(id2, Simple paramTyp)
        Function (paramTyp, typ1), c1 @ [Equals (fType, Function (paramTyp, typ1))]
    | RecFn(id1, _, id2, _, t1) as t ->
        sprintf "Invalid recursive function defintion at %A" t |> InvalidType |> raise
    | Let(id, Some typ, t1, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 <| env.Add(id, Simple typ)
        typ2, c1 @ c2 @ [Equals (typ, typ1)]
    | Let(id, None, t1, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let uni = unify c1
        let typ1' = applyType typ1 uni

        let freeVars = getFreeVars typ1' <| applyTypeToEnv env uni
        let isFn = match typ1' with | Function _ -> true | _ -> false

        let assoc = 
            if freeVars.IsEmpty || not isFn then
                Simple typ1'
            else
                Universal (freeVars, typ1')
        let typ2, c2 = collectConstraints t2  <| env.Add(id, assoc)

        typ2, c1 @ c2
    | Nil ->
        List <| getVarType [], []
    | Head(t1) ->
        let typ1, c1 = collectConstraints t1 env
        let x = getVarType [] in
        x, c1 @ [Equals (typ1, List x)]
    | Tail(t1) ->
        let typ1, c1 = collectConstraints t1 env
        let x = getVarType [] in
        List x, c1 @ [Equals (typ1, List x)]
    | IsEmpty(t1) ->
        let typ1, c1 = collectConstraints t1 env
        Bool, c1 @ [Equals (typ1, List <| getVarType [])]
    | Raise ->
        getVarType [], []
    | Try(t1, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        typ2, c1 @ c2 @ [Equals (typ1, typ2)]
    | Input ->
        List Char, []
    | Output(t1) ->
        let typ1, c1 = collectConstraints t1 env
        Unit, c1 @ [Equals (typ1, List Char)]


let typeInfer t =
    let typ, c = collectConstraints t Map.empty
    let substitutions = unify c
    applyType typ substitutions
