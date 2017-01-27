﻿module TypeInference

open System.Collections.Generic
open Definition
open Printer

exception InvalidType of string

// This is a stand-in for VarType, to avoid having to match types
//type FreeVar = string * Trait list

type FreeVar = string * Trait list

type Substitution =
    | TypeSub of string * Type
    | NameSub of string * string

type Unified(subs, traits) =
    member that.substitution: Map<string, Type> = subs
    member that.traits: Map<string, Trait list> = traits

type Constraint =
    | Equals of Type * Type

type EnvAssociation =
    | Simple of Type
    | Universal of FreeVar list * Type

let mutable varType = 0
let getVarType unit =
    let newType = varType
    varType <- varType + 1
    sprintf "X%d" newType

//#region Free Variable Collection Functions
let rec getFreeVars typ env =
    let f typ = 
        match typ with
        | Int
        | Bool
        | Char
        | Unit -> []
        | List(t1) -> getFreeVars t1 env
        | Function(t1, t2) -> getFreeVars t1 env @ getFreeVars t2 env
        | Type.Tuple(types) -> 
            List.fold (fun acc x -> getFreeVars x env @ acc) [] types
        | Type.Record(pairs) -> 
            pairs |> List.unzip |> snd |> 
            List.fold (fun acc x -> getFreeVars x env @ acc) []
        | VarType (x, traits) ->
            let freeChecker = 
                (fun x' assoc -> 
                    match assoc with
                    | Simple (VarType (x1, traits)) -> x1 = x
                    | _ -> false)
            if Map.exists freeChecker env then
                getFreeVarsInTraits traits env
            else
                [x, traits] @ getFreeVarsInTraits traits env
    in Set(f typ) |> Set.toList

and getFreeVarsInTraits traits env =
    match traits with
    | [] -> []
    | first :: rest ->
        let first' =
            match first with
            | Equatable
            | Orderable -> []
            | TuplePosition (i, t) -> getFreeVars t env
            | RecordLabel (l, t) -> getFreeVars t env
        first' @ getFreeVarsInTraits rest env

//#endregion

//#region Type Substitution Functions
let rec substituteInType (sub: Substitution) typ' =
    match typ' with
    | Int -> Int
    | Bool -> Bool
    | Char -> Char
    | Unit -> Unit
    | List(s1) -> List(substituteInType sub s1)
    | Function(s1, s2) -> Function(substituteInType sub s1, substituteInType sub s2)
    | Type.Tuple(types) ->
        Type.Tuple <| List.map (substituteInType sub) types
    | Type.Record(pairs) ->
        let names, types = List.unzip pairs
        Type.Record (List.zip names <| List.map (substituteInType sub) types)
    | VarType(id, traits) ->
        match sub with
        | TypeSub (x, newTyp) ->
            if id = x then
                match newTyp with
                | VarType (newId, newTraits) -> 
                    VarType (newId, substituteInTraits sub newTraits)
                | typ -> typ
            else
               VarType (id, substituteInTraits sub traits)
        | NameSub (x, newX) ->
            if id = x then
                VarType (newX, substituteInTraits sub traits)
            else
                VarType (id, substituteInTraits sub traits)

and substituteInTraits (sub: Substitution) traits =
    match traits with
    | [] -> []
    | first :: rest ->
        let first' =
            match first with
            | Equatable -> Equatable
            | Orderable -> Orderable
            | TuplePosition (i, t) -> TuplePosition (i, substituteInType sub t)
            | RecordLabel (l, t) -> RecordLabel (l, substituteInType sub t)
        first' :: substituteInTraits sub rest

let substituteInConstraints sub constraints =
    let f cons =
        match cons with
        | Equals (s, t) ->
            Equals (substituteInType sub s, substituteInType sub t)
    List.map f constraints

//#endregion

//#region Trait Validation Functions
let rec validateTrait trt typ =
    match typ with
    | Int ->
        match trt with
        | Orderable | Equatable -> Some Int, []
        | TuplePosition _ | RecordLabel _ -> None, []
    | Bool ->
        match trt with
        | Equatable -> Some Bool, []
        | Orderable | TuplePosition _ | RecordLabel _ -> None, []
    | Char ->
        match trt with
        | Orderable | Equatable -> Some Char, []
        | TuplePosition _ | RecordLabel _ -> None, []
    | Unit ->
        match trt with
        | Orderable | Equatable
        | TuplePosition _ | RecordLabel _ -> None, []
    | Function (typ1, typ2) ->
        match trt with
        | Orderable | Equatable
        | TuplePosition _ | RecordLabel _ -> None, []
    | List typ1 ->
        match trt with
        | Orderable | Equatable ->
            match validateTrait trt typ1 with
            | None, cons -> None, cons
            | Some typ1, cons -> Some <| List typ1, cons
        | TuplePosition _ | RecordLabel _ -> None, []
    | Type.Tuple (types) ->
        match trt with
        | Equatable ->
            let f typ =
                match validateTrait trt typ with
                | None, [] -> None
                | Some typ', [] -> Some typ'
                | _ ->
                    sprintf "Validating Equatable resulted in constraint at %A" typ 
                        |> InvalidType |> raise 
            match mapOption f types with
            | None -> None, []
            | Some types' -> Some <| Type.Tuple types', []
        | TuplePosition (pos, typ) ->
            if types.Length > pos then
                Some <| Type.Tuple types, [Equals (typ, types.[pos])]
            else
                None, []
        | Orderable | RecordLabel _ -> None, []
    | Type.Record (pairs) ->
        match trt with
        | Equatable ->
            let f (name, typ) =
                match validateTrait trt typ with
                | None, [] -> None
                | Some typ', [] -> Some (name, typ')
                | _ ->
                    sprintf "Validating Equatable resulted in constraint at %A" typ 
                        |> InvalidType |> raise 
            match mapOption f pairs with
            | None -> None, []
            | Some pairs' -> Some <| Type.Record pairs' , []
        | RecordLabel (label, typ) ->
            let names, values = List.unzip pairs
            match Seq.tryFindIndex ((=) label) names with
            | Some i ->
                 Some <| Type.Record pairs, [Equals (typ, values.[i])]
            | None ->
                None, []
        | Orderable | TuplePosition _ -> None, []
    | VarType (x, traits) ->
        if List.exists ((=) trt) traits then
            Some typ, []
        else
            Some <| VarType (x, trt::traits), []

let rec validateTraits traits (typ, cons) =
    match typ with
    | None -> None, cons
    | Some typ' -> 
        match traits with
        | [] -> Some typ', cons
        | trt::rest -> 
            let typ', cons' = validateTraits rest <| validateTrait trt typ'
            typ', cons' @ cons

//#endregion

//#region Unification Functions
let rec replaceVarTypes vars constraints =
    match vars with
    | [] -> constraints
    | (x, traits) :: rest ->
        replaceVarTypes rest <| 
            substituteInConstraints (TypeSub (x, VarType (x, traits))) constraints

let rec addTraitsToUnified vars (unified: Unified) =
    match vars with
    | [] -> unified
    | (x, traits) :: rest ->
        let uni' =
            if unified.traits.ContainsKey x then
                unified
            else        
                new Unified(unified.substitution, unified.traits.Add(x, traits))
        addTraitsToUnified rest uni'

let rec occursIn x typ =
    match typ with
    | Int
    | Bool 
    | Char
    | Unit -> false
    | List(t1) -> occursIn x t1
    | Function(t1, t2) -> occursIn x t1 || occursIn x t2
    | Type.Tuple(types) ->
        List.exists (occursIn x) types
    | Type.Record(pairs) ->
        pairs |> List.unzip |> snd |> List.exists (occursIn x)
    | VarType(id, ls) -> id = x

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
                    let t', cons' = validateTraits traits <| (Some t, [])
                    match t' with
                    | None ->
                        sprintf "Can not satisfy traits %A for %A" traits t 
                            |> InvalidType |> raise
                    | Some t' ->
                        let replacedX = substituteInConstraints (TypeSub (x, t')) <| cons' @ rest
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

//#endregion

//#region Unification Application Functions
let rec applyUniToType typ (unified: Unified) =
    match typ with
    | Int -> Int
    | Bool -> Bool
    | Char -> Char
    | Unit -> Unit
    | List(t1) -> 
        List(applyUniToType t1 unified)
    | Function(t1, t2) -> 
        Function(applyUniToType t1 unified, applyUniToType t2 unified)
    | Type.Tuple(types) ->
        Type.Tuple <| List.map (fun typ -> applyUniToType typ unified) types
    | Type.Record(pairs) ->
        let names, types = List.unzip pairs
        List.map (fun typ -> applyUniToType typ unified) types |>
        List.zip names |> Type.Record
    | VarType(x, traits) -> 
        if unified.substitution.ContainsKey x then
            applyUniToType (unified.substitution.Item x) unified
        else if unified.traits.ContainsKey x then
            VarType (x, applyUniToTraits (unified.traits.Item x) unified)
        else
            VarType (x, applyUniToTraits traits unified)
            
and applyUniToTraits traits (unified: Unified) =
    match traits with
    | [] -> []
    | first :: rest ->
        let first' =
            match first with
            | Equatable -> Equatable
            | Orderable -> Orderable
            | TuplePosition (i, t) -> TuplePosition (i, applyUniToType t unified)
            | RecordLabel (l, t) -> RecordLabel (l, applyUniToType t unified)
        first' :: applyUniToTraits rest unified
            
let rec applyUniToEnv env uni: Map<string, EnvAssociation> =
    let f key value =
        match value with
        | Simple typ ->
            Simple <| applyUniToType typ uni
        | Universal _ -> 
            value
    Map.map f env

//#endregion

//#region Constraint Collection Functions
let findId id (e: Map<string, EnvAssociation>) =
    if e.ContainsKey id then
        match e.[id] with
        | Simple typ ->
            typ, []
        | Universal (freeVars, typ) ->
            let f = (fun (x, traits) -> x, getVarType traits)
            let newVars = List.map f freeVars
            let typ' = List.fold (fun acc sub -> substituteInType (NameSub sub) acc) typ newVars
            typ', []
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
        let x = VarType (getVarType (), [])
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
        let varTyp = VarType (getVarType (), [Equatable])
        Bool, c1 @ c2 @ [Equals (typ1, typ2); Equals (varTyp, typ2)]
    | OP(t1, LessThan, t2)
    | OP(t1, LessOrEqual, t2)
    | OP(t1, GreaterOrEqual, t2)
    | OP(t1, GreaterThan, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        let varTyp = VarType (getVarType (), [Orderable])
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
        let paramTyp = VarType (getVarType (), [])
        let typ1, c1 = collectConstraints t1 <| env.Add(id, Simple paramTyp)
        Function(paramTyp, typ1), c1
    | RecFn(id1, Some typ1, id2, Some typ2, t1) ->
        let env1 = env.Add(id1, Simple <| Function(typ2, typ1)).Add(id2, Simple typ2)
        let typ1', c1 = collectConstraints t1 env1
        Function (typ2, typ1), c1 @ [Equals (typ1', typ1)]
    | RecFn(id1, None, id2, None, t1) ->
        let fType = VarType (getVarType (), [])
        let paramTyp = VarType (getVarType (), [])
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
        let typ1' = applyUniToType typ1 uni

        let freeVars = getFreeVars typ1' <| applyUniToEnv env uni
        let isFn = match typ1' with | Function _ -> true | _ -> false

        let assoc = 
            if freeVars.IsEmpty || not isFn then
                Simple typ1'
            else
                Universal (freeVars, typ1')
        let typ2, c2 = collectConstraints t2  <| env.Add(id, assoc)

        typ2, c1 @ c2
    | Nil ->
        List <| VarType (getVarType (), []), []
    | Head(t1) ->
        let typ1, c1 = collectConstraints t1 env
        let x = VarType (getVarType (), [])
        x, c1 @ [Equals (typ1, List x)]
    | Tail(t1) ->
        let typ1, c1 = collectConstraints t1 env
        let x = VarType (getVarType (), [])
        List x, c1 @ [Equals (typ1, List x)]
    | IsEmpty(t1) ->
        let typ1, c1 = collectConstraints t1 env
        Bool, c1 @ [Equals (typ1, List <| VarType (getVarType (), []))]
    | Raise ->
        VarType (getVarType (), []), []
    | Try(t1, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        typ2, c1 @ c2 @ [Equals (typ1, typ2)]
    | Input ->
        List Char, []
    | Output(t1) ->
        let typ1, c1 = collectConstraints t1 env
        Unit, c1 @ [Equals (typ1, List Char)]
    | Tuple(terms) ->
        if List.length terms < 2 then
            sprintf "Tuple must have more than 2 components at %A" term |> InvalidType |> raise
        let types, constraints = 
            List.unzip <| 
            List.map (fun t -> collectConstraints t env) terms
        Type.Tuple types, List.reduce (@) constraints
    | Record(pairs) ->
        let names, types = List.unzip pairs
        if Set(names).Count < List.length names then
            sprintf "Record has duplicate fields at %A" term |> InvalidType |> raise
        let types', constraints = 
            List.unzip <| 
            List.map (fun t -> collectConstraints t env) types
        Type.Record (List.zip names types') , List.reduce (@) constraints
    | ProjectIndex (n, t1) ->
        let typ1, c1 = collectConstraints t1 env
        let retType = VarType (getVarType (), [])
        let varType = VarType (getVarType (), [TuplePosition (n, retType)])
        retType, c1 @ [Equals (typ1, varType)]
    | ProjectName (name, t1) ->
        let typ1, c1 = collectConstraints t1 env
        let retType = VarType (getVarType (), [])
        let varType = VarType (getVarType (), [RecordLabel (name, retType)])
        retType, c1 @ [Equals (typ1, varType)]

//#endregion

let typeInfer t =
    let typ, c = collectConstraints t Map.empty
    let substitutions = unify c
    applyUniToType typ substitutions
