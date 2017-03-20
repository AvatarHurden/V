module TypeInference

open System.Collections.Generic
open Definition
open Printer

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
        | Char -> []
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
                        |> TypeException |> raise 
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
                        |> TypeException |> raise 
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
        match trt with
        | TuplePosition (i, t) ->
            let tupleMatch = function
                | TuplePosition (i', t') when i = i' ->
                    Some <| Equals (t, t')
                | _ -> None
            let constraints = List.choose tupleMatch traits
            if constraints.IsEmpty then
                Some <| VarType (x, trt::traits), [] 
            else
                Some <| VarType (x, traits), constraints
        | RecordLabel (name, t) ->
            let recordMatch = function
                | RecordLabel (name', t') when name = name' ->
                    Some <| Equals (t, t')
                | _ -> None
            let constraints = List.choose recordMatch traits
            if constraints.IsEmpty then
                Some <| VarType (x, trt::traits), []
            else
                Some <| VarType (x, traits), constraints
        | _ ->
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
    | Char -> false
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
                    sprintf "Circular constraints" |> TypeException |> raise
                else
                    let t', cons' = validateTraits traits <| (Some t, [])
                    match t' with
                    | None ->
                        sprintf "Can not satisfy traits %A for %A" traits t 
                            |> TypeException |> raise
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
            | Type.Tuple typs1, Type.Tuple typs2 when typs1.Length = typs2.Length ->
                unify <| rest @ List.map2 (fun typ1 typ2 -> Equals (typ1, typ2)) typs1 typs2
            | Type.Record pairs1, Type.Record pairs2 
                when pairs1.Length = pairs2.Length && 
                     List.forall (fun (name1, _) -> List.exists (fun (name2, _) -> name2 = name1) pairs2) pairs1 ->
            
                let matchNames (name1, typ1) =
                    let (name2, typ2) = List.find (fun (name2, typ2) -> name1 = name2) pairs2
                    Equals (typ1, typ2)
                
                unify <| rest @ List.map matchNames pairs1
            | _ -> 
                raise <| TypeException "Unsolvable constraints"

//#endregion

//#region Unification Application Functions
let rec applyUniToType typ (unified: Unified) =
    match typ with
    | Int -> Int
    | Bool -> Bool
    | Char -> Char
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

//#region Pattern Matching

let rec matchPattern pattern typ (env: Map<Ident, EnvAssociation>) cons =
    match pattern with
    | Pat (XPat x, None)-> env.Add(x, Simple typ), cons
    | Pat (XPat x, Some typ')-> env.Add(x, Simple typ'), Equals (typ', typ) :: cons

    | Pat (IgnorePat, None) -> env, cons
    | Pat (IgnorePat, Some typ') -> env, Equals (typ', typ) :: cons

    | Pat (BPat b, None) -> env, Equals (typ, Bool) :: cons
    | Pat (BPat b, Some typ') -> env, Equals (typ, Bool) :: Equals (typ', Bool) :: cons
    
    | Pat (IPat i, None) -> env, Equals (typ, Int) :: cons
    | Pat (IPat i, Some typ') -> env, Equals (typ, Int) :: Equals (typ', Int) :: cons
    
    | Pat (CPat c, None) -> env, Equals (typ, Char) :: cons
    | Pat (CPat c, Some typ') -> env, Equals (typ, Char) :: Equals (typ', Char) :: cons

    | Pat (TuplePat patterns, typ') ->
        let tupleTypes = List.map (fun _ -> VarType (getVarType (), [])) patterns
        let f = fun (env, cons) p t -> matchPattern p t env cons
        let acc = 
            match typ' with
            | Some typ' ->
                env, Equals (typ', typ) :: Equals (Type.Tuple tupleTypes, typ) :: cons
            | None ->
                env, Equals (Type.Tuple tupleTypes, typ) :: cons
        List.fold2 f acc patterns tupleTypes
    
    | Pat (RecordPat patterns, typ') ->
        let recordTypes = List.map (fun (name, _) -> name, VarType (getVarType (), [])) patterns
        let f = fun (env, cons) (_, p) (_, t) -> matchPattern p t env cons
        let acc = 
            match typ' with
            | Some typ' ->
                env, Equals (typ', typ) :: Equals (Type.Record recordTypes, typ) :: cons
            | None ->
                env, Equals (Type.Record recordTypes, typ) :: cons
        List.fold2 f acc patterns recordTypes

    | Pat (NilPat, typ') ->
        let newTyp = List (VarType (getVarType (), []))
        let cons' =
            match typ' with
            | None ->
                Equals (newTyp, typ) :: cons
            | Some typ' ->
                Equals (newTyp, typ) :: Equals (newTyp, typ') :: cons
        env, cons'

    | Pat (ConsPat (p1, p2), typ') ->
        let newTyp = VarType (getVarType (), [])
        let cons' = 
            match typ' with
            | None ->
                Equals (List newTyp, typ) :: cons
            | Some typ' ->
                Equals (List newTyp, typ') :: Equals (List newTyp, typ) :: cons
        let env', cons' = matchPattern p1 newTyp env cons' 
        matchPattern p2 (List newTyp) env' cons'

let validatePattern pattern typ (env: Map<Ident, EnvAssociation>) =
    let rec findIds (Pat (pattern, _)) =
        match pattern with
        | IgnorePat
        | NilPat
        | BPat _
        | IPat _
        | CPat _ -> []
        | XPat x -> [x]
        | TuplePat patterns ->
            List.fold (fun acc p -> acc @ findIds p) [] patterns
        | RecordPat patterns ->
            List.fold (fun acc (n, p) -> acc @ findIds p) [] patterns
        | ConsPat (p1, p2) ->
            findIds p1 @ findIds p2
    let ids = findIds pattern
    let uniques = ids |> Seq.distinct |> Seq.toList
    if uniques.Length = ids.Length then
        matchPattern pattern typ env
    else
        raise <| TypeException "A pattern cannot have repeated variable names"
        
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
        raise (TypeException <| sprintf "Identifier %A undefined" id)

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
    | OP(t1, Application, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        let x = VarType (getVarType (), [])
        x, c1 @ c2 @ [Equals (typ1, Function (typ2, x))]
    | OP(t1, Cons, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        typ1 |> List, c1 @ c2 @ [Equals (List typ1, typ2)]
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
    | Fn(pattern, t1) ->
        let paramTyp = VarType (getVarType (), [])
        let env', cons = validatePattern pattern paramTyp env []
        let typ1, c1 = collectConstraints t1 env'
        Function(paramTyp, typ1), cons @ c1
    | RecFn(id, retType, pattern, t1) ->
        let paramTyp = VarType (getVarType (), [])
        let fType = 
            match retType with
            | Some retType -> Function(paramTyp, retType) 
            | None -> VarType (getVarType (), [])
        let env', cons = validatePattern pattern paramTyp (env.Add(id, Simple fType)) []
        let typ1, c1 = collectConstraints t1 env'
        Function (paramTyp, typ1), cons @ c1 @ [Equals (fType, Function (paramTyp, typ1))]
    | Match (t1, patterns) ->
        let typ1, c1 = collectConstraints t1 env
        let retTyp = VarType (getVarType (), [])
        let f acc (pattern, condition, result) =
            let env', consPattern = validatePattern pattern typ1 env []
            let consCondition =
                match condition with
                | None -> []
                | Some cond ->
                    let typCond, consCond = collectConstraints cond env'
                    consCond @ [Equals (typCond, Bool)]
            let typRes, consRes = collectConstraints result env'
            acc @ consPattern @ consCondition @ consRes @ [Equals (typRes, retTyp)]
        retTyp, List.fold f c1 patterns
    | Let(pattern, t1, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let uni = unify c1
        let typ1' = applyUniToType typ1 uni

        let freeVars = getFreeVars typ1' <| applyUniToEnv env uni
        let isFn = match typ1' with | Function _ -> true | _ -> false

        let env', cons = 
            if freeVars.IsEmpty || not isFn then
                validatePattern pattern typ1' env []
            else
                match pattern with
                | Pat (XPat x, _) -> env.Add(x, Universal (freeVars, typ1')), []
                | _ ->
                    raise <| TypeException "Pattern not allowed for functions"
        
        let typ2, c2 = collectConstraints t2 env'
        typ2, cons @ c1 @ c2
    | Nil ->
        List <| VarType (getVarType (), []), []
    | Raise ->
        VarType (getVarType (), []), []
    | Try(t1, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        typ2, c1 @ c2 @ [Equals (typ1, typ2)]
    | Tuple(terms) ->
        if List.length terms < 2 then
            sprintf "Tuple must have more than 2 components at %A" term |> TypeException |> raise
        let types, constraints = 
            List.unzip <| 
            List.map (fun t -> collectConstraints t env) terms
        Type.Tuple types, List.reduce (@) constraints
    | Record(pairs) ->
        let names, types = List.unzip pairs
        if Set(names).Count < List.length names then
            sprintf "Record has duplicate fields at %A" term |> TypeException |> raise
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
