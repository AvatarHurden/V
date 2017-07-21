module TypeInference

open System.Collections.Generic
open Definition
open Translation
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
        | Accessor(t1, t2) -> getFreeVars t1 env @ getFreeVars t2 env
        | Function(t1, t2) -> getFreeVars t1 env @ getFreeVars t2 env
        | Type.Tuple(types) -> 
            List.fold (fun acc x -> getFreeVars x env @ acc) [] types
        | Type.Record(pairs) -> 
            pairs |> List.unzip |> snd |> 
            List.fold (fun acc x -> getFreeVars x env @ acc) []
        | VarType (x, traits) ->
            let freeChecker x' assoc =
                match assoc with
                | Simple (VarType (x1, traits)) -> x1 = x
                | _ -> false
            if Map.exists freeChecker env then
                getFreeVarsInTraits traits env
            else
                [x, traits] @ getFreeVarsInTraits traits env
    in Collections.Set(f typ) |> Set.toList

and getFreeVarsInTraits traits env =
    let f =
        function
        | Equatable
        | Orderable -> []
        | RecordLabel (l, t) -> getFreeVars t env
    List.collect f traits
//#endregion

//#region Type Substitution Functions
let rec substituteInType (sub: Substitution) typ' =
    match typ' with
    | Int -> Int
    | Bool -> Bool
    | Char -> Char
    | List(s1) -> List(substituteInType sub s1)
    | Accessor(s1, s2) -> Accessor(substituteInType sub s1, substituteInType sub s2)
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
    let f = 
        function
        | Equatable -> Equatable
        | Orderable -> Orderable
        | RecordLabel (l, t) -> RecordLabel (l, substituteInType sub t)
    List.map f traits

let substituteInConstraints sub constraints =
    let f (Equals (s, t)) =
        Equals (substituteInType sub s, substituteInType sub t)
    List.map f constraints

//#endregion

//#region Trait Validation Functions
let rec validateTrait trt typ =
    match typ with
    | Int ->
        match trt with
        | Orderable | Equatable -> Some Int, []
        | RecordLabel _ -> None, []
    | Bool ->
        match trt with
        | Equatable -> Some Bool, []
        | Orderable | RecordLabel _ -> None, []
    | Char ->
        match trt with
        | Orderable | Equatable -> Some Char, []
        | RecordLabel _ -> None, []
    | Accessor (typ1, typ2) ->
        match trt with
        | Orderable | Equatable
        | RecordLabel _ -> None, []
    | Function (typ1, typ2) ->
        match trt with
        | Orderable | Equatable
        | RecordLabel _ -> None, []
    | List typ1 ->
        match trt with
        | Orderable | Equatable ->
            match validateTrait trt typ1 with
            | None, cons -> None, cons
            | Some typ1, cons -> Some <| List typ1, cons
        | RecordLabel _ -> None, []
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
        | Orderable -> None, []
    | VarType (x, traits) ->               
        match trt with
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
        

let rec validateTraits traits typ =
    let f (typ', cons') trt = 
        let newTyp, newCons = validateTrait trt typ'
        match newTyp with
        | None -> None
        | Some newTyp -> Some (newTyp, newCons @ cons')
    foldOption f (Some (typ, [])) traits

//#endregion

//#region Unification Functions
let rec replaceVarTypes vars constraints =
    let f acc (x, traits) =
         substituteInConstraints (TypeSub (x, VarType (x, traits))) acc

    List.fold f constraints vars

let traitsToMap map traits = 
    let f (acc: Map<string, Trait list>) (x, traits) =
        acc.Add(x,traits)
    List.fold f map traits

let rec addTraitsToUnified vars (unified: Unified) =
    let f (acc: Unified) (x, traits) =
        if acc.traits.ContainsKey x then
            acc
        else        
            new Unified(acc.substitution, acc.traits.Add(x, traits))
    List.fold f unified vars

let rec occursIn x typ =
    match typ with
    | Int
    | Bool 
    | Char -> false
    | List(t1) -> occursIn x t1
    | Accessor(t1, t2) -> occursIn x t1 || occursIn x t2
    | Function(t1, t2) -> occursIn x t1 || occursIn x t2
    | Type.Tuple(types) ->
        List.exists (occursIn x) types
    | Type.Record(pairs) ->
        pairs |> List.unzip |> snd |> List.exists (occursIn x)
    | VarType(id, ls) -> id = x

let rec unify typeSubs traitSubs constraints =
//    for c in constraints do
//        match c with
//        | Equals (s,t) ->
//            printfn "%A = %A" (printType s) (printType t)
//    printfn ""
    match constraints with
    | [] -> new Unified(typeSubs, traitSubs)
    | first::rest ->
        match first with
        | Equals (s, t) ->
            match s, t with
            | s, t when s = t -> unify typeSubs traitSubs rest
            | VarType (x, traits), t 
            | t, VarType (x, traits) ->
                if occursIn x t then
                    sprintf "Circular constraints" |> TypeException |> raise
                else
                    let valid = validateTraits traits t
                    match valid with
                    | None ->
                        sprintf "Can not satisfy traits %A for %A" traits t 
                            |> TypeException |> raise
                    | Some (t', cons') ->
                        let replacedX = substituteInConstraints (TypeSub (x, t')) (cons' @ rest)
                        let newSubs = (typeSubs.Add(x, t'))
                        if t = t' then
                            unify newSubs traitSubs replacedX
                        else
                            let free = getFreeVars t' Map.empty
                            unify newSubs (traitsToMap traitSubs free) <| replaceVarTypes free replacedX                                
            | List s1, List t1 -> 
                unify typeSubs traitSubs <| rest @ [Equals (s1, t1)]
            | Accessor(s1, s2), Accessor(t1, t2) -> 
                unify typeSubs traitSubs <| rest @ [Equals (s1, t1); Equals (s2, t2)]
            | Function(s1, s2), Function(t1, t2) -> 
                unify typeSubs traitSubs <| rest @ [Equals (s1, t1); Equals (s2, t2)]
            | Type.Tuple typs1, Type.Tuple typs2 when typs1.Length = typs2.Length ->
                unify typeSubs traitSubs <| rest @ List.map2 (fun typ1 typ2 -> Equals (typ1, typ2)) typs1 typs2
            | Type.Record pairs1, Type.Record pairs2 when pairs1.Length = pairs2.Length ->
            
                let v1' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) pairs1
                let v2' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) pairs2
        
                let matchNames (name1, typ1) (name2, typ2) =
                    if name1 <> name2 then
                        raise <| TypeException (sprintf "Records %A and %A have different fields" typ1 typ2)
                    Equals (typ1, typ2)
             
                unify typeSubs traitSubs <| rest @ List.map2 matchNames v1' v2'
            | Function _, s 
            | s, Function _ ->
                raise <| TypeException (sprintf "Type %A is not a function and cannot be applied" s)
            | s, t -> 
                raise <| TypeException (sprintf "Expected type %A, but found type %A" s t)

//#endregion

//#region Unification Application Functions
let rec applyUniToType typ (unified: Unified) =
    match typ with
    | Int -> Int
    | Bool -> Bool
    | Char -> Char
    | List(t1) -> 
        List(applyUniToType t1 unified)
    | Accessor (t1, t2) ->
        Accessor(applyUniToType t1 unified, applyUniToType t2 unified)
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
    let f =
        function
        | Equatable -> Equatable
        | Orderable -> Orderable
        | RecordLabel (l, t) -> RecordLabel (l, applyUniToType t unified)
    List.map f traits
            
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
    
    | Pat (RecordPat (allowsExtra, patterns), typ') ->
        let recordTypes = List.map (fun (name, _) -> name, VarType (getVarType (), [])) patterns
        let f = fun (env, cons) (_, p) (_, t) -> matchPattern p t env cons
        let recordCons =
            if allowsExtra then
                let labelCons = List.map (fun (name, typ) -> RecordLabel (name, typ)) recordTypes
                Equals (VarType (getVarType (), labelCons), typ)
            else
                Equals (Type.Record recordTypes, typ)
        let typeCons =
            match typ' with
            | None -> []
            | Some typ' -> [Equals (typ', typ)]
        List.fold2 f (env, recordCons :: cons @ typeCons) patterns recordTypes

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

let validatePattern = matchPattern
       
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

let rec typeOfBuiltin b env =
    match b with
    | Id ->
        let varType = VarType (getVarType (), []) 
        Function (varType, varType), []
    | Add
    | Subtract
    | Multiply
    | Divide ->
        Function (Int, Function (Int, Int)), []
    | Negate ->
        Function (Int, Int), []

    | Equal
    | Different ->
        let varType = VarType (getVarType (), [Equatable])
        Function (varType, Function (varType, Bool)), []

    | LessThan
    | LessOrEqual
    | GreaterThan
    | GreaterOrEqual ->
        let varType = VarType (getVarType (), [Orderable])
        Function (varType, Function (varType, Bool)), []

    | And
    | Or ->
        Function (Bool, Function (Bool, Bool)), []

    | Cons ->
        let varType = VarType (getVarType (), [])
        Function (varType, Function (List varType, List varType)), []

    | Stack ->
        let varType1 = VarType (getVarType (), [])
        let varType2 = VarType (getVarType (), [])
        let varType3 = VarType (getVarType (), [])

        let accessTyp1 = Accessor (varType1, varType2)
        let accessTyp2 = Accessor (varType3, varType1)
        let accessTyp3 = Accessor (varType3, varType2)

        Function (accessTyp1, Function (accessTyp2, accessTyp3)), []
    | Distort ->
        let varType1 = VarType (getVarType (), [])
        let varType2 = VarType (getVarType (), [])
        let varType3 = VarType (getVarType (), [])

        let accessTyp1 = Accessor (varType1, varType2)

        let getterTyp = Function (varType1, varType3)
        let setterTyp = Function (varType3, varType1)

        let accessTyp2 = Accessor (varType3, varType2)

        Function (accessTyp1, Function (getterTyp, Function (setterTyp, accessTyp2))), []

    | Get -> 
        let varType1 = VarType (getVarType (), [])
        let varType2 = VarType (getVarType (), [])
        let accessTyp = Accessor (varType1, varType2)

        Function(accessTyp, Function(varType2, varType1)), []
    | Set -> 
        let varType1 = VarType (getVarType (), [])
        let varType2 = VarType (getVarType (), [])
        let accessTyp = Accessor (varType1, varType2)

        Function(accessTyp, Function (varType1, Function(varType2, varType2))), []

and collectConstraints term (env: Map<string, EnvAssociation>) =
    match term with
    | B true ->
        Bool, []
    | B false ->
        Bool, []
    | I(i) ->
        Int, []
    | C(c) ->
        Char, []
    | RecordAccess path ->
        let varType1 = VarType (getVarType (), [])

        // returns (IO type, record type, storage type, constraints)
        let rec f = 
            function
            | Component s ->
                let x = VarType (getVarType (), [])
                let recordTyp = VarType (getVarType (), [RecordLabel (s, x)])
                x, recordTyp, x, []
            | Distorted (p, getter, setter) ->
                let t1, c1 = collectConstraints getter env
                let t2, c2 = collectConstraints setter env

                let io = VarType (getVarType (), [])
                let storage = VarType (getVarType (), [])

                let pIo, pRec, pStorage, pC = f p

                let c' = 
                    [Equals (t1, Function(storage, io));
                    Equals (t2, Function(io, storage));
                    Equals (storage, pIo)]

                io, pRec, pStorage, c1 @ c2 @ c'
            | Stacked (p1, p2) ->
                let io1, rec1, storage1, c1 = f p1
                let io2, rec2, storage2, c2 = f p2

                let c' =
                    [Equals (storage1, io2)]

                io2, rec1, storage1, c1 @ c2 @ c'
            | Joined paths ->

                let ios = List.map (fun _ -> VarType (getVarType (), [])) paths

                let stdRecordTyp = VarType (getVarType (), [])

                let f' acc tupleIo (typ, c) =
                    Equals (typ, Accessor(tupleIo, stdRecordTyp)) :: c @ acc
                let c = List.fold2 f' [] ios <| List.map (flip collectConstraints env) paths

                Type.Tuple ios, stdRecordTyp, Type.Tuple ios, c

        let io, r, storage, c = f path
        Accessor (io, r), c
    | Fn fn ->
        match fn with
        | BuiltIn b -> typeOfBuiltin b env
        | Lambda (pattern, t1) ->
            let paramTyp = VarType (getVarType (), [])
            let env', cons = validatePattern pattern paramTyp env []
            let typ1, c1 = collectConstraints t1 env'
            Function(paramTyp, typ1), cons @ c1
        | Recursive (id, retType, pattern, t1) ->
            let paramTyp = VarType (getVarType (), [])
            let fType = 
                match retType with
                | Some retType -> Function(paramTyp, retType) 
                | None -> VarType (getVarType (), [])
            let env', cons = validatePattern pattern paramTyp (env.Add(id, Simple fType)) []
            let typ1, c1 = collectConstraints t1 env'
            Function (paramTyp, typ1), cons @ c1 @ [Equals (Function (paramTyp, typ1), fType)]
    | App(t1, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        let x = VarType (getVarType (), [])
        x, c1 @ c2 @ [Equals (typ1, Function (typ2, x))]
    | X(id) ->
        findId id env
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
                    consCond @ [Equals (Bool, typCond)]
            let typRes, consRes = collectConstraints result env'
            acc @ consPattern @ consCondition @ consRes @ [Equals (retTyp, typRes)]
        retTyp, List.fold f c1 patterns
    | Let(pattern, t1, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let uni = unify Map.empty Map.empty c1
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
    | Tuple(terms) ->
        if List.length terms < 2 then
            sprintf "Tuple must have more than 2 components at %A" term |> TypeException |> raise
        let types, constraints = 
            List.unzip <| 
            List.map (fun t -> collectConstraints t env) terms
        Type.Tuple types, List.reduce (@) constraints
    | Record(pairs) ->
        let names, types = List.unzip pairs
        if Collections.Set(names).Count < List.length names then
            sprintf "Record has duplicate fields at %A" term |> TypeException |> raise
        let types', constraints = 
            List.unzip <| 
            List.map (fun t -> collectConstraints t env) types
        Type.Record (List.zip names types') , List.reduce (@) constraints

//#endregion

let typeInfer t =
    let typ, c = collectConstraints t Map.empty
    let substitutions = unify Map.empty Map.empty c
    applyUniToType typ substitutions

let typeInferLib lib =
    let ret = List.foldBack (fun (p, t) acc -> Let(p, t, acc)) lib.terms (X "x")
    let libTerm = Fn <| Lambda(Pat(XPat "x", None), ret) 
    libTerm |> typeInfer
       