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

type TraitSpec = Trait * Map<int, Trait list>

let mutable varType = 0
let getVarType unit =
    let newType = varType
    varType <- varType + 1
    sprintf "X%d" newType
    
type Env =
    {
     //traits: Trait list // Only useful when trait creation is allowed
     types: ConstructorType list
     constructors: Map<Constructor, (Type * Type list)>
     vars: Map<string, EnvAssociation>
     mutable lastVarIndex: int
    }

    member this.getNextVarType x =
        let s = getVarType x
        this.lastVarIndex <- varType
        s

    member this.addAssoc id assoc = 
        {this with vars = this.vars.Add(id, assoc)}

type UniEnv =
    {
     traitAssoc: Map<ConstructorType, TraitSpec list>
     constraints: Constraint list
    }

    member this.validateTrait trt typ =
        match typ with
        | ConstType (c, args) ->
            match this.traitAssoc.TryFind c with
            | None -> None, []
            | Some spec ->
                match Seq.tryFind (fun (t, _) -> t = trt) spec with
                | None -> None, []
                | Some (t, reqs) ->
                    let getComponent i c =
                        if args.Length > i then
                            List.nth args i
                         else
                            sprintf "Constructor type %A doesn't have an argument at index %A" typ i |> TypeException |> raise
                    let f acc index trt =
                        Equals (getComponent index c, VarType (getVarType(), trt)) :: acc
                    Some (ConstType (c, args)), Map.fold f [] reqs
        | _ -> raise <| TypeException "Requested the environment to valide a non-constructor type"

    static member private joinAssoc assoc1 assoc2 =
        let f acc consType l =
            match Map.tryFind consType acc with
            | Some l' -> acc.Add(consType, l @ l')
            | None -> acc.Add(consType, l)
        Map.fold f assoc1 assoc2

    static member (@@) (env: UniEnv, env2: UniEnv) =
        let cons = env.constraints @ env2.constraints
        let traits = UniEnv.joinAssoc env.traitAssoc env2.traitAssoc
        {traitAssoc = traits; constraints = cons}

    static member (@@) (env: UniEnv, cons: Constraint list) =
        let oldCons = env.constraints
        {env with constraints = oldCons @ cons}
    
    static member (@@) (cons: Constraint list, env: UniEnv) =
        let oldCons = env.constraints
        {env with constraints = oldCons @ cons}

    static member empty = {traitAssoc = Map.empty; constraints = []}

let (|Empty|Split|) (env: UniEnv) = 
    match env.constraints with
    | [] -> Empty
    | head :: tail -> Split (head, {env with constraints = tail})


let LIST = ConstType (List, [VarType ("a", [])])
let defaultEnv = 
    {
     //traits = []
     types = [Int; Bool; Char; List]
     constructors = 
        Map [
            B true, (ConstType (Bool, []), [])
            B false, (ConstType (Bool, []), [])
            Nil, (LIST, [])
            Cons, (LIST, [VarType ("a", []); LIST])
            ]
     vars = Map.empty
     lastVarIndex = 0
    }

let defaultUniEnv =
    {
    traitAssoc = 
        Map [
            Bool, [(Equatable, Map.empty)]
            Int, [(Equatable, Map.empty); (Orderable, Map.empty)]
            Char, [(Equatable, Map.empty); (Orderable, Map.empty)]
            List, [(Equatable, Map.empty.Add(0, [Equatable]))
                   (Orderable, Map.empty.Add(0, [Orderable]))]
            ]
    constraints = []
    }


//#region Free Variable Collection Functions
let rec getFreeVars typ env =
    let f typ = 
        match typ with
        | ConstType (_, types) -> 
            List.fold (fun acc x -> getFreeVars x env @ acc) [] types
        | Function(t1, t2) -> 
            getFreeVars t1 env @ getFreeVars t2 env
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
            if Map.exists freeChecker env.vars then
                getFreeVarsInTraits traits env
            else
                [x, traits] @ getFreeVarsInTraits traits env
    in Set(f typ) |> Set.toList

and getFreeVarsInTraits traits env =
    let f =
        function
        | Equatable
        | Orderable -> []
        | RecordLabel (l, t) -> getFreeVars t env
    List.collect f traits
//#endregion

//#region Type Substitution Functions
and substituteInType (sub: Substitution) typ' =
    match typ' with
    | ConstType (c, types) -> 
        ConstType (c, List.map (substituteInType sub) types)
    | Function(s1, s2) -> 
        Function(substituteInType sub s1, substituteInType sub s2)
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

let substituteInConstraints sub env =
    let f (Equals (s, t)) =
        Equals (substituteInType sub s, substituteInType sub t)
    {env with constraints = List.map f env.constraints }

//#endregion

type Env with
    member env.typeOf constr =
        match constr with
            | C _ -> ConstType (Char, [])
            | I _ -> ConstType (Int, [])
            | B _ -> ConstType (Bool, [])
            | _ -> 
                match Map.tryFind constr env.constructors with
                | None -> sprintf "Undeclared constructor %A" constr |> TypeException |> raise
                | Some (ret, args) ->
                    let typ = List.foldBack (curry Function) args ret
                    let freeVars = getFreeVars typ env
                    let subs = List.map (fun x -> NameSub(fst x, getVarType ())) freeVars
                    List.fold (flip substituteInType) typ subs

    member env.parametersOf constr =
        match constr with
        | C _ -> ConstType (Char, []), []
        | I _ -> ConstType (Int, []), []
        | B _ -> ConstType (Bool, []), []
        | _ ->
            match Map.tryFind constr env.constructors with
            | None -> sprintf "Undeclared constructor %A" constr |> TypeException |> raise
            | Some (ret, args) ->
                let typ = List.fold (curry Function) ret args
                let freeVars = getFreeVars typ env
                let subs = List.map (fun x -> NameSub(fst x, getVarType ())) freeVars
                let ret' = List.fold (flip substituteInType) ret subs
                let args' = List.map (fun typ -> List.fold (flip substituteInType) typ subs) args
                ret', args'

//#region Trait Validation Functions
let rec validateTrait trt typ (env: UniEnv) =
    match typ with
    | ConstType _ as c -> 
        env.validateTrait trt c
    | Function _ -> 
        None, []
    | Type.Tuple (types) ->
        match trt with
        | Equatable ->
            let f typ =
                match validateTrait trt typ env with
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
                match validateTrait trt typ env with
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
        

let rec validateTraits traits typ env =
    let f (typ', cons') trt = 
        let newTyp, newCons = validateTrait trt typ' env
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
    | ConstType (_, types) -> 
        List.exists (occursIn x) types
    | Function(t1, t2) -> 
        occursIn x t1 || occursIn x t2
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
    | Empty -> new Unified(typeSubs, traitSubs)
    | Split (first, rest) ->
        match first with
        | Equals (s, t) ->
            match s, t with
            | s, t when s = t -> unify typeSubs traitSubs rest
            | VarType (x, traits), t 
            | t, VarType (x, traits) ->
                if occursIn x t then
                    sprintf "Circular constraints" |> TypeException |> raise
                else
                    let valid = validateTraits traits t rest
                    match valid with
                    | None ->
                        sprintf "Can not satisfy traits %A for %A" traits t 
                            |> TypeException |> raise
                    | Some (t', cons') ->
                        let replacedX = substituteInConstraints (TypeSub (x, t')) (cons' @@ rest)
                        let newSubs = (typeSubs.Add(x, t'))
                        if t = t' then
                            unify newSubs traitSubs replacedX
                        else
                            let free = getFreeVars t' defaultEnv
                            unify newSubs (traitsToMap traitSubs free) <| replaceVarTypes free replacedX                                
            | ConstType (c1, types1), ConstType (c2, types2) when c1 = c2 ->
                unify typeSubs traitSubs <| rest @@ List.map2 (fun typ1 typ2 -> Equals (typ1, typ2)) types1 types2
            | Function(s1, s2), Function(t1, t2) -> 
                unify typeSubs traitSubs <| rest @@ [Equals (s1, t1); Equals (s2, t2)]
            | Type.Tuple typs1, Type.Tuple typs2 when typs1.Length = typs2.Length ->
                unify typeSubs traitSubs <| rest @@ List.map2 (fun typ1 typ2 -> Equals (typ1, typ2)) typs1 typs2
            | Type.Record pairs1, Type.Record pairs2 when pairs1.Length = pairs2.Length ->
            
                let v1' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) pairs1
                let v2' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) pairs2
        
                let matchNames (name1, typ1) (name2, typ2) =
                    if name1 <> name2 then
                        raise <| TypeException (sprintf "Records %A and %A have different fields" typ1 typ2)
                    Equals (typ1, typ2)
             
                unify typeSubs traitSubs <| rest @@ List.map2 matchNames v1' v2'
            | Function _, s 
            | s, Function _ ->
                raise <| TypeException (sprintf "Type %A is not a function and cannot be applied" s)
            | s, t -> 
                raise <| TypeException (sprintf "Expected type %A, but found type %A" s t)

//#endregion

//#region Unification Application Functions
let rec applyUniToType typ (unified: Unified) =
    match typ with
    | ConstType (c, types) -> 
        ConstType (c, List.map (fun typ -> applyUniToType typ unified) types)
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
            
let rec applyUniToEnv (env: Env) uni: Env =
    let f key value =
        match value with
        | Simple typ ->
            Simple <| applyUniToType typ uni
        | Universal _ -> 
            value
    {env with vars = Map.map f (env.vars)}

//#endregion

//#region Pattern Matching

let rec matchPattern pattern typ (env: Env) cons =
    match pattern with
    | Pat (XPat x, None)-> env.addAssoc x (Simple typ), cons
    | Pat (XPat x, Some typ')-> env.addAssoc x (Simple typ'), Equals (typ', typ) :: cons

    | Pat (IgnorePat, None) -> env, cons
    | Pat (IgnorePat, Some typ') -> env, Equals (typ', typ) :: cons

    | Pat (ConstructorPat (c, patterns), typ') ->
        let retTyp, parameters = env.parametersOf c
        let f = fun (env, cons) p t -> matchPattern p t env cons
        let acc = 
            match typ' with
            | Some typ' ->
                env, Equals (typ', typ) :: Equals (retTyp, typ) :: cons
            | None ->
                env, Equals (retTyp, typ) :: cons
        List.fold2 f acc patterns parameters

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

let validatePattern = matchPattern
       
//#endregion

//#region Constraint Collection Functions

let findId id env =
    match env.vars.TryFind id with
    | None -> raise (TypeException <| sprintf "Identifier %A undefined" id)
    | Some v ->
        match v with
        | Simple typ ->
            typ, UniEnv.empty
        | Universal (freeVars, typ) ->
            let f = (fun (x, traits) -> x, env.getNextVarType ())
            let newVars = List.map f freeVars
            let typ' = List.fold (fun acc sub -> substituteInType (NameSub sub) acc) typ newVars
            typ', UniEnv.empty

let typeOfBuiltin b =
    match b with
    | Add
    | Subtract
    | Multiply
    | Divide ->
        Function (ConstType (Int, []), Function (ConstType (Int, []), ConstType (Int, [])))
    | Negate ->
        Function (ConstType (Int, []), ConstType (Int, []))

    | Equal
    | Different ->
        let varType = VarType (getVarType (), [Equatable])
        Function (varType, Function (varType, ConstType (Bool, [])))

    | LessThan
    | LessOrEqual
    | GreaterThan
    | GreaterOrEqual ->
        let varType = VarType (getVarType (), [Orderable])
        Function (varType, Function (varType, ConstType (Bool, [])))

    | And
    | Or ->
        Function (ConstType (Bool, []), Function (ConstType (Bool, []), ConstType (Bool, [])))

    | RecordAccess s ->
        let varType1 = VarType (getVarType (), [])
        let varType2 = VarType (getVarType (), [RecordLabel (s, varType1)])
        Function (varType1, Function(varType2, Type.Tuple [varType1; varType2]))
    | Get -> 
        let varType1 = VarType (getVarType (), [])
        let varType2 = VarType (getVarType (), [])
        let accessTyp =
            Function (varType1, Function(varType2, Type.Tuple [varType1; varType2]))
        Function(accessTyp, Function(varType2, varType1))

// collectConstraints term environment constraints
let rec collectConstraints term (env: Env) =
    match term with
    | Constructor c -> env.typeOf c, UniEnv.empty
    | BuiltIn b -> typeOfBuiltin b, UniEnv.empty
    | Fn fn ->
        match fn with
        | Lambda (pattern, t1) ->
            let paramTyp = VarType (getVarType (), [])
            let env', cons = validatePattern pattern paramTyp env []
            let typ1, c1 = collectConstraints t1 env'
            Function(paramTyp, typ1), c1 @@ cons
        | Recursive (id, retType, pattern, t1) ->
            let paramTyp = VarType (getVarType (), [])
            let fType = 
                match retType with
                | Some retType -> Function(paramTyp, retType) 
                | None -> VarType (getVarType (), [])
            let env', cons = validatePattern pattern paramTyp (env.addAssoc id (Simple fType)) []
            let typ1, c1 = collectConstraints t1 env'
            Function (paramTyp, typ1), cons @@ c1 @@ [Equals (Function (paramTyp, typ1), fType)]
    | App(t1, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        let x = VarType (getVarType (), [])
        x, c1 @@ c2 @@ [Equals (typ1, Function (typ2, x))]
    | X(id) ->
        findId id env
    | Match (t1, patterns) ->
        let typ1, c1 = collectConstraints t1 env
        let retTyp = VarType (getVarType (), [])
        let f acc (pattern, condition, result) =
            let env', consPattern = validatePattern pattern typ1 env []
            let consCondition =
                match condition with
                | None -> UniEnv.empty
                | Some cond ->
                    let typCond, consCond = collectConstraints cond env'
                    consCond @@ [Equals (ConstType (Bool, []), typCond)]
            let typRes, consRes = collectConstraints result env'
            acc @@ consPattern @@ consCondition @@ consRes @@ [Equals (retTyp, typRes)]
        retTyp, List.fold f c1 patterns
    | Let(pattern, t1, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let uni = unify Map.empty Map.empty <| c1 @@ defaultUniEnv 
        let typ1' = applyUniToType typ1 uni

        let freeVars = getFreeVars typ1' <| applyUniToEnv env uni
        let isFn = match typ1' with | Function _ -> true | _ -> false

        let env', cons = 
            if freeVars.IsEmpty || not isFn then
                validatePattern pattern typ1' env []
            else
                match pattern with
                | Pat (XPat x, _) -> env.addAssoc x (Universal (freeVars, typ1')), []
                | _ ->
                    raise <| TypeException "Pattern not allowed for functions"
        
        let typ2, c2 = collectConstraints t2 env'
        typ2, cons @@ c1 @@ c2
    | Raise ->
        VarType (getVarType (), []), UniEnv.empty
    | Tuple(terms) ->
        if List.length terms < 2 then
            sprintf "Tuple must have more than 2 components at %A" term |> TypeException |> raise
        let types, constraints = 
            List.unzip <| 
            List.map (fun t -> collectConstraints t env) terms
        Type.Tuple types, List.reduce (@@) constraints
    | Record(pairs) ->
        let names, types = List.unzip pairs
        if Set(names).Count < List.length names then
            sprintf "Record has duplicate fields at %A" term |> TypeException |> raise
        let types', constraints = 
            List.unzip <| 
            List.map (fun t -> collectConstraints t env) types
        Type.Record (List.zip names types') , List.reduce (@@) constraints

//#endregion

let typeInfer t =
    let typ, c = collectConstraints t defaultEnv
    let substitutions = unify Map.empty Map.empty <| c @@ defaultUniEnv
    applyUniToType typ substitutions

let typeInferLib lib =
    let ret = List.foldBack (fun (p, t) acc -> Let(p, t, acc)) lib.terms (X "x")
    let libTerm = Fn <| Lambda(Pat(XPat "x", None), ret) 
    libTerm |> typeInfer
       