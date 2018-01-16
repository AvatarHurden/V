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
     varTypes: Map<string, string>
     mutable lastVarIndex: int
    }

    member this.getNextVarType x =
        let s = getVarType x
        this.lastVarIndex <- varType
        s

    member this.addAssoc id assoc = 
        {this with vars = this.vars.Add(id, assoc)}

    member this.addVarAssoc id typ =
        {this with varTypes = this.varTypes.Add(id, typ)}

type UniEnv =
    {
     traitAssoc: Map<ConstructorType, TraitSpec list>
     constraints: Constraint list
    }

    member this.findTraitSpecs c =
        match c with
        | ConstructorType.Tuple n ->
            let indexes = [1..n]
            let traitsList = List.map (fun _ -> [Equatable]) indexes
            Some <| [Equatable, Map.ofList (List.zip indexes traitsList)]
        | _ -> this.traitAssoc.TryFind c

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
     varTypes = Map.empty
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
        | Accessor(t1, t2) -> getFreeVars t1 env @ getFreeVars t2 env
        | Function(t1, t2) -> getFreeVars t1 env @ getFreeVars t2 env
        | Type.Record(pairs) -> 
            pairs |> List.unzip |> snd |> 
            List.fold (fun acc x -> getFreeVars x env @ acc) []
        | VarType (x, traits) ->
            let freeChecker _ assoc =
                match assoc with
                | Simple typ' -> 
                    List.exists (fun (x', _) -> x = x') <| getFreeVars typ' defaultEnv
                | _ -> false
            if Map.exists freeChecker env.vars then
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
and substituteInType (sub: Substitution) typ' =
    match typ' with
    | ConstType (c, types) -> 
        ConstType (c, List.map (substituteInType sub) types)
    | Accessor(s1, s2) -> Accessor(substituteInType sub s1, substituteInType sub s2)
    | Function(s1, s2) -> Function(substituteInType sub s1, substituteInType sub s2)
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

    member env.instantiate typ =
        let freeVars = getFreeVars typ env

        let f (subs, env') (x, traits) =
            match Map.tryFind x env'.varTypes with
            | Some typ -> 
                NameSub (x, typ) :: subs, env'
            | None -> 
                let (env': Env), traits' = env'.instantiateTraits traits
                let varReplacement = getVarType ()
                let env' = env'.addVarAssoc x varReplacement
                NameSub (x, varReplacement) :: subs, env'

        let (subs, env') = List.fold f ([], env) freeVars
        let typ' = List.fold (flip substituteInType) typ subs
        env', typ'
    
    member private env.instantiateTraits trts =
        let instantiate trt = 
            match trt with
            | Equatable -> env, Equatable
            | Orderable -> env, Orderable
            | RecordLabel (l, typ) ->
                let env', typ' = env.instantiate typ
                env', RecordLabel (l, typ')
         
        let f (trts', env') trt =
            let env', trt' = instantiate trt
            trt' :: trts', env'
        let trts', env' = List.fold f ([], env) trts
        env', trts'

    member env.typeOf constr =
        match constr with
        | C _ -> ConstType (Char, [])
        | I _ -> ConstType (Int, [])
        | B _ -> ConstType (Bool, [])
        | Tuple n -> 
            let args = List.map (fun x -> VarType (getVarType (), [])) [1..n]
            let ret = ConstType (ConstructorType.Tuple n, args)
            List.foldBack (curry Function) args ret
        | _ -> 
            match Map.tryFind constr env.constructors with
            | None -> sprintf "Undeclared constructor %A" (printConstructor constr) |> TypeException |> raise
            | Some (ret, args) ->
                let typ = List.foldBack (curry Function) args ret
                let freeVars = getFreeVars typ env
                let subs = List.map (fun x -> NameSub(fst x, getVarType ())) freeVars
                List.fold (flip substituteInType) typ subs

    member private env.findSubs typ basedOn =
        match typ, basedOn with
        | ConstType (c, types), ConstType (c', types') when c = c' -> 
            List.fold2 (fun acc x y -> env.findSubs x y  @ acc) [] types types'
        | Accessor(t1, t2), Accessor(t1', t2') -> 
            env.findSubs t1 t1' @ env.findSubs t2 t2'
        | Function(t1, t2), Function(t1', t2') -> 
            env.findSubs t1 t1' @ env.findSubs t2 t2'
        | Type.Record(pairs), Type.Record(pairs') -> 
            let types = pairs |> List.unzip |> snd
            let types' = pairs' |> List.unzip |> snd
            List.fold2 (fun acc x y -> env.findSubs x y @ acc) [] types types'
        | VarType (x, traits), t ->
            [TypeSub (x, t)]
        | _ ->
            sprintf "Types %A and %A have different structures" (printType typ) (printType basedOn) |> TypeException |> raise
            

    member env.parametersOf constr basedOn =
        match constr with
        | C _ -> ConstType (Char, []), []
        | I _ -> ConstType (Int, []), []
        | B _ -> ConstType (Bool, []), []
        | Tuple n -> 
            let args = List.map (fun x -> VarType (getVarType (), [])) [1..n]
            let ret = ConstType (ConstructorType.Tuple n, args)

            let subs =
                match basedOn with
                | None -> []
                | Some t -> env.findSubs ret t

            let ret' = List.fold (flip substituteInType) ret subs
            let args' = List.map (fun typ -> List.fold (flip substituteInType) typ subs) args
                
            ret', args'
        | _ ->
            match Map.tryFind constr env.constructors with
            | None -> sprintf "Undeclared constructor %A" (printConstructor constr) |> TypeException |> raise
            | Some (ret, args) ->
                let subs =
                    match basedOn with
                    | None -> []
                    | Some t -> env.findSubs ret t
                
                let ret' = List.fold (flip substituteInType) ret subs
                let args' = List.map (fun typ -> List.fold (flip substituteInType) typ subs) args
                
                let typ = List.fold (curry Function) ret' args'
                let freeVars = getFreeVars typ env
                let subs = List.map (fun x -> NameSub(fst x, getVarType ())) freeVars

                let ret'' = List.fold (flip substituteInType) ret' subs
                let args'' = List.map (fun typ -> List.fold (flip substituteInType) typ subs) args'
                ret'', args''

//#region Trait Validation Functions
let rec validateTrait trt typ (env: UniEnv) =
    match typ with
    | ConstType (c, args) -> 
        validateTraitsConstructor trt c args env
    | Accessor (typ1, typ2) ->
        match trt with
        | Orderable | Equatable
        | RecordLabel _ -> None
    | Function (typ1, typ2) ->
        match trt with
        | Orderable | Equatable
        | RecordLabel _ -> None
    | Type.Record (pairs) ->
        match trt with
        | Equatable ->
            let f (name, typ) =
                match validateTrait trt typ env with
                | None -> None
                | Some (typ', cons') -> Some ((name, typ'), cons')
            match mapOption f pairs with
            | None -> None
            | Some res -> 
                let pairs', cons' = List.unzip res 
                Some (Type.Record pairs', List.concat cons')
        | RecordLabel (label, typ) ->
            let names, values = List.unzip pairs
            match Seq.tryFindIndex ((=) label) names with
            | Some i ->
                 Some (Type.Record pairs, [Equals (typ, values.[i])])
            | None ->
                None
        | Orderable -> None
    | VarType (x, traits) ->               
        match trt with
        | RecordLabel (name, t) ->
            let recordMatch = function
                | RecordLabel (name', t') when name = name' ->
                    Some <| Equals (t, t')
                | _ -> None
            let constraints = List.choose recordMatch traits
            if constraints.IsEmpty then
                Some (VarType (x, trt::traits), [])
            else
                Some (VarType (x, traits), constraints)
        | _ ->
            if List.exists ((=) trt) traits then
                Some (typ, [])
            else
                Some (VarType (x, trt::traits), [])

and validateTraitsConstructor trt c (args: Type list) env =
    match env.findTraitSpecs c with
    | None -> None
    | Some spec ->
        match Seq.tryFind (fun (t, _) -> t = trt) spec with
        | None -> None
        | Some (t, reqs) ->
            let f (index, trts) =
                if args.Length <= index then
                        sprintf "Constructor type %A doesn't have an argument at index %A" (printConstrType c) index |> TypeException |> raise
                let typ = List.nth args index
                validateTraits trts typ env
            match mapOption f (Map.toList reqs) with
            | None -> None
            | Some res -> 
                let comps, cons' = List.unzip res
                Some (ConstType (c, comps), List.concat cons')

and validateTraits traits typ env =
    let f (typ', cons') trt = 
        match validateTrait trt typ' env with
        | None -> None
        | Some (newTyp, newCons) -> Some (newTyp, newCons @ cons')
    foldOption f (Some (typ, [])) traits

//#endregion

//#region Unification Functions
let rec replaceVarTypes vars constraints =
    let f acc (x, traits) =
         substituteInConstraints (TypeSub (x, VarType (x, traits))) acc

    List.fold f constraints vars
    
let rec occursIn x typ =
    match typ with
    | ConstType (_, types) -> 
        List.exists (occursIn x) types
    | Accessor(t1, t2) -> occursIn x t1 || occursIn x t2
    | Function(t1, t2) -> occursIn x t1 || occursIn x t2
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
                        sprintf "Can not satisfy traits %A for %A" (printTraits traits) (printType t)
                            |> TypeException |> raise
                    | Some (t', cons') ->
                        let replacedX = substituteInConstraints (TypeSub (x, t')) (cons' @@ rest)
                        let newSubs = Map.map (fun _ t -> substituteInType (TypeSub (x, t')) t) typeSubs
                        let newSubs = (newSubs.Add(x, t'))
                        if t = t' then
                            unify newSubs traitSubs replacedX
                        else
                            let free = getFreeVars t' defaultEnv
                            let f (acc: Map<string, Type>) x =
                                let acc' = Map.map (fun _ t -> substituteInType (TypeSub (fst x, VarType x)) t) acc
                                acc'.Add(fst x, VarType x)
                            let newSubs = List.fold f newSubs free
                            unify newSubs traitSubs <| replaceVarTypes free replacedX                                
            | ConstType (c1, types1), ConstType (c2, types2) when c1 = c2 ->
                unify typeSubs traitSubs <| rest @@ List.map2 (fun typ1 typ2 -> Equals (typ1, typ2)) types1 types2
            | Accessor(s1, s2), Accessor(t1, t2) ->
                unify typeSubs traitSubs <| rest @@ [Equals (s1, t1); Equals (s2, t2)]
            | Function(s1, s2), Function(t1, t2) -> 
                unify typeSubs traitSubs <| rest @@ [Equals (s1, t1); Equals (s2, t2)]
            | Type.Record pairs1, Type.Record pairs2 when pairs1.Length = pairs2.Length ->
            
                let v1' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) pairs1
                let v2' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) pairs2
        
                let matchNames (name1, typ1) (name2, typ2) =
                    if name1 <> name2 then
                        raise <| TypeException (sprintf "Records %A and %A have different fields" (printType typ1) (printType typ2))
                    Equals (typ1, typ2)
             
                unify typeSubs traitSubs <| rest @@ List.map2 matchNames v1' v2'
            | Function _, s 
            | s, Function _ ->
                raise <| TypeException (sprintf "Type %A is not a function and cannot be applied" (printType s))
            | s, t -> 
                raise <| TypeException (sprintf "Expected type %A, but found type %A" (printType s) (printType t))

//#endregion

//#region Unification Application Functions
let rec applyUniToType typ (unified: Unified) =
    match typ with
    | ConstType (c, types) -> 
        ConstType (c, List.map (fun typ -> applyUniToType typ unified) types)
    | Accessor (t1, t2) ->
        Accessor(applyUniToType t1 unified, applyUniToType t2 unified)
    | Function(t1, t2) -> 
        Function(applyUniToType t1 unified, applyUniToType t2 unified)
    | Type.Record(pairs) ->
        let names, types = List.unzip pairs
        List.map (fun typ -> applyUniToType typ unified) types |>
        List.zip names |> Type.Record
    | VarType(x, traits) -> 
        if unified.substitution.ContainsKey x then
            unified.substitution.Item x
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
    let env, typ' = 
        match pattern with
        | Pat (_, None) -> env, None
        | Pat (_, Some typ) -> 
            let env', typ' = env.instantiate typ
            env', Some typ'
    let (Pat (pat, _)) = pattern

    match (pat, typ') with
    | (XPat x, None) -> env.addAssoc x (Simple typ), cons
    | (XPat x, Some typ')-> env.addAssoc x (Simple typ'), Equals (typ', typ) :: cons

    | (IgnorePat, None) -> env, cons
    | (IgnorePat, Some typ') -> env, Equals (typ', typ) :: cons

    | (ConstructorPat (c, patterns), typ') ->
        let retTyp, parameters = env.parametersOf c None
        let f = fun (env, cons) p t -> matchPattern p t env cons
        let acc = 
            match typ' with
            | Some typ' ->
                env, Equals (typ', typ) :: Equals (retTyp, typ) :: cons
            | None ->
                env, Equals (retTyp, typ) :: cons
        List.fold2 f acc patterns parameters

    | (RecordPat (allowsExtra, patterns), typ') ->
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

let rec matchUniversalPattern pattern typ (env: Env) cons =
    let env, typ' = 
        match pattern with
        | Pat (_, None) -> env, None
        | Pat (_, Some typ) -> 
            let env', typ' = env.instantiate typ
            env', Some typ'
    let (Pat (pat, _)) = pattern

    match pat, typ' with
    | (XPat x, None) -> 
        match getFreeVars typ env with
        | [] -> env.addAssoc x (Simple typ), cons
        | frees -> env.addAssoc x (Universal (frees, typ)), cons
    | (XPat x, Some typ')-> 
        match getFreeVars typ' env with
        | [] -> env.addAssoc x (Simple typ'), Equals (typ', typ) :: cons
        | frees -> env.addAssoc x (Universal (frees, typ')), Equals (typ', typ) :: cons

    | (IgnorePat, None) -> env, cons
    | (IgnorePat, Some typ') -> env, Equals (typ', typ) :: cons

    | (ConstructorPat (c, patterns), typ') ->
        let retTyp, parameters = env.parametersOf c <| Some typ
        let f = fun (env, cons) p t -> matchUniversalPattern p t env cons
        let acc = 
            match typ' with
            | Some typ' ->
                env, [Equals (typ', typ); Equals (retTyp, typ)] @ cons
            | None ->
                env, [Equals (retTyp, typ)] @ cons
        List.fold2 f acc patterns parameters

    | (RecordPat (allowsExtra, patterns), typ') ->
        let recordTypes = 
            match typ with
            | Type.Record typs -> 
                if allowsExtra then
                    let f  = fun (name, typ) -> List.exists (fun (n, p) -> n = name) patterns
                    List.filter f typs
                else
                    typs
            | _ -> sprintf "Invalid type %A for universal match" (printType typ) |> TypeException |> raise
        
        let v1' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) recordTypes
        let v2' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) patterns
        
        if v1'.Length <> v2'.Length then
            sprintf "Pattern %A and record %A have different fields" (printPattern pattern) (printType typ) |> TypeException |> raise

        let f (env, cons) (name1, p) (name2, t) =
            if name1 <> name2 then
                raise <| TypeException (sprintf "Record %A and pattern %A have different fields" (printType typ) (printPattern pattern))
            else
                matchUniversalPattern p t env cons
        let typeCons =
            match typ' with
            | None -> cons
            | Some typ' -> Equals (typ', typ) :: cons
        List.fold2 f (env, typeCons) patterns recordTypes

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

let rec typeOfBuiltin b =
    match b with
    | Id ->
        let varType = VarType (getVarType (), []) 
        Function (varType, varType)
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

    | Stack ->
        let varType1 = VarType (getVarType (), [])
        let varType2 = VarType (getVarType (), [])
        let varType3 = VarType (getVarType (), [])

        let accessTyp1 = Accessor (varType1, varType2)
        let accessTyp2 = Accessor (varType3, varType1)
        let accessTyp3 = Accessor (varType3, varType2)

        Function (accessTyp1, Function (accessTyp2, accessTyp3))
    | Distort ->
        let varType1 = VarType (getVarType (), [])
        let varType2 = VarType (getVarType (), [])
        let varType3 = VarType (getVarType (), [])

        let accessTyp1 = Accessor (varType1, varType2)

        let getterTyp = Function (varType1, varType3)
        let setterTyp = Function (varType3, varType1)

        let accessTyp2 = Accessor (varType3, varType2)

        Function (accessTyp1, Function (getterTyp, Function (setterTyp, accessTyp2)))

    | Get -> 
        let varType1 = VarType (getVarType (), [])
        let varType2 = VarType (getVarType (), [])
        let accessTyp = Accessor (varType1, varType2)

        Function(accessTyp, Function(varType2, varType1))
    | Set -> 
        let varType1 = VarType (getVarType (), [])
        let varType2 = VarType (getVarType (), [])
        let accessTyp = Accessor (varType1, varType2)

        Function(accessTyp, Function (varType1, Function(varType2, varType2)))

// collectConstraints term environment constraints
let rec collectConstraints term (env: Env) =
    match term with
    | Constructor c -> env.typeOf c, UniEnv.empty
    | BuiltIn b -> typeOfBuiltin b, UniEnv.empty
    | RecordAccess path ->
        let varType1 = VarType (getVarType (), [])

        // returns (IO type, record type, storage type, constraints)
        let rec f = 
            function
            | Component s ->
                let x = VarType (getVarType (), [])
                let recordTyp = VarType (getVarType (), [RecordLabel (s, x)])
                x, recordTyp, x, UniEnv.empty
            //| Distorted (p, getter, setter) ->
            //    let t1, c1 = collectConstraints getter env
            //    let t2, c2 = collectConstraints setter env

            //    let io = VarType (getVarType (), [])
            //    let storage = VarType (getVarType (), [])

            //    let pIo, pRec, pStorage, pC = f p

            //    let c' = 
            //        [Equals (t1, Function(storage, io));
            //        Equals (t2, Function(io, storage));
            //        Equals (storage, pIo)]

            //    io, pRec, pStorage, c' @@ c1 @@ c2 @@ pC
            //| Stacked (p1, p2) ->
            //    let io1, rec1, storage1, c1 = f p1
            //    let io2, rec2, storage2, c2 = f p2

            //    let c' =
            //        [Equals (storage1, io2)]

            //    io2, rec1, storage1, c' @@ c1 @@ c2
            | Joined paths ->

                let ios = List.map (fun _ -> VarType (getVarType (), [])) paths

                let stdRecordTyp = VarType (getVarType (), [])

                let f' acc tupleIo (typ, c) =
                    [Equals (typ, Accessor(tupleIo, stdRecordTyp))] @@ c @@ acc
                let c = List.fold2 f' UniEnv.empty ios <| List.map (flip collectConstraints env) paths

                let t = ConstType (ConstructorType.Tuple ios.Length, ios)
                t, stdRecordTyp, t, c

        let io, r, storage, c = f path
        Accessor (io, r), c
    | Fn fn ->
        match fn with
        | Lambda (arg, t1) ->
            let paramTyp = VarType (getVarType (), [])
            let env' = env.addAssoc arg (Simple paramTyp) //, cons = validatePattern pattern paramTyp env []
            let typ1, c1 = collectConstraints t1 env'
            Function(paramTyp, typ1), c1
        | Recursive (id, retType, arg, t1) ->
            let paramTyp = VarType (getVarType (), [])
            let fType = 
                match retType with
                | Some retType -> Function(paramTyp, retType) 
                | None -> VarType (getVarType (), [])
            let env' = env.addAssoc id (Simple fType)
            let env' = env'.addAssoc arg (Simple paramTyp) //, cons = validatePattern pattern paramTyp  []
            let typ1, c1 = collectConstraints t1 env'
            Function (paramTyp, typ1), c1 @@ [Equals (Function (paramTyp, typ1), fType)]
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

        let env, pat, typ = 
            match pattern with
            | Pat (pat, Some typ) -> 
                let env', typ = env.instantiate typ
                env', pat, Some typ
            | Pat (pat, None) -> env, pat, None

        let typ1, c1 = collectConstraints t1 env

        let cons = Option.fold (fun acc x -> Equals (x, typ1) :: acc) [] typ
            
        let uni = unify Map.empty Map.empty <| cons @@ c1 @@ defaultUniEnv 
        let typ1' = applyUniToType typ1 uni
        let typ' = Option.map (flip applyUniToType uni) typ

        let env', cons = matchUniversalPattern (Pat (pat, typ')) typ1' (applyUniToEnv env uni) []
        
        let typ2, c2 = collectConstraints t2 env'
        typ2, cons @@ c1 @@ c2
    | Raise ->
        VarType (getVarType (), []), UniEnv.empty
    | Record(pairs) ->
        let names, types = List.unzip pairs
        if Collections.Set(names).Count < List.length names then
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
    let libTerm = Fn <| Lambda("x", ret) 
    libTerm |> typeInfer
       