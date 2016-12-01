module TypeInference

open System.Collections.Generic
open Definition
open Printer

exception InvalidType of string

// This is a stand-in for VarType, to avoid having to match types
type FreeVar = string * Trait list

type Constraint =
    | Equals of Type * Type
    | Subtype of Type * Type
    
type Unified =
    struct 
     val substitution: Map<string, Type>
     val traits: Map<string, Trait list>
     val constraints: Constraint list
     new (subs, traits, constraints) = {
        substitution = subs
        traits = traits
        constraints = constraints
     }
    end

    new (constraints) = Unified (Map.empty, Map.empty, constraints)
    new (subs, traits) = Unified (subs, traits, [])

    member that.AddTrait x trt =
        Unified (that.substitution, that.traits.Add(x, trt))
        
    member that.AddSubstitution x subs =
        Unified (that.substitution.Add(x, subs), that.traits)
    
    member that.AddConstraint cons =
        Unified (that.substitution, that.traits, cons :: that.constraints)

type EnvAssociation =
    | Simple of Type
    | Universal of FreeVar list * Type

let mutable varType = 0
let getVarType traits =
    let newType = varType
    varType <- varType + 1
    VarType <| Var (sprintf "VarType%d" newType, traits)

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
        | Type.Tuple(types) -> 
            List.fold (fun acc x -> getFreeVars x env @ acc) [] types
        | Type.Record(pairs) -> 
            pairs |> List.unzip |> snd |> 
            List.fold (fun acc x -> getFreeVars x env @ acc) []
        | VarType {name = x; traits = traits} -> 
            let freeChecker = 
                (fun x' assoc -> 
                    match assoc with
                    | Simple (VarType {name = x1}) -> x1 = x
                    | _ -> false)
            if Map.exists freeChecker env then
                []
            else
                [(x, traits)]
    in Set(f typ) |> Set.toList

// Unify Helper Functions

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
        | Type.Tuple(types) ->
            Type.Tuple <| List.map f types
        | Type.Record(pairs) ->
            let names, types = List.unzip pairs
            Type.Record (List.zip names <| List.map f types)
        | VarType {name = id} ->
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
        | Subtype (s, t) ->
            Subtype (substituteInType subs s, substituteInType subs t)
    List.map f constraints

// Equals Constraint Solving

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
    | VarType {name = id} -> id = x

// Trait Constraint Solving

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
            substituteInConstraints (x, VarType <| Var (x, traits)) constraints

// Subtype Constraint Solving

let rec tryToExpand cons =
    match cons with
    | Equals (s, t) ->
        match s, t with
        | List s1, List t1 -> 
            Some <| [Equals (s1, t1)]
        | Function (s1, s2), Function (t1, t2) -> 
            Some <| [Equals (s1, t1); Equals (s2, t2)]
        | Type.Tuple typs1, Type.Tuple typs2 when typs1.Length = typs2.Length ->
            Some <| List.map2 (fun typ1 typ2 -> Equals (typ1, typ2)) typs1 typs2
        | Type.Record pairs1, Type.Record pairs2 
            when pairs1.Length = pairs2.Length && 
                 List.forall (fun (name1, _) -> List.exists (fun (name2, _) -> name2 = name1) pairs2) pairs1 ->
            
            let matchNames (name1, typ1) =
                let (name2, typ2) = List.find (fun (name2, typ2) -> name1 = name2) pairs2
                Equals (typ1, typ2)
                
            Some <| List.map matchNames pairs1
        | _ ->
            None
    | Subtype (s, t) ->
        match s, t with
        | Function(s1, s2), Function(t1, t2) -> 
                Some [Subtype (t1, s1); Subtype (s2, t2)]
        | Type.Tuple typs1, Type.Tuple typs2 when typs1.Length >= typs2.Length ->
            let f = (fun t1 t2 -> Subtype (t1, t2))
            let constraints = Seq.map2 f typs2 <| Seq.take typs2.Length typs1
            Some <| Seq.toList constraints
        | Type.Record pairs1, Type.Record pairs2 ->
            let names1, typs1 = List.unzip pairs1
            let names2, typs2 = List.unzip pairs2
            if Seq.forall (fun x -> Seq.exists ((=) x) names1) names2 then
                let f (indexInParent, acc) ident =
                    let indexInSubtype = Seq.findIndex ((=) ident) names1
                    indexInParent + 1, Subtype (Seq.nth indexInSubtype typs1, 
                        Seq.nth indexInParent typs2) :: acc
                let _, constraints = Seq.fold f (0, []) names2
                Some <| constraints
            else
                None
        | Type.Record pairs1, Type.Tuple typs2 when pairs1.Length >= typs2.Length ->
            let _, typs1 = List.unzip pairs1
            let f = (fun t2 t1 -> Subtype (t1, t2))
            let constraints = Seq.map2 f typs2 <| Seq.take (Seq.length typs2) typs1
            Some <| Seq.toList constraints
        | _ ->
            None

let rec expandSubtypeConstraint varName superType constraints =
    match constraints with
    | [] -> []
    | first :: rest ->
        match first with
        | Subtype (t2, VarType {name = x}) when x = varName ->
            let created = expandSubtypeConstraint x superType rest 
            let c = Subtype (t2, superType)
            if List.exists ((=) c) created then
                created
            else
                c :: created
        | Equals (VarType {name = x}, t2)
        | Equals (t2, VarType {name = x}) when x = varName ->
            let created = expandSubtypeConstraint x superType rest 
            let c = Subtype (t2, superType)
            if List.exists ((=) c) created then
                created
            else
                c :: created
        | _ ->
            let extras =
                match tryToExpand first with
                | Some values -> values
                | None -> []
            expandSubtypeConstraint varName superType <|
                rest @ extras
                    
// Main Unify 

let rec unify constraints =
//    for c in constraints do
//        match c with
//        | Equals (s,t) ->
//            printfn "%A = %A" (printType s) (printType t)
//    printfn ""
    match constraints with
    | [] -> Unified (Map.empty, Map.empty)
    | first::rest ->
        match first with
        | Equals (s, t)
        | Subtype (s, t) when s = t ->
            unify rest

        | Equals (VarType _ as s, t)
        | Equals (t, (VarType _ as s)) ->
            unifyVarType s t rest

        | Subtype (VarType {name = x} as s, t)
        | Subtype (t, (VarType {name = x} as s)) ->
            let uni = unify <| rest @ expandSubtypeConstraint x t rest 
            uni.AddConstraint first

        | _ ->
            match tryToExpand first with
            | Some cons -> unify <| rest @ cons
            | None ->
                raise <| InvalidType "Unsolvable constraints"

and unifyVarType t1 t2 rest =
    match t1, t2 with
    | VarType {name = x; traits = traits}, t 
    | t, VarType {name = x; traits = traits} when not <| occursIn x t ->
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
                    List.fold (fun acc (x, trts) -> acc.AddTrait x trts) unified free
            unified.AddSubstitution x t'
    | _ -> 
        raise <| InvalidType "Passed non-varType to varType function"

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
    | Type.Tuple(types) ->
        Type.Tuple <| List.map (fun typ -> applyType typ unified) types
    | Type.Record(pairs) ->
        let names, types = List.unzip pairs
        List.map (fun typ -> applyType typ unified) types |>
        List.zip names |> Type.Record
    | VarType {name = x} -> 
        if unified.substitution.ContainsKey x then
            applyType (unified.substitution.Item x) unified
        else if unified.traits.ContainsKey x then
            VarType <| Var (x, unified.traits.Item x)
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
            let newVars = List.map (fun (x, traits) -> x, getVarType traits) freeVars
            List.fold 
                (fun acc subs -> substituteInType subs acc)
                typ newVars, []
    else
        sprintf "Identifier %A undefined" id |> InvalidType |> raise

// collectConstraints term environment constraints
let rec collectConstraints term (env: Map<string, EnvAssociation>) =
    match term with
    | True ->
        Bool, []
    | False ->
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
        let x = getVarType []
        x, c1 @ [Equals (typ1, List x)]
    | Tail(t1) ->
        let typ1, c1 = collectConstraints t1 env
        let x = getVarType []
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
    | Tuple(terms) ->
        if List.length terms < 2 then
            sprintf "Tuple must have more than 2 components at %A" term |> InvalidType |> raise
        let types, constraints = 
            List.unzip <| 
            List.map (fun t -> collectConstraints t env) terms
        Type.Tuple types, List.reduce (@) constraints
    | Record(pairs) ->
        let names, types = List.unzip pairs
        if List.length types < 2 then
            sprintf "Record must have more than 2 values at %A" term |> InvalidType |> raise
        elif Set(names).Count < List.length names then
            sprintf "Record has duplicate fields at %A" term |> InvalidType |> raise
        let types', constraints = 
            List.unzip <| 
            List.map (fun t -> collectConstraints t env) types
        Type.Record (List.zip names types') , List.reduce (@) constraints
    | ProjectIndex(n, t1) ->
        let typ1, c1 = collectConstraints t1 env
        let retType = getVarType []
        let varType = 
            Type.Tuple <| 
            List.map (fun x -> getVarType []) [0..n-1] @ [retType]
        retType, [Subtype (typ1, varType)]
    | ProjectName(s, t1) ->
        let typ1, c1 = collectConstraints t1 env
        let retType = getVarType []
        let varType = Type.Record [s, retType]
        retType, [Subtype (typ1, varType)]
     

let typeInfer t =
    let typ, c = collectConstraints t Map.empty
    let uni = unify c
    let typ1 = applyType typ uni

    let freeVars = getFreeVars typ1 Map.empty

    let f c =
        match c with
        | Equals (s, t) 
        | Subtype (s, t) ->
            List.exists (fun (x, _) -> occursIn x s || occursIn x t) freeVars
                
    let c' = List.filter f uni.constraints
    typ1, Unified (uni.substitution, uni.traits, c')
