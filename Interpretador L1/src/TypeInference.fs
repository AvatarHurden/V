module TypeInference

open Definition
open Printer

exception InvalidType of string

type Constraint =
    | Equals of Type * Type
    | Trait of Type * Trait

type EnvAssociation =
    | Simple of Type
    | Universal of Ident list * Type * Constraint list

let mutable varType = 0
let getVarType unit =
    let newType = varType
    varType <- varType + 1
    VarType <| sprintf "VarType%d" newType

    
// Trait Unify Functions

let rec expandTraitConstraint (Trait (typ, trait') as constraint') list =
    match list with
    | [] -> []
    | first::rest ->
        match first with
        | Equals (t1, t2) ->
            match t1, t2 with
            | List t1', List t2' -> 
                expandTraitConstraint constraint' <| rest @ [Equals (t1', t2')]
            | Function (t1', t1''), Function (t2', t2'') ->
                expandTraitConstraint constraint' <| rest @ [Equals (t1', t2'); Equals (t1'', t2'')]
            | t1, t2 | t2, t1 when t1 = typ ->
                (expandTraitConstraint constraint' <| rest) @ [Trait (t2, trait')]
            | _ ->
                expandTraitConstraint constraint' rest
        | _ -> 
            expandTraitConstraint constraint' rest

let rec getTraitRequirements typ trait' =
    match trait' with
    | Equatable ->
        match typ with
        | Int | Bool | Char -> []
        | VarType x as typ' -> [Trait (typ', Equatable)]
        | List typ' -> getTraitRequirements typ' trait'
        | Function (_, _) | Unit -> 
            raise <| InvalidType "Did not meet equatable trait requirement" 
    | Orderable ->
        match typ with
        | Int | Char -> []
        | VarType x as typ' -> [Trait (typ', Orderable)]
        | List typ' -> getTraitRequirements typ' trait'
        | Bool | Unit | Function (_, _) -> 
            raise <| InvalidType "Did not meet orderable trait requirement"

// Polimorphism Functions

let rec getFreeVars typ (env: Map<string, EnvAssociation>) =
    match typ with
    | Int -> []
    | Bool -> []
    | Char -> []
    | Unit -> []
    | List(t1) -> getFreeVars t1 env
    | Function(t1, t2) -> getFreeVars t1 env @ getFreeVars t2 env
    | VarType x -> 
        let freeChecker = 
            (fun x' assoc -> 
                match assoc with
                | Simple (VarType x1) -> x1 = x
                | _ -> false)
        let isFree = Map.exists freeChecker env
        if isFree then
            []
        else
            [x]

let rec getConstraintsForFreeVars constraints (freeVars: Ident list) =
    match constraints with
    | [] -> []
    | first::rest ->
        match first with
        | Trait (VarType x, trait') as c ->
            if List.exists (fun id -> id = x) freeVars then
                [c] @ getConstraintsForFreeVars rest freeVars
            else
                getConstraintsForFreeVars rest freeVars
        | _ ->
           getConstraintsForFreeVars rest freeVars

// Normal Unify Functions

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
        | VarType(id) ->
            if id = x then
                typ
            else
                VarType(id)
    in f typ'

let substituteInConstraints subs constraints =
    let x, typ = subs
    let f cons =
        match cons with
        | Trait (typ, trait') ->
            Trait (substituteInType subs typ, trait')
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
    | VarType(id) -> id = x

let rec unify constraints =
//    for c in constraints do
//        match c with
//        | Equals (s,t) ->
//            printfn "%A = %A" (typeString s) (typeString t)
//    printfn ""
    match constraints with
    | [] -> Map.empty
    | first::rest ->
        match first with
        | Trait (typ, trait') as c ->
            match typ with
            | VarType _ ->
                unify <| rest @ (expandTraitConstraint c rest)
            | _ ->
                unify <| rest @ (getTraitRequirements typ trait')
        | Equals (s, t) ->
            match s, t with
            | s, t when s = t -> unify rest
            | VarType x, t | t, VarType x ->
                if occursIn x t then
                    sprintf "Circular constraints" |> InvalidType |> raise
                else
                    let subs = unify (substituteInConstraints (x, t) rest) 
                    subs.Add(x, t)
            | List s1, List t1 -> 
                unify <| rest @ [Equals (s1, t1)]
            | Function(s1, s2), Function(t1, t2) -> 
                unify <| rest @ [Equals (s1, t1); Equals (s2, t2)]
            | _ -> 
                raise <| InvalidType "Unsolvable constraints"

let rec applyType typ substitutions =
    match typ with
    | Int -> Int
    | Bool -> Bool
    | Char -> Char
    | Unit -> Unit
    | List(t1) -> 
        List(applyType t1 substitutions)
    | Function(t1, t2) -> 
        Function(applyType t1 substitutions, applyType t2 substitutions)
    | VarType(x) -> 
        if Map.containsKey x substitutions then
            applyType substitutions.[x] substitutions
        else
            typ

// Constraint Collection Functions

let findId id (e: Map<string, EnvAssociation>) =
    if e.ContainsKey id then
        match e.[id] with
        | Simple typ ->
            typ, []
        | Universal (freeVars, typ, constraints) ->
            let newVars = List.map (fun x -> x, getVarType ()) freeVars
            List.fold 
                (fun acc subs -> substituteInType subs acc)
                typ newVars, 
            List.fold 
                (fun acc subs -> substituteInConstraints subs acc)
                constraints newVars
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
        let x = getVarType ()
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
        Bool, c1 @ c2 @ [Equals (typ1, typ2); Trait (typ1, Equatable); Trait (typ2, Equatable)]
    | OP(t1, LessThan, t2)
    | OP(t1, LessOrEqual, t2)
    | OP(t1, GreaterOrEqual, t2)
    | OP(t1, GreaterThan, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        Bool, c1 @ c2 @ [Equals (typ1, typ2); Trait (typ1, Orderable); Trait (typ2, Orderable)]
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
        let paramTyp = getVarType ()
        let typ1, c1 = collectConstraints t1 <| env.Add(id, Simple paramTyp)
        Function(paramTyp, typ1), c1
    | RecFn(id1, Some typ1, id2, Some typ2, t1) ->
        let env1 = env.Add(id1, Simple <| Function(typ2, typ1)).Add(id2, Simple typ2)
        let typ1', c1 = collectConstraints t1 env1
        Function (typ2, typ1), c1 @ [Equals (typ1', typ1)]
    | RecFn(id1, None, id2, None, t1) ->
        let fType = getVarType ()
        let paramTyp = getVarType ()
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
        let typ1' = unify c1 |> applyType typ1
        let freeVars = getFreeVars typ1' env
        let c1' = getConstraintsForFreeVars c1 freeVars
        let assoc, cons = 
            if freeVars.IsEmpty then
                let varTyp = getVarType ()
                Simple varTyp, [Equals (varTyp, typ1)]
            else
                Universal (freeVars, typ1', c1'), []
        let typ2, c2 = collectConstraints t2  <| env.Add(id, assoc)
        typ2, c1 @ c2 @ cons
    | Nil ->
        List <| getVarType (), []
    | Head(t1) ->
        let typ1, c1 = collectConstraints t1 env
        let x = getVarType () in
        x, c1 @ [Equals (typ1, List x)]
    | Tail(t1) ->
        let typ1, c1 = collectConstraints t1 env
        let x = getVarType () in
        List x, c1 @ [Equals (typ1, List x)]
    | IsEmpty(t1) ->
        let typ1, c1 = collectConstraints t1 env
        Bool, c1 @ [Equals (typ1, List <| getVarType ())]
    | Raise ->
        getVarType (), []
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
