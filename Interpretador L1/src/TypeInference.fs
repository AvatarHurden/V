module TypeInference

open Definition
open Parser

exception InvalidType of string

type Constraint =
    | Equals of Type * Type

type EnvAssociation =
    | Simple of Type
    | Universal of Ident list * Type

let mutable varType = 0
let getVarType unit =
    let newType = varType
    varType <- varType + 1
    sprintf "VarType%d" newType |> Type.X

let substituteInType subs typ' =
    let x, typ = subs
    let rec f s =
        match s with
        | Int -> Int
        | Bool -> Bool
        | List(s1) -> List(f s1)
        | Function(s1, s2) -> Function(f s1, f s2)
        | Type.X(id) ->
            if id = x then
                typ
            else
                Type.X(id)
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
    | Bool -> false
    | List(t1) -> occursIn x t1
    | Function(t1, t2) -> occursIn x t1 || occursIn x t2
    | Type.X(id) -> id = x

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
        | Equals (s, t) ->
            match s, t with
            | s, t when s = t -> unify rest
            | Type.X x, t | t, Type.X x ->
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
    | List(t1) -> 
        List(applyType t1 substitutions)
    | Function(t1, t2) -> 
        Function(applyType t1 substitutions, applyType t2 substitutions)
    | Type.X(x) -> 
        if Map.containsKey x substitutions then
            applyType substitutions.[x] substitutions
        else
            typ

let findId id (e: Map<string, EnvAssociation>) =
    if e.ContainsKey id then
        match e.[id] with
        | Simple typ ->
            typ, []
        | Universal (freeVars, typ) ->
            List.fold 
                (fun acc x -> substituteInType (x, getVarType ()) acc)
                typ freeVars, []
    else
        sprintf "Identifier %A undefined" id |> InvalidType |> raise

let rec getFreeVars typ (env: Map<string, EnvAssociation>) =
    match typ with
    | Int -> []
    | Bool -> []
    | List(t1) -> getFreeVars t1 env
    | Function(t1, t2) -> getFreeVars t1 env @ getFreeVars t2 env
    | Type.X x -> 
        let isFree = Map.exists (fun x' assoc -> 
            match assoc with
            | Simple (Type.X x1) -> x1 = x
            | _ -> false) env
        if isFree then
            []
        else
            [x]
         
// collectConstraints term environment constraints
let rec collectConstraints term (env: Map<string, EnvAssociation>) =
    match term with
    | True ->
        Bool, []
    | False ->
        Bool, []
    | I(i) ->
        Int, []
    | OP(t1, Application, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        let x = getVarType ()
        x, c1 @ c2 @ [Equals (typ1, Function (typ2, x))]
    | OP(t1, Cons, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        typ1 |> List, c1 @ c2 @ [Equals (List typ1, typ2)]
    | OP(t1, op, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        match op with
        | Add | Subtract | Multiply | Divide ->
            Int, c1 @ c2 @ [Equals (typ1, Int); Equals (typ2, Int)]
        | LessThan | LessOrEqual | Equal | Different | GreaterOrEqual | GreaterThan ->
            Bool, c1 @ c2 @ [Equals (typ1, Int); Equals (typ2, Int)]
        | _ -> sprintf "Unknown operator at %A" term |> InvalidType |> raise
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
        let assoc, cons = 
            if freeVars.IsEmpty then
                let varTyp = getVarType ()
                Simple varTyp, [Equals (varTyp, typ1)]
            else
                Universal (freeVars, typ1'), []
        let typ2, c2 = collectConstraints t2  <| env.Add(id, assoc)
        typ2, c1 @ c2 @ cons
    | Nil ->
        getVarType () |> List, []
    | Head(t1) ->
        let typ1, c1 = collectConstraints t1 env
        let x = getVarType () in
        x, c1 @ [Equals (typ1, List x)]
    | Tail(t1) ->
        let typ1, c1 = collectConstraints t1 env
        let x = getVarType () in
        x |> List, c1 @ [Equals (typ1, List x)]
    | IsEmpty(t1) ->
        let typ1, c1 = collectConstraints t1 env
        Bool, c1 @ [Equals (typ1, List <| getVarType ())]
    | Raise ->
        getVarType (), []
    | Try(t1, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        typ2, c1 @ c2 @ [Equals (typ1, typ2)]
    | Closure(_, _, _) | RecClosure(_, _, _, _) as t->
        sprintf "Cannot collect constraints for a closure at %A" t |> InvalidType |> raise



let typeInfer t =
    let typ, c = collectConstraints t Map.empty
    let substitutions = unify c
    applyType typ substitutions
