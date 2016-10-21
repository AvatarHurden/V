module TypeInference

open Definition

exception InvalidType of string

type Constraint =
    | Equals of Type * Type
    | Trait of Type * Trait

let mutable varType = 0
let getVarType unit =
    let newType = varType
    varType <- varType + 1
    sprintf "VarType%d" newType |> Type.X

let rec findId id e =
    match e with
    | [] ->
        sprintf "Identifier %A undefined" id |> InvalidType |> raise
    | (x, typ)::tl ->
        if x = id then
            typ, []
        else
            findId id tl

// collectConstraints term environment constraints
let rec collectConstraints term env =
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
    | OP(t1, Equal, t2) 
    | OP(t1, Different, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        Bool, c1 @ c2 @ [Equals (typ1, typ2); Trait (typ1, Equatable)]
    | OP(t1, op, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 env
        match op with
        | Add | Subtract | Multiply | Divide ->
            Int, c1 @ c2 @ [Equals (typ1, Int); Equals (typ2, Int)]
        | LessThan | LessOrEqual | GreaterOrEqual | GreaterThan ->
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
        let typ1, c1 = collectConstraints t1 ((id, typ)::env)
        Function(typ, typ1), c1
    | Fn(id, None, t1) ->
        let paramTyp = getVarType ()
        let typ1, c1 = collectConstraints t1 ((id, paramTyp)::env)
        Function(paramTyp, typ1), c1
    | Let(id, Some typ, t1, t2) ->
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 ((id, typ)::env)
        typ2, c1 @ c2 @ [Equals (typ, typ1)]
    | Let(id, None, t1, t2) ->
        let varTyp = getVarType ()
        let typ1, c1 = collectConstraints t1 env
        let typ2, c2 = collectConstraints t2 ((id, varTyp)::env)
        typ2, c1 @ c2 @ [Equals (varTyp, typ1)]
    | LetRec(id1, Some typ1, Some typ2, id2, t1, t2) ->
        let typ1', c1 = collectConstraints t1 ((id1, Function(typ1, typ2))::(id2, typ1)::env)
        let typ2', c2 = collectConstraints t2 ((id1, Function(typ1, typ2))::env)
        typ2', c1 @ c2 @ [Equals (typ2, typ1')]
    | LetRec(id1, None, None, id2, t1, t2) ->
        let fType = getVarType ()
        let paramTyp = getVarType ()
        let typ1, c1 = collectConstraints t1 ((id1, fType)::(id2, paramTyp)::env)
        let typ2, c2 = collectConstraints t2 ((id1, fType)::env)
        typ2, c1 @ c2 @ [Equals (fType, Function (paramTyp, typ1))]
    | LetRec(id1, _, _, id2, t1, t2) as t ->
        sprintf "Invalid recursive let defintion at %A" t |> InvalidType |> raise
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

// Equals Unify Functions

let rec occursIn x typ =
    match typ with
    | Int
    | Bool -> false
    | List(t1) -> occursIn x t1
    | Function(t1, t2) -> occursIn x t1 || occursIn x t2
    | Type.X(id) -> id = x
    

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
        | Trait (typ, trait') ->
            Trait (substituteInType subs typ, trait')
    List.map f constraints

// Trait Unify Functions

let rec expandTraitConstraint (Trait (typ, trait') as constraint') list =
    match list with
    | [] -> []
    | first::rest ->
        match first with
        | Equals (s, t) | Equals (t, s) when s = typ ->
            (expandTraitConstraint constraint' <| rest) @ [Trait (t, trait')]
        | _ -> 
            expandTraitConstraint constraint' rest

let rec getTraitRequirements typ trait' =
    match trait' with
    | Equatable ->
        match typ with
        | Int | Bool -> []
        | Type.X x as typ' -> [Trait (typ', Equatable)]
        | List typ' -> getTraitRequirements typ' trait'
        | Function (_, _) -> 
            raise <| InvalidType "Did not meet equatable trait requirement" 

// Main Unify Functions

let rec unify constraints =
    match constraints with
    | [] -> Map.empty
    | first::rest ->
        match first with
        | Trait (typ, trait') as c ->
            match typ with
            | Type.X _ ->
                unify <| rest @ (expandTraitConstraint c rest)
            | _ ->
                unify <| rest @ (getTraitRequirements typ trait')
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
            substitutions.[x]
        else
            raise <| InvalidType "Unsolvable type"

let typeInfer t =
    let typ, c = collectConstraints t []
    let substitutions = unify c
    applyType typ substitutions
