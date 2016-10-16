module TypeInference

open Definition

exception InvalidType of string

let mutable varType = 0

let getVarType unit =
    let newType = varType in
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

// collectEqs term environment constraints
let rec collectEqs t e =
    match t with
    | True ->
        Bool, []
    | False ->
        Bool, []
    | I(i) ->
        Int, []
    | OP(t1, Application, t2) ->
        let t1', c1 = collectEqs t1 e in
        let t2', c2 = collectEqs t2 e in
        let x = getVarType () in
        x, c1 @ c2 @ [t1', Function(t2', x)]
    | OP(t1, Cons, t2) ->
        let t1', c1 = collectEqs t1 e in
        let t2', c2 = collectEqs t2 e in
        t1' |> List, c1 @ c2 @ [t1' |> List, t2']
    | OP(t1, op, t2) ->
        let t1', c1 = collectEqs t1 e in
        let t2', c2 = collectEqs t2 e in
        match op with
        | Add | Subtract | Multiply | Divide ->
            Int, c1 @ c2 @ [t1', Int; t2', Int]
        | LessThan | LessOrEqual | Equal | Different | GreaterOrEqual | GreaterThan ->
            Bool, c1 @ c2 @ [t1', Int; t2', Int]
        | _ -> sprintf "Unknown operator at %A" t |> InvalidType |> raise
    | Cond(t1, t2, t3) ->
        let t1', c1 = collectEqs t1 e in
        let t2', c2 = collectEqs t2 e in
        let t3', c3 = collectEqs t3 e in
        t2', c1 @ c2 @ c3 @ [t1', Bool; t2', t3']
    | X(id) ->
        findId id e
    | Fn(id, Some typ, t1) ->
        let t1', c1 = collectEqs t1 ((id, typ)::e) in
        Function(typ, t1'), c1
    | Fn(id, None, t1) ->
        let paramTyp = getVarType ()
        let t1', c1 = collectEqs t1 ((id, paramTyp)::e) in
        Function(paramTyp, t1'), c1
    | Let(id, Some typ, t1, t2) ->
        let t1', c1 = collectEqs t1 e in
        let t2', c2 = collectEqs t2 ((id, typ)::e) in
        t2', c1 @ c2 @ [typ, t1']
    | Let(id, None, t1, t2) ->
        let varTyp = getVarType ()
        let t1', c1 = collectEqs t1 e in
        let t2', c2 = collectEqs t2 ((id, varTyp)::e) in
        t2', c1 @ c2 @ [varTyp, t1']
    | LetRec(id1, Some typ1, Some typ2, id2, t1, t2) ->
        let t1', c1 = collectEqs t1 ((id1, Function(typ1, typ2))::(id2, typ1)::e) in
        let t2', c2 = collectEqs t2 ((id1, Function(typ1, typ2))::e) in
        t2', c1 @ c2 @ [typ2, t1']
    | LetRec(id1, None, None, id2, t1, t2) ->
        let fType = getVarType ()
        let paramTyp = getVarType ()
        let t1', c1 = collectEqs t1 ((id1, fType)::(id2, paramTyp)::e) in
        let t2', c2 = collectEqs t2 ((id1, fType)::e) in
        t2', c1 @ c2 @ [fType, Function(paramTyp, t1')]
    | Nil ->
        getVarType () |> List, []
    | Head(t1) | Tail(t1) ->
        let t1', c1 = collectEqs t1 e
        let x = getVarType () in
        x, c1 @ [t1', x |> List]
    | IsEmpty(t1) ->
        let t1', c1 = collectEqs t1 e
        Bool, c1 @ [t1', getVarType () |> List]
    | Raise ->
        getVarType (), []
    | Try(t1, t2) ->
        let t1', c1 = collectEqs t1 e in
        let t2', c2 = collectEqs t2 e in
        t2', c1 @ c2 @ [t1', t2']

let substinty x t s =
    let rec f s =
        match s with
        | Int -> Int
        | Bool -> Bool
        | List(s1) -> List(f s1)
        | Function(s1, s2) -> Function(f s1, f s2)
        | Type.X(id) ->
            if id = x then
                t
            else
                Type.X(id)
    in f s

let substintconstr x t c =
    List.map
        (fun (s1, s2) ->
            (substinty x t s1, substinty x t s2))
        c

let occursin x t =
    let rec o t =
        match t with
        | Int
        | Bool -> false
        | List(t1) -> o t1
        | Function(t1, t2) -> o t1 || o t2
        | Type.X(id) -> id = x
    in o t

let rec unify c =
    match c with
    | [] -> []
    | (s, t)::rest when s = t -> unify rest
    | (Type.X(x), t)::rest | (t, Type.X(x))::rest ->
        if occursin x t then
            sprintf "Circular constraints" |> InvalidType |> raise
        else
            unify (substintconstr x t rest) @ [Type.X(x), t]
    | (List(s1), List(t1))::rest -> unify (rest @ [s1, t1])
    | (Function(s1, s2), Function(t1, t2))::rest -> unify (rest @ [s1, t1; s2, t2])
    | _ -> sprintf "Unsolvable constraints" |> InvalidType |> raise

let applyType t c =
    let rec substitute x c =
        match c with
        | [] ->
            sprintf "Unsolvable type" |> InvalidType |> raise
        | (s, t)::rest ->
            if s = x then
                t
            else
                substitute x rest
    let rec findX t =
        match t with
        | Int -> Int
        | Bool -> Bool
        | List(t1) -> List(findX t1)
        | Function(t1, t2) -> Function(findX t1, findX t2)
        | Type.X(x) -> substitute (Type.X(x)) c
    in findX t

let typeInfer t =
    let typ, c = collectEqs t [] in
    applyType typ (unify c)
