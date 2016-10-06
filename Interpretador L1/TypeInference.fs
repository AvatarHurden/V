module TypeInference

open Definition

let mutable varType = 0

let getVarType unit =
    let newType = varType in
    varType <- varType + 1
    sprintf "VarType%d" newType

let rec findId id e =
    match e with
    | [] ->
        sprintf "Identifier %A undefined" id |> WrongExpression |> raise
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
        let x = getVarType () |> Type.X in
        x, c1 @ c2 @ [t1', Function(t2', x)]
    | OP(t1, Cons, t2) ->
        let t1', c1 = collectEqs t1 e in
        let t2', c2 = collectEqs t2 e in
        t1' |> List, c1 @ c2 @ [t1', t2']
    | OP(t1, op, t2) ->
        let t1', c1 = collectEqs t1 e in
        let t2', c2 = collectEqs t2 e in
        match op with
        | Add | Subtract | Multiply | Divide ->
            Int, c1 @ c2 @ [t1', Int; t2', Int]
        | LessThan | LessOrEqual | Equal | Different | GreaterOrEqual | GreaterThan ->
            Bool, c1 @ c2 @ [t1', Int; t2', Int]
        | _ -> sprintf "Unknown operator at %A" t |> WrongExpression |> raise
    | Cond(t1, t2, t3) ->
        let t1', c1 = collectEqs t1 e in
        let t2', c2 = collectEqs t2 e in
        let t3', c3 = collectEqs t3 e in
        t2', c1 @ c2 @ c3 @ [t1', Bool; t2', t3']
    | X(id) ->
        findId id e
    | Fn(id, typ, t1) ->
        let t1', c1 = collectEqs t1 ((id, typ)::e) in
        Function(typ, t1'), c1
    | Let(id, typ, t1, t2) ->
        let t1', c1 = collectEqs t1 e in
        let t2', c2 = collectEqs t2 ((id, typ)::e) in
        t2', c1 @ c2 @ [typ, t1']
    | LetRec(id1, typ1, typ2, id2, t1, t2) ->
        let t1', c1 = collectEqs t1 ((id1, Function(typ1, typ2))::(id2, typ1)::e) in
        let t2', c2 = collectEqs t2 ((id1, Function(typ1, typ2))::e) in
        t2', c1 @ c2 @ [typ2, t1']
    | Nil ->
        getVarType () |> Type.X |> List, []
    | Head(t1) | Tail(t1) ->
        let t1', c1 = collectEqs t1 e
        let x = getVarType () |> Type.X in
        x, c1 @ [t1', x |> List]
    | IsEmpty(t1) ->
        let t1', c1 = collectEqs t1 e
        Bool, c1 @ [t1', getVarType () |> Type.X |> List]
    | Raise ->
        getVarType () |> Type.X, []
    | Try(t1, t2) ->
        let t1', c1 = collectEqs t1 e in
        let t2', c2 = collectEqs t2 e in
        t2', c1 @ c2 @ [t1', t2']
