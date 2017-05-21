module Translation

open Definition

let condenseFunction name parameters retTerm retTyp =
    let f p (func, funcType: Type option) = 
        match p with
        | Pat(_, Some typ) when funcType.IsSome ->
            Fn(p, func), Some <| Function(typ, funcType.Value) 
        | Pat (_, _) ->
            Fn(p, func), None

    List.foldBack f parameters (retTerm, retTyp)

let rec condenseNamedFunction isRec id head tail retTyp retTerm =
    let recName = (if isRec then Some id else None)
    let retTerm, retTyp = 
        condenseFunction recName tail (translate retTerm) retTyp

    let fnTyp = 
        match head with
        | Pat(_, Some typ) when retTyp.IsSome -> 
            Some <| Function(typ, retTyp.Value)
        | Pat(_, _) -> None

    if isRec then
        Pat(XPat id, fnTyp), RecFn(id, retTyp, head, retTerm)
    else
        Pat(XPat id, fnTyp), Fn(head, retTerm)

and translateDecl decl = 
    match decl with
    | DeclConst (p, t1) -> (p, translate t1)
    | DeclFunc (isRec, id, [], retTyp, retTerm) ->
        Pat(XPat id, retTyp), translate retTerm
    | DeclFunc (isRec, id, head :: tail, retTyp, retTerm) ->
        condenseNamedFunction isRec id head tail retTyp retTerm

and translate term =
    match term with
    | ExB b -> B b
    | ExI i -> I i
    | ExC c -> C c
    | ExOP (t1, op, t2) -> OP(translate t1, op, translate t2)
    | ExCond (t1, t2, t3) -> Cond(translate t1, translate t2, translate t3)
    | ExX x -> X x
    | ExFn (pars, t) -> fst <| condenseFunction None pars (translate t) None
    | ExRecFn (id, pars, typ, t) -> 
        let head :: tail = pars
        snd <| condenseNamedFunction true id head tail typ t
        
    | ExMatch (t1, patterns) -> 
        let f (p, cond, res) =
            match cond with
            | None -> (p, None, translate res)
            | Some cond -> (p, Some <| translate cond, translate res)
        Match(translate t1, List.map f patterns)

    | ExLet (decl, t2) ->
        let (p, t1) = translateDecl decl
        Let(p, t1, translate t2)

    | ExNil -> Nil
    | ExRaise -> Raise
    | ExTuple terms -> Tuple <| List.map translate terms
    | ExRecord pairs -> Record <| List.map (fun (s, t) -> (s, translate t)) pairs
    | ExRecordAccess (s, t1, t2) -> RecordAccess (s, translate t1, translate t2)
        
    | Range (first, second, last) ->
        let increment =
            match second with
            | None -> I 1
            | Some second -> 
                OP(translate second, Subtract, translate first)
        OP (
            OP (
                OP (X "range", Application, translate first), 
             Application, translate last), 
         Application, increment)
    | Comprehension (retTerm, p, source) ->
        let f = Fn (p, translate retTerm)
        OP (OP (X "map", Application, f), Application, translate source)

let rec extendDecl decl =
    let (p, t) = decl
    DeclConst(p, extend t)

and extend term =
    match term with
    | B b -> ExB b
    | I i -> ExI i
    | C c -> ExC c
    | OP (t1, op, t2) -> ExOP(extend t1, op, extend t2)
    | Cond (t1, t2, t3) -> ExCond(extend t1, extend t2, extend t3)
    | X x -> ExX x
    | Fn (p, t) -> ExFn([p] ,extend t)
    | RecFn (id, typ, p, t) -> ExRecFn(id, [p], typ, extend t)
    | Match (t1, patterns) -> 
        let f (p, cond, res) =
            match cond with
            | None -> (p, None, extend res)
            | Some cond -> (p, Some <| extend cond, extend res)
        ExMatch(extend t1, List.map f patterns)
    | Let (p, t1, t2) -> ExLet(DeclConst(p, extend t1), extend t2)
    | Nil -> ExNil
    | Raise -> ExRaise
    | Tuple terms -> ExTuple <| List.map extend terms
    | Record pairs -> ExRecord <| List.map (fun (s, t) -> (s, extend t)) pairs
    | RecordAccess (s, t1, t2) -> ExRecordAccess(s, extend t1, extend t2)