module Translation

open Definition

let rec translate term =
    match term with
    | ExB b -> B b
    | ExI i -> I i
    | ExC c -> C c
    | ExOP (t1, op, t2) -> OP(translate t1, op, translate t2)
    | ExCond (t1, t2, t3) -> Cond(translate t1, translate t2, translate t3)
    | ExX x -> X x
    | ExFn (pat, t) -> Fn(pat, translate t)
    | ExRecFn (id, typ, pat, t) -> RecFn(id, typ, pat, translate t)
    | ExMatch (t1, patterns) -> 
        let f (p, cond, res) =
            match cond with
            | None -> (p, None, translate res)
            | Some cond -> (p, Some <| translate cond, translate res)
        Match(translate t1, List.map f patterns)
    | ExLet (p, t1, t2) -> Let(p, translate t1, translate t2)
    | ExNil -> Nil
    | ExRaise -> Raise
    | ExTuple terms -> Tuple <| List.map translate terms
    | ExRecord pairs -> Record <| List.map (fun (s, t) -> (s, translate t)) pairs
    | ExRecordAccess (s, t1, t2) -> RecordAccess(s, translate t1, translate t2)

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

let rec extend term =
    match term with
    | B b -> ExB b
    | I i -> ExI i
    | C c -> ExC c
    | OP (t1, op, t2) -> ExOP(extend t1, op, extend t2)
    | Cond (t1, t2, t3) -> ExCond(extend t1, extend t2, extend t3)
    | X x -> ExX x
    | Fn (p, t) -> ExFn(p ,extend t)
    | RecFn (id, typ, p, t) -> ExRecFn(id, typ, p, extend t)
    | Match (t1, patterns) -> 
        let f (p, cond, res) =
            match cond with
            | None -> (p, None, extend res)
            | Some cond -> (p, Some <| extend cond, extend res)
        ExMatch(extend t1, List.map f patterns)
    | Let (p, t1, t2) -> ExLet(p, extend t1, extend t2)
    | Nil -> ExNil
    | Raise -> ExRaise
    | Tuple terms -> ExTuple <| List.map extend terms
    | Record pairs -> ExRecord <| List.map (fun (s, t) -> (s, extend t)) pairs
    | RecordAccess (s, t1, t2) -> ExRecordAccess(s, extend t1, extend t2)