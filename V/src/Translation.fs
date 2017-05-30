module Translation

open Definition

let rec private translateType typ (env: TranslationEnv) =
    match typ with
    | ExVarType (s, traits) -> VarType (s, traits)
    | ExChar -> Char
    | ExBool -> Bool
    | ExInt -> Int
    | ExList t -> List <| translateType t env
    | ExFunction (t1, t2) -> Function (translateType t1 env, translateType t2 env)
    | ExTupleType ts -> 
        Type.Tuple <| List.map (fun t -> translateType t env) ts
    | ExRecordType ts -> 
        Type.Record <| List.map (fun (s, t) -> s, translateType t env) ts
    | ExTypeAlias s -> 
        match env.typeAliases.TryFind s with
        | Some typ -> typ
        | None -> raise <| ParseException (sprintf "The type %s is undeclared" s)

let private translateSomeType typ env = 
    match typ with
    | None -> None
    | Some typ -> Some <| translateType typ env

let private translatePatterns patterns env =
    let rec findRepeats (ids: Set<Ident>) ((pattern, typ)) =
        match pattern with
        | ExIgnorePat -> Pat (IgnorePat, translateSomeType typ env), ids
        | ExNilPat -> Pat (NilPat, translateSomeType typ env), ids
        | ExBPat b -> Pat (BPat b, translateSomeType typ env), ids
        | ExIPat i -> Pat (IPat i, translateSomeType typ env), ids
        | ExCPat c -> Pat (CPat c, translateSomeType typ env), ids
        | ExXPat x -> 
            if ids.Contains x then
                raise <| ParseException (sprintf "The identifier %s is bound twice" x)
            else
                Pat (XPat x, translateSomeType typ env), ids.Add x
        | ExTuplePat patterns ->
            let f pat (acc, pats) =
                let (newPat, acc') = findRepeats acc pat
                (acc', newPat :: pats)
            let (ids', pats) = List.foldBack f patterns (ids, [])
            Pat (TuplePat pats, translateSomeType typ env), ids'
        | ExRecordPat (b, patterns) ->
            let f (s, pat) (acc, pats) =
                let (newPat, acc') = findRepeats acc pat
                (acc', (s, newPat) :: pats)
            let (ids', pats) = List.foldBack f patterns (ids, [])
            Pat (RecordPat (b, pats), translateSomeType typ env), ids'
        | ExConsPat (p1, p2) ->
            let p1', ids' = findRepeats ids p1
            let p2', ids' = findRepeats ids' p2
            Pat (ConsPat (p1', p2'), translateSomeType typ env), ids'
     
    let f pat (acc, pats) =
        let (newPat, acc') = findRepeats acc pat
        (acc', newPat :: pats)
    let (ids', pats) = List.foldBack f patterns (Set.empty, [])
    pats

let private translatePattern pat env = List.head <| translatePatterns [pat] env

let private condenseFunction name parameters retTerm retTyp =
    let f p (func, funcType: Type option) = 
        match p with
        | Pat(_, Some typ) when funcType.IsSome ->
            Fn(p, func), Some <| Function(typ, funcType.Value) 
        | Pat (_, _) ->
            Fn(p, func), None
    
    let fn, typ = List.foldBack f parameters (retTerm, retTyp)
    fn, typ

let rec private condenseNamedFunction isRec id parameters retTyp retTerm env =
    match parameters with
    | [] -> 
        let t' =  translateTerm retTerm env
        Pat(XPat id, retTyp), t'
    | head :: tail ->
        let recName = (if isRec then Some id else None)
        let t' = translateTerm retTerm env
        let retTerm, retTyp = condenseFunction recName tail t' retTyp
           
        let fnTyp = 
            match head with
            | Pat(_, Some typ) when retTyp.IsSome -> 
                Some <| Function(typ, retTyp.Value)
            | Pat(_, _) -> None

        if isRec then
            Pat(XPat id, fnTyp), RecFn(id, retTyp, head, retTerm)
        else
            Pat(XPat id, fnTyp), Fn(head, retTerm)

and private translateDecl decl env = 
    match decl with
    | DeclConst (p, t1) -> 
        let p' = translatePattern p env
        let t1' = translateTerm t1 env
        [(p', t1')], env
    | DeclFunc (isRec, id, parameters, retTyp, retTerm) ->
        let parameters' = translatePatterns parameters env
        let typ' = translateSomeType retTyp env
        let pat, fn = condenseNamedFunction isRec id parameters' typ' retTerm env
        [(pat, fn)], env
    | DeclImport (comps) -> comps, env
    | DeclAlias (s, typ) ->
        let env' = env.addTypeAlias s <| translateType typ env
        [], env'

and private translateTerm term env =
    match term with
    | ExB b -> B b
    | ExI i -> I i
    | ExC c -> C c
    | ExOP (t1, op, t2) -> 
        let t1' = translateTerm t1 env
        let t2' = translateTerm t2 env
        OP(t1', op, t2')
    | ExCond (t1, t2, t3) -> 
        let t1' = translateTerm t1 env
        let t2' = translateTerm t2 env
        let t3' = translateTerm t3 env
        Cond(t1', t2', t3')
    | ExX x -> X x
    | ExFn (pars, t) -> 
        let pars' = translatePatterns pars env
        let t' = translateTerm t env
        let fn, typ = condenseFunction None pars' t' None
        fn
    | ExRecFn (id, pars, typ, t) -> 
        let pars' = translatePatterns pars env
        let typ' = translateSomeType typ env
        let pat, fn = condenseNamedFunction true id pars' typ' t env
        fn
        
    | ExMatch (t1, patterns) -> 
        let f (p, cond, res) =
            match cond with
            | None -> 
                let p' = translatePattern p env
                let res' = translateTerm res env
                (p', None, res')
            | Some cond ->
                let p' = translatePattern p env
                let cond' = translateTerm cond env
                let res' = translateTerm res env
                (p', Some cond', res')
        let t1' = translateTerm t1 env
        Match(t1', List.map f patterns)

    | ExLet (decl, t2) ->
        let comps, env' = translateDecl decl env
        let t2' = translateTerm t2 env'
        List.foldBack (fun (p, t) acc -> Let(p, t, acc)) comps t2'
            
    | ExNil -> Nil
    | ExRaise -> Raise
    | ExTuple terms -> 
        Tuple <| List.map (fun t -> translateTerm t env) terms
    | ExRecord pairs -> 
        Record <| List.map (fun (s, t) -> (s, translateTerm t env)) pairs
    | ExRecordAccess (s, t1, t2) -> 
        let t1' = translateTerm t1 env
        let t2' = translateTerm t2 env
        RecordAccess (s, t1', t2')
        
    | Range (first, second, last) ->
        let first' = translateTerm first env
        let last' = translateTerm last env
        let increment =
            match second with
            | None -> I 1
            | Some second -> 
                let second' = translateTerm second env
                OP(second', Subtract, first')
        OP (
            OP (
                OP (X "range", Application, first'), 
             Application, last'), 
         Application, increment)
    | Comprehension (retTerm, p, source) ->
        let f = Fn (translatePattern p env, translateTerm retTerm env)
        OP (OP (X "map", Application, f), Application, translateTerm source env)
       
let translateLib declarations env =
    let f (comps, env) decl =
        let newComps, env' = translateDecl decl env
        comps @ newComps, env'
    List.fold f ([], env) declarations

let translate term env =
    translateTerm term env