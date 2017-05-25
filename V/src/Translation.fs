module Translation

open Definition

type Env = 
    {typeAliases: Map<string, Type>}

let rec translateType typ =
    match typ with
    | ExVarType (s, traits) -> VarType (s, traits)
    | ExChar -> Char
    | ExBool -> Bool
    | ExInt -> Int
    | ExList t -> List <| translateType t
    | ExFunction (t1, t2) -> Function (translateType t1, translateType t2)
    | ExTupleType ts ->  Type.Tuple <| List.map translateType ts
    | ExRecordType ts ->  Type.Record <| List.map (fun (s, t) -> s, translateType t) ts

let rec translateSomeType typ = 
    match typ with
    | None -> None
    | Some typ -> Some <| translateType typ


// Validates and returns the inputted pattern list
let translatePatterns patterns =
    let rec findRepeats (ids: Set<Ident>) ((pattern, typ)) =
        match pattern with
        | ExIgnorePat -> Pat (IgnorePat, translateSomeType typ), ids
        | ExNilPat -> Pat (NilPat, translateSomeType typ), ids
        | ExBPat b -> Pat (BPat b, translateSomeType typ), ids
        | ExIPat i -> Pat (IPat i, translateSomeType typ), ids
        | ExCPat c -> Pat (CPat c, translateSomeType typ), ids
        | ExXPat x -> 
            if ids.Contains x then
                raise <| ParseException (sprintf "The identifier %s is bound twice" x)
            else
                Pat (XPat x, translateSomeType typ), ids.Add x
        | ExTuplePat patterns ->
            let f pat (acc, pats) =
                let (newPat, acc') = findRepeats acc pat
                (acc', newPat :: pats)
            let (ids', pats) = List.foldBack f patterns (ids, [])
            Pat (TuplePat pats, translateSomeType typ), ids'
        | ExRecordPat (b, patterns) ->
            let f (s, pat) (acc, pats) =
                let (newPat, acc') = findRepeats acc pat
                (acc', (s, newPat) :: pats)
            let (ids', pats) = List.foldBack f patterns (ids, [])
            Pat (RecordPat (b, pats), translateSomeType typ), ids'
        | ExConsPat (p1, p2) ->
            let p1', ids' = findRepeats ids p1
            let p2', ids' = findRepeats ids' p2
            Pat (ConsPat (p1', p2'), translateSomeType typ), ids'
     
    let f pat (acc, pats) =
        let (newPat, acc') = findRepeats acc pat
        (acc', newPat :: pats)
    let (ids', pats) = List.foldBack f patterns (Set.empty, [])
    pats

let translatePattern pat = List.head <| translatePatterns [pat]

let condenseFunction name parameters retTerm retTyp =
    let f p (func, funcType: Type option) = 
        match p with
        | Pat(_, Some typ) when funcType.IsSome ->
            Fn(p, func), Some <| Function(typ, funcType.Value) 
        | Pat (_, _) ->
            Fn(p, func), None
    
    List.foldBack f parameters (retTerm, retTyp)

let rec condenseNamedFunction isRec id parameters retTyp retTerm =
    match parameters with
    | [] -> Pat(XPat id, retTyp), translate retTerm
    | head :: tail ->
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

and translateLib declarations =
    List.concat <| List.map translateDecl declarations

and translateDecl decl = 
    match decl with
    | DeclConst (p, t1) -> [(translatePattern p, translate t1)]
    | DeclFunc (isRec, id, parameters, retTyp, retTerm) ->
        [condenseNamedFunction isRec id (translatePatterns parameters) (translateSomeType retTyp) retTerm]
    | DeclImport (comps) -> comps

and translate term =
    match term with
    | ExB b -> B b
    | ExI i -> I i
    | ExC c -> C c
    | ExOP (t1, op, t2) -> OP(translate t1, op, translate t2)
    | ExCond (t1, t2, t3) -> Cond(translate t1, translate t2, translate t3)
    | ExX x -> X x
    | ExFn (pars, t) -> 
        fst <| condenseFunction None (translatePatterns pars) (translate t) None
    | ExRecFn (id, pars, typ, t) -> 
        snd <| condenseNamedFunction true id (translatePatterns pars) (translateSomeType typ) t
        
    | ExMatch (t1, patterns) -> 
        let f (p, cond, res) =
            match cond with
            | None -> (translatePattern p, None, translate res)
            | Some cond -> (translatePattern p, Some <| translate cond, translate res)
        Match(translate t1, List.map f patterns)

    | ExLet (decl, t2) ->
        let comps = translateDecl decl
        List.foldBack (fun (p, t) acc -> Let(p, t, acc)) comps <| translate t2
            
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
        let f = Fn (translatePattern p, translate retTerm)
        OP (OP (X "map", Application, f), Application, translate source)
       