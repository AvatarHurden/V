module Translation

open Definition

//#region Environment and Library

type TranslationEnv = 
    {idents: Set<Ident>
     lastUsedSuffix: int
     typeAliases: Map<string, Type>}

    member this.generateNewIdentAndAdd (x: unit) =
        let baseName = "generated"
        let mutable suffix = this.lastUsedSuffix
        while this.idents.Contains <| baseName + (string suffix) do
            suffix <- suffix + 1
        let newIdent = baseName + (string suffix)
        let newEnv = {this with lastUsedSuffix = suffix; 
                                idents = this.idents.Add newIdent}
        newIdent, newEnv
    
    member this.generateNewIdents (amount: int) =
        let f (ids, (accEnv: TranslationEnv)) x =
            let newIdent, newEnv = accEnv.generateNewIdentAndAdd ()
            newIdent :: ids, newEnv
        List.fold f ([], this) [1..amount]

    member this.addIdents idents =
        let idents' = Set.union this.idents idents
        {this with idents = idents'}

    member this.addTypeAlias name typ =
        let aliases = this.typeAliases.Add (name, typ)
        {this with typeAliases = aliases}

let emptyTransEnv = {idents = Set.empty; lastUsedSuffix = 0; typeAliases = Map.empty}

type Library =
    {terms: LibComponent list;
    translationEnv: TranslationEnv;
    operators: OperatorSpec list}

let emptyLib = {terms = []; operators = []; translationEnv = emptyTransEnv}

//#endregion

let rec private translateType typ (env: TranslationEnv) =
    match typ with
    | ExVarType (s, traits) -> VarType (s, traits)
    | ExConstType (c, types) -> ConstType (c, List.map (fun t -> translateType t env) types)
    | ExFunction (t1, t2) -> Function (translateType t1 env, translateType t2 env)
    | ExAccessor (t1, t2) -> Accessor (translateType t1 env, translateType t2 env)
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
        | ExConstructorPat (c, patterns) -> 
            let f pat (acc, pats) =
                let (newPat, acc') = findRepeats acc pat
                (acc', newPat :: pats)
            let (ids', pats) = List.foldBack f patterns (ids, [])
            Pat (ConstructorPat (c, pats), translateSomeType typ env), ids'
        | ExXPat x -> 
            if ids.Contains x then
                raise <| ParseException (sprintf "The identifier %s is bound twice" x)
            else
                Pat (XPat x, translateSomeType typ env), ids.Add x
        | ExRecordPat (b, patterns) ->
            let f (s, pat) (acc, pats) =
                let (newPat, acc') = findRepeats acc pat
                (acc', (s, newPat) :: pats)
            let (ids', pats) = List.foldBack f patterns (ids, [])
            Pat (RecordPat (b, pats), translateSomeType typ env), ids'
        | ExListPat patterns ->
            let f pat (acc, pats) =
                let (newPat, acc') = findRepeats acc pat
                (acc', newPat :: pats)
            let (ids', pats) = List.foldBack f patterns (ids, [])
            List.foldBack (fun p acc -> Pat (ConstructorPat (Cons, [p; acc]), None)) pats (Pat (ConstructorPat (Nil, []), None)), ids'
     
    let f pat (acc, pats) =
        let (newPat, acc') = findRepeats acc pat
        (acc', newPat :: pats)
    List.foldBack f patterns (Set.empty, [])

let private translatePattern pat env = 
    let ids, pats = translatePatterns [pat] env
    ids, List.head pats

let rec private getIdents pattern = 
    let (Pat (pattern, _)) = pattern
    match pattern with
    | XPat x -> [x]
    | IgnorePat -> []
    | ConstructorPat (c, arguments) -> List.concat <| List.map getIdents arguments
    | RecordPat (allowsExtras, patterns) -> 
        let _, patterns = List.unzip patterns
        List.concat <| List.map getIdents patterns
      
let private transformToIdents parameters =
    let f par =
        match par with
        | Pat(XPat id, None) -> Some id
        | _ -> None

    mapOption f parameters

let rec private condenseFunction (recName: Ident option) exParameters exRetTerm env =
    let ids, parameters = translatePatterns exParameters env

    let realParameters, retTerm, env' = 
        match transformToIdents parameters with
        | Some ids -> 
            let env' = env.addIdents <| Set.ofList ids
            ids, translateTerm exRetTerm env', env'
        | None -> 
            let size = parameters.Length
            let ids, env' = env.generateNewIdents size
            let matchPattern = 
                match exParameters with
                | [x] -> x
                | xs -> (ExConstructorPat (Tuple size, exParameters), None)
            let matchReturn = translateTerm exRetTerm env'
            let matchCase = matchPattern, None, exRetTerm
            let realExRetTerm = 
                match ids with
                | [x] -> ExMatch (ExX x, [matchCase]) 
                | xs -> ExMatch (ExTuple (List.map ExX xs), [matchCase])

            ids, translateTerm realExRetTerm env', env'

    match realParameters with
    | [] -> 
        retTerm
    | first :: parameters' ->
        let f p func = Fn <| Lambda(p, func)
    
        let innerFn = List.foldBack f parameters' retTerm

        let finalFn = 
            match recName with
            | Some name -> Fn <| Recursive(name, None, first, innerFn)
            | None -> Fn <| Lambda(first, innerFn)

        finalFn

and private condenseNamedFunction isRec id parameters retTerm env =
    let fnTerm =
        if isRec then
            condenseFunction (Some id) parameters retTerm env
        else
            condenseFunction None parameters retTerm env
    
    Pat(XPat id, None), fnTerm

and private translateDecl decl env = 
    match decl with
    | DeclConst (p, t1) -> 
        let ids, p' = translatePattern p env
        let t1' = translateTerm t1 env
        [(p', t1')], env.addIdents ids
    | DeclFunc (isRec, id, parameters, retTyp, retTerm) ->
        let ids, parameters' = translatePatterns parameters env
        let innerEnv = env.addIdents <| Set.ofList [id]
        let typ' = translateSomeType retTyp innerEnv
        let pat, fn = condenseNamedFunction isRec id parameters retTerm innerEnv
        [(pat, fn)], innerEnv
    | DeclImport (comps) -> 
        let ids = comps |> List.unzip |> fst |> List.map getIdents |> List.concat
        comps, env.addIdents <| Set.ofList ids
    | DeclAlias (s, typ) ->
        let env' = env.addTypeAlias s <| translateType typ env
        [], env'

and private translateFn fn env =
    match fn with
    | ExLambda (pars, t) -> 
        let ids, pars' = translatePatterns pars env
        let t' = translateTerm t env
        let fn = condenseFunction None pars t env
        fn
    | ExRecursive (id, pars, typ, t) -> 
        let ids, pars' = translatePatterns pars env
        let typ' = translateSomeType typ env
        let t' = translateTerm t env
        let fn = condenseFunction (Some id) pars t env
        fn

and private translateTerm term env =
    match term with
    | ExBuiltIn b -> BuiltIn b
    | ExConstructor c -> Constructor c
    | ExX x -> X x
    | ExRecordAccess path ->
        let rec f = 
            function
            | ExComponent s -> Component s
            //| ExDistorted (p, getter, setter) ->
            //    Distorted (f p, translateTerm getter env, translateTerm setter env)
            //| ExStacked (p1, p2) ->
            //    Stacked (f p1, f p2)
            | ExJoined [x] as p ->
                sprintf "Joined accessor %A must have at least 2 terms at %A" p term 
                    |> ParseException |> raise
            | ExJoined paths ->
                Joined <| List.map (flip translateTerm env) paths
        RecordAccess <| f path
    | ExFn fn -> translateFn fn env
    | ExApp (t1, t2) ->
        App(translateTerm t1 env, translateTerm t2 env)
        
    | ExMatch (t1, patterns) -> 
        let f (p, cond, res) =
            let ids, p' = translatePattern p env
            let env' = env.addIdents ids
            match cond with
            | None -> 
                let res' = translateTerm res env'
                (p', None, res')
            | Some cond ->
                let cond' = translateTerm cond env'
                let res' = translateTerm res env'
                (p', Some cond', res')
        let t1' = translateTerm t1 env
        Match(t1', List.map f patterns)

    | ExLet (decl, t2) ->
        let comps, env' = translateDecl decl env
        let t2' = translateTerm t2 env'
        List.foldBack (fun (p, t) acc -> Let(p, t, acc)) comps t2'
            
    | ExListTerm l ->
        List.foldBack (fun x acc -> App (App (Constructor Cons, translateTerm x env), acc)) l (Constructor Nil)

    | ExRaise -> Raise
    | ExTuple terms -> 
        let f = (fun acc x -> App (acc, translateTerm x env))
        List.fold f (Constructor (Tuple terms.Length)) terms
    | ExRecord pairs -> 
        Record <| List.map (fun (s, t) -> (s, translateTerm t env)) pairs
    | Cond (t1, t2, t3) -> 
        let t1' = translateTerm t1 env
        let t2' = translateTerm t2 env
        let t3' = translateTerm t3 env
        Match(t1', 
            [Pat(ConstructorPat (B true, []), None), None, t2'; 
             Pat(ConstructorPat (B false, []), None), None, t3'])
    | Range (first, second, last) ->
        let first' = translateTerm first env
        let last' = translateTerm last env
        let increment =
            match second with
            | None -> Constructor <| I 1
            | Some second -> 
                let second' = translateTerm second env
                App (App (BuiltIn Subtract, second'), first')
        App (App (App (X "range", first'), last'), increment)
    | Comprehension (retTerm, p, source) ->
        let fn = condenseFunction None [p] retTerm env
        App (App (X "map", fn), translateTerm source env)
       
let translateLib declarations env =
    let f (comps, env) decl =
        let newComps, env' = translateDecl decl env
        comps @ newComps, env'
    List.fold f ([], env) declarations

let translate term env =
    translateTerm term env