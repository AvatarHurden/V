module Translation

open Definition

//#region Environment and Library

type TranslationEnv = 
    {idents: Map<Ident, Ident>
     nextSuffix: int
     typeAliases: Map<string, Type>}

    member this.generateSubstitutionFor (x: string) =
        let newX, newEnv = this.generateNewIdentAndAdd ()
        let newEnv = {newEnv with idents = newEnv.idents.Add (x, newX) }
        newX, newEnv

    member this.generateNewIdentAndAdd (x: unit) =
        let newIdent = "generated" + (string this.nextSuffix)
        let newEnv = {this with nextSuffix = this.nextSuffix + 1 }
        newIdent, newEnv
    
    member this.generateNewIdents (amount: int) =
        let f (ids, (accEnv: TranslationEnv)) x =
            let newIdent, newEnv = accEnv.generateNewIdentAndAdd ()
            newIdent :: ids, newEnv
        List.fold f ([], this) [1..amount]

    member this.addTypeAlias name typ =
        let aliases = this.typeAliases.Add (name, typ)
        {this with typeAliases = aliases}

let emptyTransEnv = {idents = Map.empty; nextSuffix = 0; typeAliases = Map.empty}

type Library =
    {terms: LibComponent list;
    translationEnv: TranslationEnv;
    operators: OperatorSpec list}

let emptyLib = {terms = []; operators = []; translationEnv = emptyTransEnv}

//#endregion

let rec translateType typ (env: TranslationEnv) =
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

let translateSomeType typ env = 
    match typ with
    | None -> None
    | Some typ -> Some <| translateType typ env

let translatePatterns patterns env =
    let rec findRepeats ((pattern, typ)) (ids: Set<Ident>) env =
        match pattern with
        | ExIgnorePat -> Pat (IgnorePat, translateSomeType typ env), ids, env
        | ExConstructorPat (c, patterns) -> 
            let f pat (pats, ids, env) =
                let (newPat, ids', env') = findRepeats pat ids env
                (newPat :: pats, ids', env')
            let (pats, ids', env') = List.foldBack f patterns ([], ids, env)
            Pat (ConstructorPat (c, pats), translateSomeType typ env), ids', env'
        | ExXPat x -> 
            if ids.Contains x then
                raise <| ParseException (sprintf "The identifier %s is bound twice" x)
            else
                let newX, env' = env.generateSubstitutionFor x
                Pat (XPat newX, translateSomeType typ env), ids.Add x, env'
        | ExRecordPat (b, patterns) ->
            let f (s, pat) (pats, ids, env) =
                let (newPat, ids', env') = findRepeats pat ids env
                ((s, newPat) :: pats, ids', env')
            let (pats, ids', env') = List.foldBack f patterns ([], ids, env)
            Pat (RecordPat (b, pats), translateSomeType typ env), ids', env'
        | ExListPat patterns ->
            let f pat (pats, ids, env) =
                let (newPat, ids', env') = findRepeats pat ids env
                (newPat :: pats, ids', env')
            let (pats, ids', env') = List.foldBack f patterns ([], ids, env)
            let foldF p acc = Pat (ConstructorPat (Cons, [p; acc]), translateSomeType typ env)
            List.foldBack foldF pats (Pat (ConstructorPat (Nil, []), translateSomeType typ env)), ids', env'

    let f pat (pats, ids, env) =
        let (newPat, ids', env') = findRepeats pat ids env
        (newPat :: pats, ids', env')
    let (patterns', _, env') = List.foldBack f patterns ([], Set.empty, env)
    patterns', env'

let translatePattern pat env = 
    let pats, env' = translatePatterns [pat] env
    List.head pats, env'

let rec getIdents pattern = 
    let (Pat (pattern, _)) = pattern
    match pattern with
    | XPat x -> [x]
    | IgnorePat -> []
    | ConstructorPat (c, arguments) -> List.concat <| List.map getIdents arguments
    | RecordPat (allowsExtras, patterns) -> 
        let _, patterns = List.unzip patterns
        List.concat <| List.map getIdents patterns
      
let transformToIdents parameters =
    let f par =
        match par with
        | Pat(XPat id, None) -> Some id
        | _ -> None

    mapOption f parameters

let rec condenseFunction (recName: Ident option) exParameters exRetTerm env =
    let parameters, env' = translatePatterns exParameters env

    let realParameters, retTerm, env' = 
        match transformToIdents parameters with
        | Some ids -> 
            //let env' = env.addIdents <| Set.ofList ids
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

and condenseNamedFunction isRec id parameters retTerm env =
    let fnTerm =
        if isRec then
            condenseFunction (Some id) parameters retTerm env
        else
            condenseFunction None parameters retTerm env
    
    Pat(XPat id, None), fnTerm

and translateDecl decl env = 
    match decl with
    | DeclConst (p, t1) -> 
        let p', env' = translatePattern p env
        let t1' = translateTerm t1 env
        [(p', t1')], env'
    | DeclFunc (isRec, id, parameters, retTyp, retTerm) ->
        let parameters', env' = translatePatterns parameters env
        let innerEnv = env'
        let typ' = translateSomeType retTyp innerEnv
        let pat, fn = condenseNamedFunction isRec id parameters retTerm innerEnv
        [(pat, fn)], innerEnv
    | DeclImport (comps) -> 
        let ids = comps |> List.unzip |> fst |> List.map getIdents |> List.concat
        comps, env
    | DeclAlias (s, typ) ->
        let env' = env.addTypeAlias s <| translateType typ env
        [], env'

and translateFn fn env =
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

and translateTerm term env =
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
            let p', env' = translatePattern p env
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