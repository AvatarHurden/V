module Translation

open Definition

//#region Environment and Library

type TranslationEnv = 
    {idents: Map<Ident, Ident>
     nextSuffix: int
     nextTypeSuffix: int
     typeAliases: Map<string, Type>}

    member this.generateSubstitutionFor (x: string) =
        let newX, newEnv = this.generateNewIdent ()
        let newEnv = {newEnv with idents = newEnv.idents.Add (x, newX) }
        newX, newEnv

    member this.generateNewIdent (x: unit) =
        let newIdent = "generated" + (string this.nextSuffix)
        let newEnv = {this with nextSuffix = this.nextSuffix + 1 }
        newIdent, newEnv
    
    member this.generateNewIdents (amount: int) =
        let f (ids, (accEnv: TranslationEnv)) x =
            let newIdent, newEnv = accEnv.generateNewIdent ()
            newIdent :: ids, newEnv
        List.fold f ([], this) [1..amount]
        
    member this.generateNewVarType (x: unit) =
        let replacement = "type" + (string this.nextTypeSuffix)
        let newEnv = {this with nextTypeSuffix = this.nextTypeSuffix + 1}
        ExVarType(replacement, []), newEnv
    
    member this.typePattern (pat: ExVarPattern) : ExVarPattern * TranslationEnv =
        match pat with
        | (p, None) ->
            let typ, env' = this.generateNewVarType ()
            (p, Some typ), env'
        | pat -> pat, this
        
    member this.typePatterns pats =
        let f pat (pats, (env: TranslationEnv))=
            let pat', env' = env.typePattern pat
            pat' :: pats, env'
        List.foldBack f pats ([], this) 
        
    member this.addTypeAlias name typ =
        let aliases = this.typeAliases.Add (name, typ)
        {this with typeAliases = aliases}
        
let emptyTransEnv = 
    {idents = Map.empty; 
     nextSuffix = 0; 
     nextTypeSuffix = 0; 
     typeAliases = Map.empty}

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
      
let rec transformToIdents parameters =
    let f par =
        match par with
        | Pat(XPat id, None) -> Some id
        | _ -> None

    mapOption f parameters
    
and translateDecl decl env = 
    match decl with
    | DeclConst (p, t1) -> 
        let p', env' = translatePattern p env
        let t1' = translateTerm t1 env
        [(p', t1')], env'
    | DeclFunc (isRec, id, parameters, retTyp, retTerm) ->
        match retTyp with
        | None -> 
            let fn =
                match isRec with
                | true -> ExRecursive (id, parameters, None, retTerm)
                | false -> ExLambda (parameters, retTerm)
            let id', env' = env.generateSubstitutionFor id
            let fn' = translateFn fn env'
            [Pat (XPat id', None), fn'], env'
        | Some typ ->
            let parameters', env' = env.typePatterns parameters
            let f (pat: ExVarPattern) retTyp =
                match pat with
                | (p, Some typ) -> ExFunction (typ, retTyp)
                | _ -> sprintf "%A was misstyped" pat |> ParseException |> raise
            let retTyp' = List.foldBack f parameters' typ
            let fn =
                match isRec with
                | true -> ExRecursive (id, parameters', retTyp, retTerm)
                | false -> ExLambda (parameters', retTerm)
            let id', env' = env'.generateSubstitutionFor id
            let fn' = translateFn fn env'
            [Pat (XPat id', Some <| translateType retTyp' env'), fn'], env'
    | DeclImport (comps) -> 
        let ids = comps |> List.unzip |> fst |> List.map getIdents |> List.concat
        comps, env
    | DeclAlias (s, typ) ->
        let env' = env.addTypeAlias s <| translateType typ env
        [], env'

and translateFn fn env =

    let (|Identifiers|_|) patterns =
        let f (p: VarPattern) = match p with | Pat (XPat x, None) -> Some x | _ -> None
        mapOption f patterns

    let composeResult patterns ret env =
        match patterns with
        | Identifiers ids -> 
            let matchRes = translateTerm ret env
            ids, matchRes
        | _ -> 
            let arguments, env' = env.generateNewIdents patterns.Length
            let matchRes = translateTerm ret env'
            match patterns with 
            | [pat] -> arguments, Match (X arguments.Head, [pat, None, matchRes])
            | pars' ->
                let matchPattern = Pat (ConstructorPat (Tuple arguments.Length, pars'), None)
                let matchArg = List.fold (fun acc x -> App (acc, X x)) (Constructor (Tuple arguments.Length)) arguments
                arguments, Match (matchArg, [matchPattern, None, matchRes])
    
    match fn with
    | ExLambda (patterns, t) ->
        let patterns', env' = translatePatterns patterns env
        
        let arguments, result = composeResult patterns' t env'
           
        List.foldBack (fun x partial -> Fn <| Lambda(x, partial)) arguments result
    | ExRecursive (id, patterns, typ, t) -> 
        let patterns', env' = translatePatterns patterns env
        let id', env' = env'.generateSubstitutionFor id
        
        let arguments, result = composeResult patterns' t env'
        
        match arguments with
        | head :: tail ->
            let body = List.foldBack (fun x partial -> Fn <| Lambda(x, partial)) tail result
            Fn <| Recursive (id', translateSomeType typ env', head, body)
        | _ ->
            raise <| ParseException (sprintf "Function %A must have at least one argument" fn)

and translateTerm term env =
    match term with
    | ExBuiltIn b -> BuiltIn b
    | ExConstructor c -> Constructor c
    | ExX x -> 
        match env.idents.TryFind x with
        | Some x' -> X x'
        | None -> 
            raise <| ParseException (sprintf "Identifier %A was not declared" x)
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
        let fn = translateFn (ExLambda ([p], retTerm)) env
        App (App (X "map", fn), translateTerm source env)
       
let translateLib declarations env =
    let f (comps, env) decl =
        let newComps, env' = translateDecl decl env
        comps @ newComps, env'
    List.fold f ([], env) declarations

let translate term env =
    translateTerm term env