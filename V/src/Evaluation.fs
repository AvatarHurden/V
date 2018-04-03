module Evaluation

open Definition
open Printer

let private (|AnyRaise|_|) (t1, t2) =
    match t1, t2 with
    | ResRaise, _
    | _, ResRaise -> Some()
    | _ -> None

type Env with

    member this.areCompatible c1 c2 =
        match c1, c2 with
        | I _, I _ -> true
        | _, I _
        | I _, _ -> false
        | C _, C _ -> true
        | _, C _
        | C _, _ -> false
        | B _, B _ -> true
        | _, B _
        | B _, _ -> false
        | Tuple len1, Tuple len2 -> len1 = len2
        | c1, c2 ->
            let f x = fun (s: Constructor list) -> List.exists ((=) x) s
            match List.tryFind (f c1) this.groups with
            | None -> sprintf "Constructor %A is not in any group" (printConstructor c1) |> EvalException |> raise
            | Some s -> List.exists ((=) c2) s
    
    member this.compare c1 c2 op =
        let inline func a b = 
            match op with
            | LessThan -> a < b
            | LessOrEqual -> a <= b
            | GreaterOrEqual -> a >= b
            | GreaterThan -> a > b
            | Equal -> a = b
            | Different -> a <> b
            | _ -> sprintf "Cannot order %A and %A with %A" (printConstructor c1) (printConstructor c2) op |> EvalException |> raise  
        match c1, c2 with 
        | I i1, I i2 -> func i1 i2
        | C c1, C c2 -> func c1 c2
        | B b1, B b2 -> func b1 b2
        | Tuple len1, Tuple len2 when len1 = len2 -> func len1 len2        
        | c1, c2 ->
            if not <| this.areCompatible c1 c2 then
                sprintf "Cannot compare %A and %A" (printConstructor c1) (printConstructor c2) |> EvalException |> raise
            
            let f x = fun (s: Constructor list) -> List.exists ((=) x) s
            match List.tryFind (f c1) this.groups with
            | None -> sprintf "Constructor %A is not in any group" (printConstructor c1) |> EvalException |> raise
            | Some s -> 
                let i1 = List.findIndex ((=) c1) s
                let i2 = List.findIndex ((=) c2) s
                func i1 i2

    member this.numArgsFor c =
        match c with
        | I _ | B _ | C _ -> 0
        | Tuple len -> len
        | c -> 
            match this.numArgs.TryFind c with
            | None -> sprintf "Constructor %A does not have a number of arguments" (printConstructor c) |> EvalException |> raise
            | Some i -> i

    member this.addId id result =
        let newIds = this.ids.Add(id, result)
        {this with ids = newIds}

//#region Pattern Matching

let rec matchPattern (Pat (pattern, _)) result (env: Env) =
    match pattern with
    | XPat x -> Some <| env.addId x result
    | IgnorePat -> Some env 
    | ConstructorPat (c, arguments) ->
        match result with
        | ResConstructor (c', arguments') when c = c' && arguments.Length = arguments'.Length ->
            let f acc p r =
                match acc with
                | None -> None
                | Some env -> matchPattern p r env
            List.fold2 f (Some env) arguments arguments'
        | ResConstructor (c', arguments') when env.areCompatible c c' ->
            None
        | ResConstructor _ ->
            raise <| EvalException "Wrong constructor passed for constructor pattern"
        | _ -> 
            raise <| EvalException "Non constructor passed for constructor pattern"
    | RecordPat (allowsExtras, patterns) ->
        match result with
        | ResRaise -> None
        | ResRecord results when allowsExtras || results.Length = patterns.Length ->

            let results' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) results

            let patterns' =
                if not allowsExtras then
                    List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) patterns
                else if results.Length >= patterns.Length then
                    let dict = List.fold (fun (acc: Map<string, VarPattern>) (name, pat) -> acc.Add(name, pat)) Map.empty patterns
                    List.map (fun (name, value) -> name, match dict.TryFind name with None -> Pat(IgnorePat, None) | Some p -> p) results'
                else
                    raise (EvalException <| sprintf "Record %A has less fields than pattern %A" (printResult result) (printSemiPattern pattern))

            let f acc (pName, pValue) (rName, rValue) =
                if pName <> rName then
                    raise (EvalException <| sprintf "Record %A has different fields from pattern %A" (printResult result) (printSemiPattern pattern))
                match acc with
                | None -> None
                | Some env -> matchPattern pValue rValue env
            List.fold2 f (Some env) patterns' results'
        | ResRecord results ->
            raise <| EvalException "Records have different lengths in pattern"
        | _ -> 
            raise <| EvalException "Invalid result for record pattern"

let validatePattern pattern result (env: Env) =
    matchPattern pattern result env
        
//#endregion

//#region Comparisons

let rec compareEquality t1 t2 (env: Env) =
    match t1, t2 with
    | AnyRaise -> ResRaise
    | ResConstructor (c, arguments), ResConstructor (c', arguments') ->
        if not <| env.areCompatible c c' then
            sprintf "Cannot compare %A and %A" (printConstructor c) (printConstructor c') |> EvalException |> raise
        
        match env.compare c c' Equal with
        | false -> ResConstructor (B false, [])
        | true ->
            let f acc r1 r2 =
                match acc, compareEquality r1 r2 env with
                | AnyRaise -> ResRaise
                | ResConstructor (B false, []), _ -> ResConstructor (B false, [])
                | ResConstructor (B true, []), ResConstructor (B b2, []) -> ResConstructor (B b2, [])
                | _ -> raise <| EvalException "Equal returned a non-expected value"
            List.fold2 f (ResConstructor (B true, [])) arguments arguments'
    | ResRecord v1, ResRecord v2 when v1.Length = v2.Length ->
        let v1' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) v1
        let v2' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) v2
        
        let f acc (n1, r1) (n2, r2) =
            if n1 <> n2 then
                raise <| EvalException (sprintf "Records %A and %A have different fields" (printResult t1) (printResult t2))
            match acc, compareEquality r1 r2 env with
            | AnyRaise -> ResRaise
            | ResConstructor (B false, []), _ -> ResConstructor (B false, [])
            | ResConstructor (B true, []), ResConstructor (B b2, []) -> ResConstructor (B b2, [])
            | _ -> raise <| EvalException "Equal returned a non-expected value"
        List.fold2 f (ResConstructor (B true, [])) v1' v2'
    | _ , _ -> sprintf "Values %A and %A are not comparable" (printResult t1) (printResult t2) |> EvalException |> raise  

let rec compareOrder t1 t2 orderType (env: Env) =
    match t1, t2 with
    | AnyRaise -> ResRaise
    | ResConstructor (c, arguments), ResConstructor (c', arguments') ->
        if not <| env.areCompatible c c' then
            sprintf "Cannot compare %A and %A" (printConstructor c) (printConstructor c') |> EvalException |> raise  
        match env.compare c c' Equal with
        | false -> (ResConstructor (B (env.compare c c' orderType), []))
        | true ->
            let f (acc: result option) r1 r2 =
                match acc, compareEquality r1 r2 env with
                | Some res, _ -> Some res
                | None, ResRaise -> Some ResRaise
                | None, ResConstructor (B true, []) -> None
                | None, ResConstructor (B false, []) -> Some <| compareOrder r1 r2 orderType env
                | _ -> raise <| EvalException "Equal returned a non-expected value"
            match List.fold2 f None arguments arguments' with
            | Some res -> res
            | None ->
                match orderType with
                | GreaterOrEqual | LessOrEqual -> ResConstructor (B true, [])
                | GreaterThan | LessThan -> ResConstructor (B false, [])
                | _ -> sprintf "Cannot order %A and %A with %A" (printResult t1) (printResult t2) orderType |> EvalException |> raise  
    | _ , _ -> sprintf "Values %A and %A are not comparable" (printResult t1) (printResult t2) |> EvalException |> raise  
    
//#endregion

// Returns (result, result option),
// first result is old value of field
// second result is modified record
let rec traversePath (path: ResPath) term (newValue: result option) env =
    match term with
    | ResRecord pairs ->
        
        match path with
        | ResComponent s ->
            let names, values = List.unzip pairs
            match Seq.tryFindIndex ((=) s) names with
            | None -> sprintf "Record %A doesn't contain label %A" (printResult term) s |> EvalException |> raise
            | Some i ->
                let array = List.toArray values

                let old = Array.get array i
                    
                match newValue with
                | None -> 
                    old, term
                | Some value -> 
                    Array.set array i value

                    let newValues = List.ofArray array
                    let newRecord = ResRecord <| List.zip names newValues

                    old, newRecord
        | ResDistorted (path, getter, setter) ->
            //let newValue' =
                //match newValue with
                //| None -> None
                //| Some value -> Some <| applyResults setter value env

            let oldValue, _ = traversePath path term None env
            let oldValue' = applyResults getter oldValue env

            let newValue' = 
                match newValue with
                | None -> None
                | Some value -> 
                    let partial = applyResults setter value env
                    Some <| applyResults partial oldValue env

            let _, newRec = traversePath path term newValue' env

            oldValue', newRec

        | ResJoined paths ->
            match newValue with
            | None ->
                let values = List.map (fun p -> fst <| traversePath p term None env) paths
                let len = values.Length
                ResConstructor (Constructor.Tuple len, values), term
            | Some (ResConstructor (Constructor.Tuple len, oldValues)) when oldValues.Length = paths.Length ->
                let f = 
                    fun (oldValues, record) p value ->
                        let value, record' = traversePath p record (Some value) env
                        value :: oldValues, record'
                let newValues, record = List.fold2 f ([], term) paths oldValues
                let len = newValues.Length
                ResConstructor (Constructor.Tuple len, newValues), record
            | Some _ ->
                raise <| EvalException "joined paths must be set using a tuple"
        | ResStacked (p1, p2) ->
            let internalRecord, _ = traversePath p1 term None env
            let oldValue, internalRecord' = traversePath p2 internalRecord newValue env
            let _, newRecord = traversePath p1 term (Some internalRecord') env
            oldValue, newRecord

    | _ -> sprintf "Second argument is not a record" |> EvalException |> raise

and private evalPartial b results t2_thunk env =
    let t2 = 
        match b with
        | And | Or -> 
            match results with
            | [] -> t2_thunk ()
            | _ -> ResConstructor (I 0, [])
        | _ -> t2_thunk ()
    match t2 with
    | ResRaise -> ResRaise
    | t2 -> 
        match b with
        | Id -> 
            match results with
            | [] -> t2
            | _ ->
                sprintf "Wrong number of arguments to Id" |> EvalException |> raise
        
        | Add ->
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] ->
                match t1, t2 with
                | AnyRaise -> ResRaise
                | ResConstructor (I i1, []), ResConstructor (I i2, []) -> ResConstructor (I (i1 + i2), [])
                | _, _ -> sprintf "Add requires numbers" |> EvalException |> raise
            | _ ->
                sprintf "Wrong number of arguments to add" |> EvalException |> raise
        | Subtract ->
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] ->
                match t1, t2 with
                | AnyRaise -> ResRaise
                | ResConstructor (I i1, []), ResConstructor (I i2, []) -> ResConstructor (I (i1 - i2), [])
                | _, _ -> sprintf "Subtract requires numbers" |> EvalException |> raise
            | _ ->
                sprintf "Wrong number of arguments to subtract" |> EvalException |> raise
        | Multiply ->
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] ->
                match t1, t2 with
                | AnyRaise -> ResRaise
                | ResConstructor (I i1, []), ResConstructor (I i2, []) -> ResConstructor (I (i1 * i2), [])
                | _, _ -> sprintf "Multiply requires numbers" |> EvalException |> raise
            | _ ->
                sprintf "Wrong number of arguments to multiply" |> EvalException |> raise
        | Divide ->
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] ->
                match t1, t2 with
                | AnyRaise -> ResRaise
                | ResConstructor (I i, []), ResConstructor (I 0, []) -> ResRaise
                | ResConstructor (I i1, []), ResConstructor (I i2, []) -> ResConstructor (I (i1 / i2), [])
                | _, _ -> sprintf "Divide requires numbers" |> EvalException |> raise
            | _ ->
                sprintf "Wrong number of arguments to divide" |> EvalException |> raise
        | Negate ->
            match results with
            | [] -> 
                match t2 with
                | ResRaise -> ResRaise
                | ResConstructor (I i, []) -> ResConstructor (I (-i), [])
                | _ -> sprintf "Negate requires a number" |> EvalException |> raise
            | _ ->
                sprintf "Wrong number of arguments to negate" |> EvalException |> raise
    
        | LessThan 
        | LessOrEqual 
        | GreaterThan 
        | GreaterOrEqual ->
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] ->
                compareOrder t1 t2 b env
            | _ -> 
                sprintf "Wrong number of arguments to comparison" |> EvalException |> raise

        | Equal ->
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] ->
                compareEquality t1 t2 env
            | _ -> 
                sprintf "Wrong number of arguments to equality" |> EvalException |> raise
        | Different ->
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] ->
                match compareEquality t1 t2 env with
                | ResRaise -> ResRaise
                | ResConstructor (B b, []) -> ResConstructor (B (not b), [])
                | _ -> raise <| EvalException "Equal returned a non-expected value"
            | _ -> 
                sprintf "Wrong number of arguments to inequality" |> EvalException |> raise
        | And ->
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] ->
                match t1 with
                | ResRaise -> ResRaise
                | ResConstructor (B false, []) -> ResConstructor (B false, [])
                | ResConstructor (B true, []) -> t2_thunk ()
                | _ -> sprintf "And requires a boolean" |> EvalException |> raise
            | _ ->
                sprintf "Wrong number of arguments to and" |> EvalException |> raise
        | Or ->
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] ->
                match t1 with
                | ResRaise -> ResRaise
                | ResConstructor (B true, []) -> ResConstructor (B true, [])
                | ResConstructor (B false, []) -> t2_thunk ()
                | _ -> sprintf "Or requires a boolean" |> EvalException |> raise
            | _ ->
                sprintf "Wrong number of arguments to Or" |> EvalException |> raise

        | Stack ->
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] ->
                match t1, t2 with
                | AnyRaise -> ResRaise
                | ResRecordAcess path, ResRecordAcess path2 ->
                    ResRecordAcess <| ResStacked (path, path2)
                | _ -> sprintf "Stack needs a pair of record accessors" |> EvalException |> raise
            | _ -> 
                sprintf "Wrong number of arguments to stack" |> EvalException |> raise
        | Distort ->
            let t3 = t2
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] -> ResPartial (AppBuiltIn b, [t1; t2])
            | [t1; t2] ->
                match t1, t2, t3 with
                | ResRaise, _, _ -> ResRaise
                | _, ResRaise, _ -> ResRaise
                | _, _, ResRaise -> ResRaise
                | ResRecordAcess path, getter, setter ->
                    ResRecordAcess <| ResDistorted (path, getter, setter)
                | _ -> sprintf "Compose needs a pair of record accessors" |> EvalException |> raise
            | _ -> 
                sprintf "Wrong number of arguments to compose" |> EvalException |> raise
        | Get ->
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] ->
                match t1, t2 with
                | AnyRaise -> ResRaise
                | ResRecordAcess paths, t2 ->
                    fst <| traversePath paths t2 None env
                | ResFn _, _ -> ResRaise
                | _ -> sprintf "First argument of get is not a function" |> EvalException |> raise
            | _ -> 
                sprintf "Wrong number of arguments to get" |> EvalException |> raise
        | Set ->
            let t3 = t2
            match results with
            | [] -> ResPartial (AppBuiltIn b, [t2])
            | [t1] -> ResPartial (AppBuiltIn b, [t1; t2])
            | [t1; t2] ->
                match t1, t2, t3 with
                | ResRaise, _, _ -> ResRaise
                | _, ResRaise, _ -> ResRaise
                | _, _, ResRaise -> ResRaise
                | ResRecordAcess paths, value, record ->
                    snd <| traversePath paths record (Some value) env
                | ResFn _, _, _ -> ResRaise
                | _ -> sprintf "First argument of set is not a function" |> EvalException |> raise
            | _ -> 
                sprintf "Wrong number of arguments to set" |> EvalException |> raise

and private applyResults fn res env =
    match fn with
    | ResRaise -> ResRaise
    | ResPartial(AppBuiltIn b, args) ->
        match res with
        | ResRaise -> ResRaise
        | _ -> evalPartial b args (fun _ -> res) env
    | ResPartial(AppConstructor c, args) ->
        match res with
        | ResRaise -> ResRaise
        | t2' ->
            if env.numArgsFor c = args.Length + 1 then
                ResConstructor (c, args @ [t2'])
            else
                ResPartial (AppConstructor c, args @ [t2'])
    | ResFn (fn, env') ->
        let env', arg, e = 
            match fn with
            | Lambda (arg, e) -> env', arg, e
            | Recursive (id, _, arg, e) -> 
                env'.addId id (ResFn(fn, env')), arg, e
        match res with
        | ResRaise -> ResRaise
        | t2' -> eval e <| env'.addId arg t2'
    | t1' -> sprintf "First operand %A is not a function" (printResult t1') |> EvalException |> raise

and private apply fn t2 (env: Env) =
    match fn with
    | ResRaise -> ResRaise
    | ResPartial(AppBuiltIn b, args) ->
        evalPartial b args (fun _ -> eval t2 env) env
    | ResPartial(AppConstructor c, args) ->
        match eval t2 env with
        | ResRaise -> ResRaise
        | t2' ->
            if env.numArgsFor c = args.Length + 1 then
                ResConstructor (c, args @ [t2'])
            else
                ResPartial (AppConstructor c, args @ [t2'])
    | ResFn (fn, env') ->
        let env', arg, e = 
            match fn with
            | Lambda (arg, e) -> env', arg, e
            | Recursive (id, _, arg, e) -> 
                env'.addId id (ResFn(fn, env')), arg, e
        match eval t2 env with
        | ResRaise -> ResRaise
        | t2' -> eval e <| env'.addId arg t2'
    | t1' -> sprintf "First operand %A is not a function" (printResult t1') |> EvalException |> raise

and private eval (t: term) (env: Env) =
    match t with
    | BuiltIn b -> ResPartial(AppBuiltIn b, [])
    | Constructor c -> 
        match env.numArgsFor c with
        | 0 -> ResConstructor (c, [])
        | _ -> ResPartial (AppConstructor c, [])
    | RecordAccess path ->
        let rec f = 
            function
            | Component s -> ResComponent s
            //| Distorted (p, getter, setter) -> ResDistorted (f p, eval getter env, eval setter env)
            //| Stacked (p1, p2) -> ResStacked (f p1, f p2)
            | Joined paths -> 
                let reduce p =
                    match eval p env with
                    | ResRecordAcess p -> p
                    | t' -> sprintf "%A is not a record access at joined record access %A" (printResult t') t |> EvalException |> raise
                ResJoined <| List.map reduce paths
        ResRecordAcess <| f path
    | Fn fn -> ResFn (fn, env)
    | App (t1, t2) ->
        apply (eval t1 env) t2 env
    | Match (t1, patterns) ->
        match eval t1 env with
        | t1' ->
            let f acc (pattern, condition, result) =
                match acc with
                | Some x -> Some x
                | None ->
                    match validatePattern pattern t1' env with
                    | None -> None
                    | Some env' ->
                        match condition with
                        | None -> Some <| eval result env'
                        | Some cond ->
                            match eval cond env' with
                            | ResRaise -> Some ResRaise
                            | ResConstructor (B true, []) -> Some <| eval result env'
                            | ResConstructor (B false, []) -> None
                            | _ -> sprintf "Match condition %A returned a non-boolean at %A" cond t |> EvalException |> raise
            match List.fold f None patterns with
            | None -> ResRaise
            | Some v -> v
    | Let(pattern, t1, t2) ->
        match eval t1 env with
        | ResRaise -> ResRaise
        | t1' -> 
            match validatePattern pattern t1' env with
            | None -> ResRaise
            | Some env' -> eval t2 env'
    | Raise -> ResRaise
    | Record(pairs) ->
        if Collections.Set(List.unzip pairs |> fst).Count < List.length pairs then
            sprintf "Record has duplicate fields at %A" t |> EvalException |> raise
        
        let f (name, t) =
            match eval t env with
            | ResRaise -> None
            | t' -> Some (name, t')

        match mapOption f pairs with
        | None -> ResRaise
        | Some results -> ResRecord results

        //ResRecord <| List.map (fun (name, t) -> name, eval t env) pairs
    | X(id) -> 
        match env.ids.TryFind id with
        | None -> sprintf "Could not find identifier %A" id |> EvalException |> raise
        | Some r -> r            


let evaluate t =
    eval t defaultEnv
