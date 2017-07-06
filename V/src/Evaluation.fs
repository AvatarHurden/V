module Evaluation

open Definition
open System

let private (|AnyRaise|_|) (t1, t2) =
    match t1, t2 with
    | ResRaise, _
    | _, ResRaise -> Some()
    | _ -> None

//#endregion

//#region Pattern Matching

let rec matchPattern (Pat (pattern, _)) result (env: Map<Ident, result>) =
    match pattern with
    | XPat x -> Some <| env.Add(x, result)
    | IgnorePat -> Some env 
    | ConstructorPat (c, arguments) ->
        match result with
        | ResConstructor (c', arguments') when c = c' && arguments.Length = arguments'.Length ->
            let f acc p r =
                match acc with
                | None -> None
                | Some env -> matchPattern p r env
            List.fold2 f (Some env) arguments arguments'
        | ResConstructor (c', arguments') when constructorsMatch c c' ->
            None
        | ResConstructor _ ->
            raise <| EvalException "Wrong constructor passed for constructor pattern"
        | _ -> 
            printf "hello world"
            raise <| EvalException "Non constructor passed for constructor pattern"
    | TuplePat patterns ->
        match result with
        | ResRaise -> None
        | ResTuple results when results.Length = patterns.Length ->
            let f acc p r =
                match acc with
                | None -> None
                | Some env -> matchPattern p r env
            List.fold2 f (Some env) patterns results
        | ResTuple results ->
            raise <| EvalException "Tuples do not match in pattern"
        | _ -> 
            raise <| EvalException "Invalid result for tuple pattern"
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
                    raise (EvalException <| sprintf "Record %A has less fields than pattern %A" result pattern)

            let f acc (pName, pValue) (rName, rValue) =
                if pName <> rName then
                    raise (EvalException <| sprintf "Record %A has different fields from pattern %A" result pattern)
                match acc with
                | None -> None
                | Some env -> matchPattern pValue rValue env
            List.fold2 f (Some env) patterns' results'
        | ResRecord results ->
            raise <| EvalException "Records have different lengths in pattern"
        | _ -> 
            raise <| EvalException "Invalid result for record pattern"

let validatePattern pattern result (env: Map<Ident, result>) =
    matchPattern pattern result env
        
//#endregion

//#region Comparisons

let rec compareEquality t1 t2 =
    match t1, t2 with
    | AnyRaise -> ResRaise
    | ResConstructor (c, arguments), ResConstructor (c', arguments') ->
        if not <| constructorsMatch c c' then
            sprintf "Cannot compare %A and %A" c c' |> EvalException |> raise  
        let f acc r1 r2 =
            match acc, compareEquality r1 r2 with
            | AnyRaise -> ResRaise
            | ResConstructor (B false, []), _ -> ResConstructor (B false, [])
            | ResConstructor (B true, []), ResConstructor (B b2, []) -> ResConstructor (B b2, [])
            | _ -> raise <| EvalException "Equal returned a non-expected value"
        List.fold2 f (ResConstructor (B (c = c'), [])) arguments arguments'
    | ResTuple v1, ResTuple v2 when v1.Length = v2.Length ->
        let f acc r1 r2 =
            match acc, compareEquality r1 r2 with
            | AnyRaise -> ResRaise
            | ResConstructor (B false, []), _ -> ResConstructor (B false, [])
            | ResConstructor (B true, []), ResConstructor (B b2, []) -> ResConstructor (B b2, [])
            | _ -> raise <| EvalException "Equal returned a non-expected value"
        List.fold2 f (ResConstructor (B true, [])) v1 v2
    | ResRecord v1, ResRecord v2 when v1.Length = v2.Length ->
        let v1' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) v1
        let v2' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) v2
        
        let f acc (n1, r1) (n2, r2) =
            if n1 <> n2 then
                raise <| EvalException (sprintf "Records %A and %A have different fields" t1 t2)
            match acc, compareEquality r1 r2 with
            | AnyRaise -> ResRaise
            | ResConstructor (B false, []), _ -> ResConstructor (B false, [])
            | ResConstructor (B true, []), ResConstructor (B b2, []) -> ResConstructor (B b2, [])
            | _ -> raise <| EvalException "Equal returned a non-expected value"
        List.fold2 f (ResConstructor (B true, [])) v1' v2'
    | _ , _ -> sprintf "Values %A and %A are not comparable" t1 t2 |> EvalException |> raise  

let rec compareOrder t1 t2 orderType =
    let func = 
        match orderType with
        | LessThan -> (<)
        | LessOrEqual -> (<=)
        | GreaterOrEqual -> (>=)
        | GreaterThan -> (>)
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> EvalException |> raise  
    match t1, t2 with
    | AnyRaise -> ResRaise
    | ResConstructor (c, arguments), ResConstructor (c', arguments') ->
        if not <| constructorsMatch c c' then
            sprintf "Cannot compare %A and %A" c c' |> EvalException |> raise  
        match c = c' with
        | false -> (ResConstructor (B (func c c'), []))
        | true ->
            let f (acc: result option) r1 r2 =
                match acc, compareEquality r1 r2 with
                | Some res, _ -> Some res
                | None, ResRaise -> Some ResRaise
                | None, ResConstructor (B true, []) -> None
                | None, ResConstructor (B false, []) -> Some <| compareOrder r1 r2 orderType
                | _ -> raise <| EvalException "Equal returned a non-expected value"
            match List.fold2 f None arguments arguments' with
            | Some res -> res
            | None ->
                match orderType with
                | GreaterOrEqual | LessOrEqual -> ResConstructor (B true, [])
                | GreaterThan | LessThan -> ResConstructor (B false, [])
                | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> EvalException |> raise  
    | _ , _ -> sprintf "Values %A and %A are not comparable" t1 t2 |> EvalException |> raise  
    
//#endregion

let rec private evalPartial b results term env =
    match b with
    | Add ->
        match results with
        | [] -> 
            let t1 = eval term env
            match t1 with
            | ResRaise -> ResRaise
            | t1 -> ResPartial (AppBuiltIn b, [t1])
        | [t1] ->
            let t2 = eval term env
            match t1, t2 with
            | AnyRaise -> ResRaise
            | ResConstructor (I i1, []), ResConstructor (I i2, []) -> ResConstructor (I (i1 + i2), [])
            | _, _ -> sprintf "Add requires numbers" |> EvalException |> raise
        | _ ->
            sprintf "Wrong number of arguments to add" |> EvalException |> raise
    | Subtract ->
        match results with
        | [] -> 
            let t1 = eval term env
            match t1 with
            | ResRaise -> ResRaise
            | t1 -> ResPartial (AppBuiltIn b, [t1])
        | [t1] ->
            let t2 = eval term env
            match t1, t2 with
            | AnyRaise -> ResRaise
            | ResConstructor (I i1, []), ResConstructor (I i2, []) -> ResConstructor (I (i1 - i2), [])
            | _, _ -> sprintf "Subtract requires numbers" |> EvalException |> raise
        | _ ->
            sprintf "Wrong number of arguments to subtract" |> EvalException |> raise
    | Multiply ->
        match results with
        | [] -> 
            let t1 = eval term env
            match t1 with
            | ResRaise -> ResRaise
            | t1 -> ResPartial (AppBuiltIn b, [t1])
        | [t1] ->
            let t2 = eval term env
            match t1, t2 with
            | AnyRaise -> ResRaise
            | ResConstructor (I i1, []), ResConstructor (I i2, []) -> ResConstructor (I (i1 * i2), [])
            | _, _ -> sprintf "Multiply requires numbers" |> EvalException |> raise
        | _ ->
            sprintf "Wrong number of arguments to multiply" |> EvalException |> raise
    | Divide ->
        match results with
        | [] -> 
            let t1 = eval term env
            match t1 with
            | ResRaise -> ResRaise
            | t1 -> ResPartial (AppBuiltIn b, [t1])
        | [t1] ->
            let t2 = eval term env
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
            let t1 = eval term env        
            match t1 with
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
        | [] -> 
            let t1 = eval term env
            match t1 with
            | ResRaise -> ResRaise
            | t1 -> ResPartial (AppBuiltIn b, [t1])
        | [t1] ->
            let t2 = eval term env
            compareOrder t1 t2 b
        | _ -> 
            sprintf "Wrong number of arguments to comparison" |> EvalException |> raise

    | Equal ->
        match results with
        | [] -> 
            let t1 = eval term env
            match t1 with
            | ResRaise -> ResRaise
            | t1 -> ResPartial (AppBuiltIn b, [t1])
        | [t1] ->
            let t2 = eval term env
            compareEquality t1 t2
        | _ -> 
            sprintf "Wrong number of arguments to equality" |> EvalException |> raise
    | Different ->
        match results with
        | [] -> 
            let t1 = eval term env
            match t1 with
            | ResRaise -> ResRaise
            | t1 -> ResPartial (AppBuiltIn b, [t1])
        | [t1] ->
            let t2 = eval term env
            match compareEquality t1 t2 with
            | ResRaise -> ResRaise
            | ResConstructor (B b, []) -> ResConstructor (B (not b), [])
            | _ -> raise <| EvalException "Equal returned a non-expected value"
        | _ -> 
            sprintf "Wrong number of arguments to inequality" |> EvalException |> raise
    | And ->
        match results with
        | [] -> 
            let t1 = eval term env
            match t1 with
            | ResRaise -> ResRaise
            | t1 -> ResPartial (AppBuiltIn b, [t1])
        | [t1] ->
            match t1 with
            | ResRaise -> ResRaise
            | ResConstructor (B false, []) -> ResConstructor (B false, [])
            | ResConstructor (B true, []) ->  eval term env
            | _ -> sprintf "And requires a boolean" |> EvalException |> raise
        | _ ->
            sprintf "Wrong number of arguments to and" |> EvalException |> raise
    | Or ->
        match results with
        | [] -> 
            let t1 = eval term env
            match t1 with
            | ResRaise -> ResRaise
            | t1 -> ResPartial (AppBuiltIn b, [t1])
        | [t1] ->
            match t1 with
            | ResRaise -> ResRaise
            | ResConstructor (B true, []) -> ResConstructor (B true, [])
            | ResConstructor (B false, []) ->  eval term env
            | _ -> sprintf "Or requires a boolean" |> EvalException |> raise
        | _ ->
            sprintf "Wrong number of arguments to Or" |> EvalException |> raise

    | Get ->
        match results with
        | [] -> 
            let t1 = eval term env
            match t1 with
            | ResRaise -> ResRaise
            | t1 -> ResPartial (AppBuiltIn b, [t1])
        | [t1] ->
            let t2 = eval term env
            match t1, t2 with
            | AnyRaise -> ResRaise
            | ResPartial (AppBuiltIn (RecordAccess s), []), ResRecord pairs ->
                let names, values = List.unzip pairs
                match Seq.tryFindIndex ((=) s) names with
                | Some i ->
                    Seq.nth i values
                | None ->
                    sprintf "Record has no entry %A at %A" s t2 |> EvalException |> raise
            | ResFn _, _ -> ResRaise
            | _, ResRecord _ -> sprintf "First argument of get is not a function" |> EvalException |> raise
            | _, _ -> sprintf "Second argument of get is not a record" |> EvalException |> raise
        | _ -> 
            sprintf "Wrong number of arguments to get" |> EvalException |> raise
    | RecordAccess s ->
        match results with
        | [] -> 
            let t1 = eval term env
            match t1 with
            | ResRaise -> ResRaise
            | t1 -> ResPartial (AppBuiltIn b, [t1])
        | [t1] ->
            let t2 = eval term env
            match t1, t2 with
            | AnyRaise -> ResRaise
            | t1, ResRecord pairs ->
                let names, values = List.unzip pairs
                match Seq.tryFindIndex ((=) s) names with
                | Some i ->
                    let start = Seq.take i values
                    let old = Seq.nth i values
                    let finish = Seq.skip (i+1) values
                    let newValueSeq = [t1] :> seq<_>
                    let newValues = Seq.toList (Seq.concat [start; newValueSeq; finish])
                    let newRec = ResRecord <| List.zip names newValues 
                    ResTuple [old; newRec]
                | None ->
                    sprintf "Record has no entry %A at %A" s t2 |> EvalException |> raise
            | _ -> sprintf "Second argument is not a record" |> EvalException |> raise
        | _ ->
            sprintf "Wrong number of arguments to record access" |> EvalException |> raise

and private eval t env =
    match t with
    | BuiltIn b -> ResPartial(AppBuiltIn b, [])
    | Constructor c -> 
        match constructorArgs c with
        | 0 -> ResConstructor (c, [])
        | _ -> ResPartial (AppConstructor c, [])
    | Fn fn -> ResFn (fn, env)
    | App (t1, t2) ->
        match eval t1 env with
        | ResRaise -> ResRaise
        | ResPartial(AppBuiltIn b, args) ->
            evalPartial b args t2 env
        | ResPartial(AppConstructor c, args) ->
            match eval t2 env with
            | ResRaise -> ResRaise
            | t2' ->
                if constructorArgs c = args.Length + 1 then
                    ResConstructor (c, args @ [t2'])
                else
                    ResPartial (AppConstructor c, args @ [t2'])
        | ResFn (fn, env') ->
            match fn with
            | Lambda (pattern, e) ->
                match eval t2 env with
                | ResRaise -> ResRaise
                | t2' -> 
                    match validatePattern pattern t2' env' with
                    | None -> ResRaise
                    | Some env' -> eval e env'
            | Recursive (id, _, pattern, e) ->
                match eval t2 env with
                | ResRaise -> ResRaise
                | t2' -> 
                    match validatePattern pattern t2' env' with
                    | None -> ResRaise
                    | Some env' -> eval e <| env'.Add(id, ResFn(fn, env'))
        | t1' -> sprintf "First operand %A is not a function at %A" t1' t |> EvalException |> raise
    
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
    | Tuple(terms) ->
        if List.length terms < 2 then
            sprintf "Tuple must have more than 2 components at %A" t |> EvalException |> raise
    
        let f t =
            match eval t env with
            | ResRaise -> None
            | t' -> Some t'

        match mapOption f terms with
        | None -> ResRaise
        | Some results -> ResTuple results

        //ResTuple <| List.map (fun t -> eval t env) terms
    | Record(pairs) ->
        if Set(List.unzip pairs |> fst).Count < List.length pairs then
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
        if env.ContainsKey id then
            env.[id]
        else
            sprintf "Could not find identifier %A" id |> EvalException |> raise


let evaluate t =
    eval t Map.empty
