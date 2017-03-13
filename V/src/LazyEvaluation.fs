module LazyEvaluation

open Definition

let searchEnv id (indexes: int list) (env: lazyEnv) =
    let indexList = List.mapi (fun i x -> (env.Length - i - 1, x)) env
    List.tryFindIndex (fun (i, (id', assoc)) -> id' = id && (List.exists ((=) i) indexes)) indexList

let remove indexes (env: lazyEnv) =
    let indexList = List.mapi (fun i x -> (env.Length - i - 1, x)) env
    let filtered = List.filter (fun (i, _) -> not <| List.exists ((=) i) indexes) indexList
    List.map (fun (_, x) -> x) filtered


let setValue partial n env =
    let f index (id, assoc) =
        if index = n then
            (id, Partial partial) 
        else 
            (id, assoc)
    List.mapi f env

let rec lazyMatchPattern (Var (pattern, _)) term (env: lazyEnv) indexes isRec  =
    match pattern with
    | XPattern x -> 
        let indexes' = if isRec then env.Length :: indexes else indexes
        Some <| (x, Thunk (term, indexes')) :: env, [env.Length]
    | IgnorePattern -> Some env, []
    | TuplePattern patterns ->
        match lazyEval term env indexes with
        | PartTuple (results, indexes'), env' when results.Length = patterns.Length ->
            let f acc p r =
                match acc with
                | None, _ -> acc
                | Some env', indexes' -> 
                    let env', addedIndexes = lazyMatchPattern p r env' indexes' isRec
                    env', addedIndexes @ indexes'
            let env', allIndexes = List.fold2 f (Some env', indexes') patterns results
            env', List.filter (fun index -> not <| List.exists ((=) index) indexes') allIndexes
        | PartTuple _, env ->
            raise <| EvalException "Tuples do not match in pattern"
        | _ -> 
            raise <| EvalException "Invalid result for tuple pattern"
    | RecordPattern patterns ->
        match lazyEval term env indexes with
        | PartRecord (results, indexes'), env' when results.Length = patterns.Length ->

            let existsInPatterns (rName, _) =
                List.exists (fun (pName, _) -> pName = rName) patterns

            if List.forall existsInPatterns results then
                let f acc (pName, pValue) =
                    match acc with
                    | None, _ -> acc
                    | Some env', indexes' ->
                        let (_, rValue) = List.find (fun (rName, rValue) -> rName = pName) results
                        let env', addedIndexes = lazyMatchPattern pValue rValue env' indexes' isRec
                        env', addedIndexes @ indexes'
                let env', allIndexes = List.fold f (Some env', indexes') patterns
                env', List.filter (fun index -> not <| List.exists ((=) index) indexes') allIndexes
            else
                raise <| EvalException "Records have different fields in pattern"
        | PartRecord _, env' ->
            raise <| EvalException "Records have different lengths in pattern"
        | _ -> 
            raise <| EvalException "Invalid result for record pattern"
    | NilPattern ->
        match lazyEval term env indexes with
        | PartNil, env' -> Some env, []
        | PartCons _, env' -> None, []
        | _ -> 
            raise <| EvalException "Invalid result for nil pattern"
    | ConsPattern (p1, p2) ->
        match lazyEval term env indexes with
        | PartNil, env' -> None, []
        | PartCons (v1, v2, internalIndexes), env' -> 
            match lazyMatchPattern p1 v1 env' internalIndexes isRec with
            | None, added -> None, added
            | Some env, added -> 
                let env', added' = lazyMatchPattern p2 v2 env (internalIndexes @ added) isRec
                env', added' @ added
        | _ -> 
            raise <| EvalException "Invalid result for cons pattern"

and lazyCompareEquality (t1, indexes1) (t2, indexes2) env =
    let v1, env = lazyEval t1 env indexes1
    let v2, env = lazyEval t2 env indexes2
    match v1, v2 with
    | PartRaise, _ -> PartRaise, env
    | _, PartRaise -> PartRaise, env
    | PartI i1, PartI i2 -> PartB (i1 = i2), env
    | PartC c1, PartC c2 -> PartB (c1 = c2), env
    | PartB b1, PartB b2 -> PartB (b1 = b2), env
    | PartNil, PartNil -> PartB true, env
    | PartCons _, PartNil -> PartB false, env
    | PartNil, PartCons _  -> PartB false, env
    | PartCons (hd1, tl1, indexes1), PartCons (hd2, tl2, indexes2) ->
        let v1, env = lazyCompareEquality (hd1, indexes1) (hd2, indexes2) env
        match v1 with
        | PartRaise -> PartRaise, env
        | PartB false -> PartB false, env
        | PartB true ->
            let v2, env = lazyCompareEquality (tl1, indexes1) (tl2, indexes2) env
            match v2 with
            | PartRaise -> PartRaise, env
            | PartB true -> PartB true, env
            | PartB false -> PartB false, env
            | _ -> raise <| EvalException "Equal returned a non-expected value"
        | _ -> raise <| EvalException "Equal returned a non-expected value"
    | PartTuple (v1, indexes1), PartTuple (v2, indexes2) when v1.Length = v2.Length ->
        let f (acc, env) r1 r2 =
            let v, env = lazyCompareEquality (r1, indexes1) (r2, indexes2) env
            match acc, v with
            | PartB false, _ -> PartB false, env
            | PartRaise, _
            | _, PartRaise -> PartRaise, env
            | PartB b1, PartB b2 -> PartB (b1 && b2), env
            | _ -> raise <| EvalException "Equal returned a non-expected value"
        List.fold2 f (PartB true, env) v1 v2
    | PartRecord (v1, indexes1), PartRecord (v2, indexes2) when v1.Length = v2.Length ->
        let v1' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) v1
        let v2' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) v2
        
        let f (acc, env) (n1, r1) (n2, r2) =
            if n1 <> n2 then
                raise <| EvalException (sprintf "Records %A and %A have different fields" t1 t2)
            let v, up = lazyCompareEquality (r1, indexes1) (r2, indexes2) env
            match acc, v with
            | PartB false, _ -> PartB false, up
            | PartRaise, _
            | _, PartRaise -> PartRaise, up
            | PartB b1, PartB b2 -> PartB (b1 && b2), up
            | _ -> raise <| EvalException "Equal returned a non-expected value"
        List.fold2 f (PartB true, env) v1' v2'
    | _ , _ -> sprintf "Values %A and %A are not comparable" t1 t2 |> EvalException |> raise  


and lazyCompareOrder (t1, indexes1) (t2, indexes2) orderType env =
    let v1, env = lazyEval t1 env indexes1
    let v2, env = lazyEval t2 env indexes2
    match v1, v2 with
    | PartRaise, _ -> PartRaise, env
    | _, PartRaise -> PartRaise, env
    | PartI i1, PartI i2 -> 
        match orderType with
        | LessThan -> PartB (i1 < i2), env
        | LessOrEqual -> PartB (i1 <= i2), env
        | GreaterOrEqual -> PartB (i1 >= i2), env
        | GreaterThan -> PartB (i1 > i2), env
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> EvalException |> raise  
    | PartC c1, PartC c2 -> 
        match orderType with
        | LessThan -> PartB (c1 < c2), env
        | LessOrEqual -> PartB (c1 <= c2), env
        | GreaterOrEqual -> PartB (c1 >= c2), env
        | GreaterThan -> PartB (c1 > c2), env
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> EvalException |> raise  
    | PartNil, PartNil ->
        match orderType with
        | LessOrEqual | GreaterOrEqual -> PartB true, env
        | LessThan | GreaterThan -> PartB false, env
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> EvalException |> raise  
    | PartCons _, PartNil ->
        match orderType with
        | GreaterOrEqual | GreaterThan -> PartB true, env
        | LessOrEqual | LessThan -> PartB false, env
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> EvalException |> raise  
    | PartNil, PartCons _ ->
        match orderType with
        | LessOrEqual | LessThan -> PartB true, env
        | GreaterOrEqual | GreaterThan -> PartB false, env
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> EvalException |> raise  
    | PartCons (hd1, tl1, indexes1), PartCons (hd2, tl2, indexes2) ->
        let v1, env = lazyCompareEquality (hd1, indexes1) (hd2, indexes2) env
        match v1 with
        | PartRaise -> PartRaise, env
        | PartB false -> lazyCompareOrder (hd1, indexes1) (hd2, indexes2) orderType env
        | PartB true -> lazyCompareOrder (tl1, indexes1) (tl2, indexes2) orderType env
        | _ -> raise <| EvalException "Equal returned a non-expected value"
    | _ , _ -> sprintf "Values %A and %A are not comparable" t1 t2 |> EvalException |> raise  

and lazyEval (term: term) env indexes: partial * lazyEnv =
    match term with
    | B b -> PartB b, env
    | I i -> PartI i, env
    | C c -> PartC c, env
    | Skip -> PartSkip, env
    | Raise -> PartRaise, env
    | Nil -> PartNil, env
    | OP (t1, Cons, t2) -> PartCons (t1, t2, indexes), env
    | Tuple terms -> PartTuple (terms, indexes), env
    | Record terms -> PartRecord (terms, indexes), env
    | Fn (pattern, t) -> PartClosure (pattern, t, indexes), env
    | RecFn (name, typ, pattern, t) -> 
        PartRecClosure (name, pattern, t, indexes), env
    | X id ->
        match searchEnv id indexes env with
        | None ->
            sprintf "Could not find identifier %A" id |> EvalException |> raise
        | Some index ->
            let (id', assoc) = env.Item index
            match assoc with
            | Partial p -> p, env
            | Thunk (t, start) ->
                let v, env' = lazyEval t env start
                v, setValue v index env'

    | IsEmpty t ->
        match lazyEval t env indexes with
        | PartRaise, env'
        | PartNil, env' -> PartB true, env'
        | PartCons _, env' -> PartB false, env'
        | t', _ -> sprintf "Term %A is not a list at %A" t' term |> EvalException |> raise
    | Head t ->
        match lazyEval t env indexes with
        | PartRaise, env'
        | PartNil, env' -> PartRaise, env'
        | PartCons (t1, t2, size), env' -> 
            lazyEval t1 env' size
        | t', _ -> sprintf "Term %A is not a list at %A" t' term |> EvalException |> raise
    | Tail t ->
        match lazyEval t env indexes with
        | PartRaise, env'
        | PartNil, env' -> PartRaise, env'
        | PartCons (t1, t2, size), env' -> 
            lazyEval t2 env' size
        | t', _ -> sprintf "Term %A is not a list at %A" t' term |> EvalException |> raise
    
    | Let (p, t1, t2) ->
        match lazyMatchPattern p t1 env indexes true with
        | Some env', added -> 
            let v, env'' = lazyEval t2 env' (indexes @ added)
            v, env''
        | None, added -> PartRaise, env

    | OP (t1, Application, t2) ->
        let v, env' = lazyEval t1 env indexes
        match v with
        | PartRaise -> PartRaise, env'
        | PartClosure (pattern, t1', indexes') ->
            match lazyMatchPattern pattern t2 env' indexes false with
            | None, added  -> PartRaise, env'
            | Some internEnv, added -> 
                let v, internEnv' = lazyEval t1' internEnv (indexes' @ added)
                v, internEnv'
        | PartRecClosure (f, pattern, t1', indexes') as t' ->
            match lazyMatchPattern pattern t2 env' indexes false with
            | None, _ -> PartRaise, env'
            | Some internEnv, added ->
//                let added' = internEnv.Length :: added
//                let internEnv' = (f, Partial <| PartRecClosure (f, pattern, t1', internEnv.Length :: indexes')) :: internEnv
                let v, internEnv' = lazyEval t1' internEnv (indexes' @ added)
                v, internEnv'
        | t1' -> sprintf "First operand %A is not a function at %A" t1' term |> EvalException |> raise

    | OP (t1, Equal, t2) ->
        lazyCompareEquality (t1, indexes) (t2, indexes) env
        
    | OP (t1, Different, t2) ->
        match lazyCompareEquality (t1, indexes) (t2, indexes) env with
        | PartRaise, env' -> PartRaise, env'
        | PartB b, env' -> PartB (not b), env'
        | _ -> raise <| EvalException "Equal returned a non-expected value"
    | OP (t1, (LessThan as op), t2)
    | OP (t1, (LessOrEqual as op), t2)
    | OP (t1, (GreaterOrEqual as op), t2)
    | OP (t1, (GreaterThan as op), t2) ->
        lazyCompareOrder (t1, indexes) (t2, indexes) op env

    | OP (t1, (Add as op), t2)
    | OP (t1, (Subtract as op), t2)
    | OP (t1, (Multiply as op), t2)
    | OP (t1, (Divide as op), t2) ->
        let v1, env' = lazyEval t1 env indexes
        let v2, env' = lazyEval t2 env' indexes
        match v1, v2 with
        | PartRaise , _ -> PartRaise, env'
        | _, PartRaise-> PartRaise, env'
        | PartI i1, PartI i2->
            match op with
            | Add -> PartI (i1 + i2), env'
            | Subtract -> PartI (i1 - i2), env'
            | Multiply -> PartI (i1 * i2), env'
            | Divide when i2 <> 0 -> PartI (i1 / i2), env'
            | Divide when i2 = 0 -> PartRaise, env'
            | _ -> sprintf "Term %A is not an operator at %A" op term |> EvalException |> raise
        | _, _ -> sprintf "Operation %A requires numbers at %A" op term |> EvalException |> raise
        
    | OP (t1, And, t2) ->
        let v1, env' = lazyEval t1 env indexes
        let v2, env' = lazyEval t2 env' indexes
        match v1, v2 with
        | PartRaise, _ -> PartRaise, env'
        | PartB false, _ -> PartB false, env'
        | PartB true, PartRaise -> PartRaise, env'
        | PartB true, PartB true -> PartB true, env'
        | PartB true, PartB false -> PartB false, env'
        | t1', t2' -> sprintf "AND operation requires boolean values at %A" term |> EvalException |> raise
    | OP (t1, Or, t2) ->
        let v1, env' = lazyEval t1 env indexes
        let v2, env' = lazyEval t2 env' indexes
        match v1, v2 with
        | PartRaise, _ -> PartRaise, env'
        | PartB true, _ -> PartB true, env'
        | PartB false, PartRaise -> PartRaise, env'
        | PartB false, PartB true -> PartB true, env'
        | PartB false, PartB false -> PartB false, env'
        | t1', t2' -> sprintf "OR operation requires boolean values at %A" term |> EvalException |> raise

    | OP (t1, Sequence, t2) ->
        match lazyEval t1 env indexes with
        | PartRaise, env' -> PartRaise, env'
        | PartSkip, env' -> lazyEval t2 env' indexes
        | t1', _ -> sprintf "First operand %A is not skip at %A" t1' term |> EvalException |> raise

    | Cond (t1, t2, t3) ->
        match lazyEval t1 env indexes with
        | PartRaise, env' -> PartRaise, env'
        | PartB true, env' -> lazyEval t2 env' indexes
        | PartB false, env' -> lazyEval t3 env' indexes
        | t1', _ -> sprintf "Term %A is not a Boolean at %A" t1' term |> EvalException |> raise

    | Try (t1, t2) ->
        match lazyEval t1 env indexes with
        | PartRaise, env' -> lazyEval t2 env' indexes
        | t1', env' -> t1', env'

    | ProjectIndex (n, t) ->
        match lazyEval t env indexes with
        | PartRaise, env' -> PartRaise, env'
        | PartTuple (terms, indexes'), env' ->
            if n >= 0 && n < terms.Length then
                lazyEval (List.nth terms n) env' indexes'
            else
                sprintf "Cannot acces index %A of tuple at %A" n term |> EvalException |> raise
        | t1', _ -> sprintf "Term %A is not a tuple at %A" t1' term |> EvalException |> raise
    | ProjectName (s, t) ->
        match lazyEval t env indexes with
        | PartRaise, env' -> PartRaise, env'
        | PartRecord (pairs, indexes'), env' ->
            let names, terms = List.unzip pairs
            match List.tryFindIndex ((=) s) names with
            | Some i ->
                lazyEval (List.nth terms i) env' indexes'
            | _ ->
                sprintf "Record has no entry %A at %A" s term |> EvalException |> raise
        | t1' -> sprintf "Term %A is not a record at %A" t1' term |> EvalException |> raise

    | Input
    | Output _ ->
        raise <| EvalException "IO is not supported in lazy evaluation"

let rec fullyEvaluate t env indexes =
    match lazyEval t env indexes with
    | PartB b, _ -> ResB b
    | PartSkip, _ -> ResSkip
    | PartI i, _ -> ResI i
    | PartC c, _ -> ResC c
    | PartRaise, _ -> ResRaise
    | PartNil, _ -> ResNil
    | PartCons (t1, t2, indexes'), env' ->
        match fullyEvaluate t1 env' indexes', fullyEvaluate t2 env' indexes' with
        | ResRaise, _ -> ResRaise
        | _, ResRaise -> ResRaise
        | r1, r2 -> ResCons(r1, r2)
    | PartClosure (p, term, _), _ -> ResClosure (p, term, Map.empty)
    | PartRecClosure (x, p, term, _), _ -> ResRecClosure (x, p, term, Map.empty)
    | PartTuple (terms, indexes'), env' ->
        let f t =
            match fullyEvaluate t env' indexes' with
            | ResRaise -> None
            | t' -> Some t'

        match mapOption f terms with
        | None -> ResRaise
        | Some results -> ResTuple results
    | PartRecord (pairs, indexes'), env' ->
        let f (name, t) =
            match fullyEvaluate t env' indexes' with
            | ResRaise -> None
            | t' -> Some (name, t')

        match mapOption f pairs with
        | None -> ResRaise
        | Some results -> ResRecord results

let lazyEvaluate t =
    fullyEvaluate t [] []
