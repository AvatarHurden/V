module Evaluation

open Definition
open System

//#region String Conversion

let rec private toString term =
    match term with
    | ResCons (ResC c, t2) -> (string c) + (toString t2)
    | t -> "" 

let rec private fromString string =
    match string with
    | c::rest -> ResCons (ResC c, fromString rest)
    | [] -> ResNil

//#endregion

//#region Pattern Matching

let rec matchPattern (Pat (pattern, _)) result (env: Map<Ident, result>) =
    match pattern with
    | XPat x -> Some <| env.Add(x, result)
    | IgnorePat -> Some env  
    | BPat b ->
        match result with
        | ResRaise -> None
        | ResB b' when b' = b -> Some env
        | ResB _ -> None
        | _ -> raise <| EvalException "Boolean does not match in pattern"
    | IPat i ->
        match result with
        | ResRaise -> None
        | ResI i' when i' = i -> Some env
        | ResI _ -> None
        | _ -> raise <| EvalException "Integer does not match in pattern"
    | CPat c ->
        match result with
        | ResRaise -> None
        | ResC c' when c' = c -> Some env
        | ResC _ -> None
        | _ -> raise <| EvalException "Integer does not match in pattern"
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
    | NilPat ->
        match result with
        | ResRaise -> None
        | ResNil -> Some env
        | ResCons _ -> None
        | _ -> 
            raise <| EvalException "Invalid result for nil pattern"
    | ConsPat (p1, p2) ->
        match result with
        | ResRaise -> None
        | ResNil -> None
        | ResCons (v1, v2) -> 
            match matchPattern p1 v1 env with
            | None -> None
            | Some env -> matchPattern p2 v2 env
        | _ -> 
            raise <| EvalException "Invalid result for cons pattern"

let validatePattern pattern result (env: Map<Ident, result>) =
    matchPattern pattern result env
        
//#endregion

//#region Comparisons

let rec compareEquality t1 t2 =
    match t1, t2 with
    | ResRaise, _ -> ResRaise
    | _, ResRaise -> ResRaise
    | ResI i1, ResI i2 -> ResB (i1 = i2)
    | ResC c1, ResC c2 -> ResB (c1 = c2)
    | ResB b1, ResB b2 -> ResB (b1 = b2)
    | ResNil, ResNil -> ResB true
    | ResCons (hd1, tl1), ResNil -> ResB false
    | ResNil, ResCons (hd1, tl1)  -> ResB false
    | ResCons (hd1, tl1), ResCons (hd2, tl2) ->
        match compareEquality hd1 hd2, compareEquality tl1 tl2 with
        | ResRaise, _ -> ResRaise
        | ResB false, _ -> ResB false
        | ResB true, ResB false -> ResB false
        | ResB true, ResB true -> ResB true
        | ResB true, ResRaise -> ResRaise
        | _ -> raise <| EvalException "Equal returned a non-expected value"
    | ResTuple v1, ResTuple v2 when v1.Length = v2.Length ->
        let f acc r1 r2 =
            match acc, compareEquality r1 r2 with
            | ResRaise, _ -> ResRaise
            | ResB false, _ -> ResB false
            | ResB true, ResRaise -> ResRaise
            | ResB true, ResB b2 -> ResB b2
            | _ -> raise <| EvalException "Equal returned a non-expected value"
        List.fold2 f (ResB true) v1 v2
    | ResRecord v1, ResRecord v2 when v1.Length = v2.Length ->
        let v1' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) v1
        let v2' = List.sortWith (fun (s1, t1) (s2, t2) -> compare s1 s2) v2
        
        let f acc (n1, r1) (n2, r2) =
            if n1 <> n2 then
                raise <| EvalException (sprintf "Records %A and %A have different fields" t1 t2)
            match acc, compareEquality r1 r2 with
            | ResRaise, _ -> ResRaise
            | ResB false, _ -> ResB false
            | ResB true, ResRaise -> ResRaise
            | ResB true, ResB b2 -> ResB b2
            | _ -> raise <| EvalException "Equal returned a non-expected value"
        List.fold2 f (ResB true) v1' v2'
    | _ , _ -> sprintf "Values %A and %A are not comparable" t1 t2 |> EvalException |> raise  

let rec compareOrder t1 t2 orderType =
    match t1, t2 with
    | ResRaise, _ -> ResRaise
    | _, ResRaise -> ResRaise
    | ResI i1, ResI i2 -> 
        match orderType with
        | LessThan -> ResB (i1 < i2)
        | LessOrEqual -> ResB (i1 <= i2)
        | GreaterOrEqual -> ResB (i1 >= i2)
        | GreaterThan -> ResB (i1 > i2)
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> EvalException |> raise  
    | ResC c1, ResC c2 -> 
        match orderType with
        | LessThan -> ResB (c1 < c2)
        | LessOrEqual -> ResB (c1 <= c2)
        | GreaterOrEqual -> ResB (c1 >= c2)
        | GreaterThan -> ResB (c1 > c2)
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> EvalException |> raise  
    | ResNil, ResNil ->
        match orderType with
        | LessOrEqual | GreaterOrEqual -> ResB true
        | LessThan | GreaterThan -> ResB false
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> EvalException |> raise  
    | ResCons (hd1, tl1), ResNil ->
        match orderType with
        | GreaterOrEqual | GreaterThan -> ResB true
        | LessOrEqual | LessThan -> ResB false
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> EvalException |> raise  
    | ResNil, ResCons (hd1, tl1) ->
        match orderType with
        | LessOrEqual | LessThan -> ResB true
        | GreaterOrEqual | GreaterThan -> ResB false
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> EvalException |> raise  
    | ResCons (hd1, tl1), ResCons (hd2, tl2) ->
        match compareEquality hd1 hd2, compareOrder tl1 tl2 orderType with
        | ResRaise, _ -> ResRaise
        | ResB true, t2' -> t2'
        | ResB false, _ -> compareOrder hd1 hd2 orderType
        | _ -> raise <| EvalException "Equal returned a non-expected value"
    | _ , _ -> sprintf "Values %A and %A are not comparable" t1 t2 |> EvalException |> raise  
    
//#endregion

let rec private evalPartial b (args: term list) env =
    match b with
    | Get ->
        match args with
        | [t1; t2] ->
            let t1' = eval t1 env
            let t2' = eval t2 env
            match t1', t2' with
            | ResPartial ((RecordAccess2 s), []), ResRecord pairs ->
                let names, values = List.unzip pairs
                match Seq.tryFindIndex ((=) s) names with
                | Some i ->
                    Seq.nth i values
                | None ->
                    sprintf "Record has no entry %A at %A" s (args.Item 1) |> EvalException |> raise
            | _ -> sprintf "Wrong arguments" |> EvalException |> raise
        | _ -> 
            sprintf "Wrong arguments" |> EvalException |> raise
    | RecordAccess2 s ->
        match args with
        | [t1; t2] ->
            let t1' = eval t1 env
            let t2' = eval t2 env
            match t1', t2' with
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
                    sprintf "Record has no entry %A at %A" s (args.Item 1) |> EvalException |> raise
            | _ -> sprintf "Second argument is not a record" |> EvalException |> raise
        | _ ->
            sprintf "Wrong number of arguments to record access" |> EvalException |> raise

and private eval t env =
    match t with
    | Built b -> ResPartial(b, [])
    | B b-> ResB b
    | I i -> ResI i
    | C c -> ResC c
    | OP(t1, Application, t2) ->
        match eval t1 env with
        | ResRaise -> ResRaise
        | ResPartial(b, args) ->
            let args' = args @ [t2]
            if args'.Length = numArgs b then
                evalPartial b args' env
            else
                ResPartial(b, args')
        | ResRecClosure(id1, pattern, e, env') as t1' ->
            match eval t2 env with
            | t2' -> 
                match validatePattern pattern t2' env' with
                | None -> ResRaise
                | Some env' -> eval e <| env'.Add(id1, t1')
        | ResClosure(pattern, e, env') ->
            match eval t2 env with
            | t2' -> 
                match validatePattern pattern t2' env' with
                | None -> ResRaise
                | Some env' -> eval e env'
        | t1' -> sprintf "First operand %A is not a function at %A" t1' t |> EvalException |> raise
    | OP(t1, Cons, t2) ->
        match eval t1 env with
        | t1' ->
            match eval t2 env with
            | ResRaise -> ResRaise
            | ResCons(_, _) as t2' -> ResCons(t1', t2')
            | ResNil -> ResCons(t1', ResNil)
            | t2' -> sprintf "Term %A is not a list at %A" t2' t |> EvalException |> raise
    | OP(t1, Equal, t2) ->
        compareEquality (eval t1 env) (eval t2 env)
    | OP(t1, Different, t2) ->
        let equals = compareEquality (eval t1 env) (eval t2 env)
        match equals with
        | ResRaise -> ResRaise
        | ResB b -> ResB (not b)
        | _ -> raise <| EvalException "Equal returned a non-expected value"
    | OP(t1, (LessThan as op), t2)
    | OP(t1, (LessOrEqual as op), t2)
    | OP(t1, (GreaterOrEqual as op), t2)
    | OP(t1, (GreaterThan as op), t2) ->
        compareOrder (eval t1 env) (eval t2 env) op
    | OP(t1, (Add as op), t2)
    | OP(t1, (Subtract as op), t2)
    | OP(t1, (Multiply as op), t2)
    | OP(t1, (Divide as op), t2) ->
        match eval t1 env, eval t2 env with
        | ResRaise, _ -> ResRaise
        | _, ResRaise -> ResRaise
        | ResI i1, ResI i2 ->
            match op with
            | Add -> ResI (i1 + i2)
            | Subtract -> ResI (i1 - i2)
            | Multiply -> ResI (i1 * i2)
            | Divide when i2 <> 0 -> ResI (i1 / i2)
            | Divide when i2 = 0 -> ResRaise
            | _ -> sprintf "Term %A is not an operator at %A" op t |> EvalException |> raise
        | _, _ -> sprintf "Operation %A requires numbers at %A" op t |> EvalException |> raise
    | Fn(pattern, t1) -> ResClosure(pattern, t1, env)
    | RecFn(id1, typ1, pattern, t) -> ResRecClosure(id1, pattern, t, env)
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
                            | ResB true -> Some <| eval result env'
                            | ResB false -> None
                            | _ -> sprintf "Match condition %A returned a non-boolean at %A" cond t |> EvalException |> raise
            match List.fold f None patterns with
            | None -> ResRaise
            | Some v -> v
    | Let(pattern, t1, t2) ->
        match eval t1 env with
        | t1' -> 
            match validatePattern pattern t1' env with
            | None -> ResRaise
            | Some env' -> eval t2 env'
    | Nil -> ResNil
    | Raise -> ResRaise
    | Tuple(terms) ->
        if List.length terms < 2 then
            sprintf "Tuple must have more than 2 components at %A" t |> EvalException |> raise
    
        ResTuple <| List.map (fun t -> eval t env) terms
    | Record(pairs) ->
        if Set(List.unzip pairs |> fst).Count < List.length pairs then
            sprintf "Record has duplicate fields at %A" t |> EvalException |> raise

        ResRecord <| List.map (fun (name, t) -> name, eval t env) pairs
    | RecordAccess (s, t1, t2) ->
        let newValue = eval t1 env
        match eval t2 env with
        | ResRaise -> ResRaise
        | ResRecord pairs ->
            let names, values = List.unzip pairs
            match Seq.tryFindIndex ((=) s) names with
            | Some i ->
                let start = Seq.take i values
                let old = Seq.nth i values
                let finish = Seq.skip (i+1) values
                let newValueSeq = [newValue] :> seq<_>
                let newValues = Seq.toList (Seq.concat [start; newValueSeq; finish])
                let newRec = ResRecord <| List.zip names newValues 
                ResTuple [old; newRec]
            | None ->
                sprintf "Record has no entry %A at %A" s t2 |> EvalException |> raise
        | t2' -> sprintf "Term %A is not a record at %A" t2' t |> EvalException |> raise
    | X(id) -> 
        if env.ContainsKey id then
            env.[id]
        else
            sprintf "Could not find identifier %A" id |> EvalException |> raise


let evaluate t =
    eval t Map.empty
