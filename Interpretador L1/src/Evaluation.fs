module Evaluation

open Definition
open System

let rec private toString term =
    match term with
    | ResCons (ResC c, t2) -> (string c) + (toString t2)
    | t -> "" 

let rec private fromString string =
    match string with
    | c::rest -> ResCons (ResC c, fromString rest)
    | [] -> ResNil

and compareEquality t1 t2 =
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
        | ResB false, _ -> ResB false
        | ResB true, ResB false -> ResB false
        | ResB true, ResB true -> ResB true
        | _ -> raise <| WrongExpression "Equal returned a non-expected value"
    | ResTuple v1, ResTuple v2 when v1.Length = v2.Length ->
        let f acc r1 r2 =
            match acc, compareEquality r1 r2 with
            | ResRaise, _
            | _, ResRaise -> ResRaise
            | ResB b1, ResB b2 -> ResB (b1 && b2)
            | _ -> raise <| WrongExpression "Equal returned a non-expected value"
        List.fold2 f (ResB true) v1 v2
    | ResRecord v1, ResRecord v2 when v1.Length = v2.Length ->
        let existsInV1 (name2, _) =
            List.exists (fun (name1, _) -> name2 = name1) v1
        
        if List.forall existsInV1 v2 then
            let f acc (name1, r1) =
                let (name2, r2) = List.find (fun (name2, typ2) -> name1 = name2) v2
                match acc, compareEquality r1 r2 with
                | ResRaise, _
                | _, ResRaise -> ResRaise
                | ResB b1, ResB b2 -> ResB (b1 && b2)
                | _ -> raise <| WrongExpression "Equal returned a non-expected value"
            List.fold f (ResB true) v1
        else
            raise <| WrongExpression (sprintf "Records %A and %A have different fields" t1 t2)
    | _ , _ -> sprintf "Values %A and %A are not comparable" t1 t2 |> WrongExpression |> raise  

and compareOrder t1 t2 orderType =
    match t1, t2 with
    | ResRaise, _ -> ResRaise
    | _, ResRaise -> ResRaise
    | ResI i1, ResI i2 -> 
        match orderType with
        | LessThan -> ResB (i1 < i2)
        | LessOrEqual -> ResB (i1 <= i2)
        | GreaterOrEqual -> ResB (i1 >= i2)
        | GreaterThan -> ResB (i1 > i2)
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> WrongExpression |> raise  
    | ResC c1, ResC c2 -> 
        match orderType with
        | LessThan -> ResB (c1 < c2)
        | LessOrEqual -> ResB (c1 <= c2)
        | GreaterOrEqual -> ResB (c1 >= c2)
        | GreaterThan -> ResB (c1 > c2)
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> WrongExpression |> raise  
    | ResNil, ResNil ->
        match orderType with
        | LessOrEqual | GreaterOrEqual -> ResB true
        | LessThan | GreaterThan -> ResB false
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> WrongExpression |> raise  
    | ResCons (hd1, tl1), ResNil ->
        match orderType with
        | GreaterOrEqual | GreaterThan -> ResB true
        | LessOrEqual | LessThan -> ResB false
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> WrongExpression |> raise  
    | ResNil, ResCons (hd1, tl1) ->
        match orderType with
        | LessOrEqual | LessThan -> ResB true
        | GreaterOrEqual | GreaterThan -> ResB false
        | _ -> sprintf "Cannot order %A and %A with %A" t1 t2 orderType |> WrongExpression |> raise  
    | ResCons (hd1, tl1), ResCons (hd2, tl2) ->
        match compareEquality hd1 hd2, compareOrder tl1 tl2 orderType with
        | ResB true, t2' -> t2'
        | ResB false, _ -> compareOrder hd1 hd2 orderType
        | _ -> raise <| WrongExpression "Equal returned a non-expected value"
    | _ , _ -> sprintf "Values %A and %A are not comparable" t1 t2 |> WrongExpression |> raise  

and private eval t env =
    match t with
    | B b-> ResB b
    | Skip -> ResSkip
    | I i -> ResI i
    | C c -> ResC c
    | OP(t1, Application, t2) ->
        match eval t1 env with
        | ResRaise -> ResRaise
        | ResRecClosure(id1, id2, e, env') as t1' ->
            match eval t2 env with
            | ResRaise ->  ResRaise
            | t2' -> eval e <| env'.Add(id2, t2').Add(id1, t1')
        | ResClosure(id, e, env') ->
            match eval t2 env with
            | ResRaise -> ResRaise
            | t2' -> eval e <| env'.Add(id, t2')
        | t1' -> sprintf "First operand %A is not a function at %A" t1' t |> WrongExpression |> raise
    | OP(t1, Cons, t2) ->
        match eval t1 env with
        | ResRaise -> ResRaise
        | t1' ->
            match eval t2 env with
            | ResRaise -> ResRaise
            | ResCons(_, _) as t2' -> ResCons(t1', t2')
            | ResNil -> ResCons(t1', ResNil)
            | t2' -> sprintf "Term %A is not a list at %A" t2' t |> WrongExpression |> raise
    | OP(t1, Sequence, t2) ->
        match eval t1 env with
        | ResRaise -> ResRaise
        | ResSkip -> eval t2 env
        | t1' -> sprintf "First operand %A is not skip at %A" t1' t |> WrongExpression |> raise
    | OP(t1, Equal, t2) ->
        compareEquality (eval t1 env) (eval t2 env)
    | OP(t1, Different, t2) ->
        let equals = compareEquality (eval t1 env) (eval t2 env)
        match equals with
        | ResRaise -> ResRaise
        | ResB b -> ResB (not b)
        | _ -> raise <| WrongExpression "Equal returned a non-expected value"
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
            | _ -> sprintf "Term %A is not an operator at %A" op t |> WrongExpression |> raise
        | _, _ -> sprintf "Operation %A requires numbers at %A" op t |> WrongExpression |> raise
    | OP(t1, And, t2) ->
        match eval t1 env, eval t2 env with
        | ResRaise, _ -> ResRaise
        | ResB false, _ -> ResB false
        | ResB true, ResRaise -> ResRaise
        | ResB true, ResB true -> ResB true
        | ResB true, ResB false -> ResB false
        | t1', t2' -> sprintf "AND operation requires boolean values at %A" t |> WrongExpression |> raise
    | OP(t1, Or, t2) ->
        match eval t1 env, eval t2 env with
        | ResRaise, _ -> ResRaise
        | ResB true, _ -> ResB true
        | ResB false, ResRaise -> ResRaise
        | ResB false, ResB true -> ResB true
        | ResB false, ResB false -> ResB false
        | t1', t2' -> sprintf "OR operation requires boolean values at %A" t |> WrongExpression |> raise
    | Cond(t1, t2, t3) ->
        match eval t1 env with
        | ResRaise -> ResRaise
        | ResB true -> eval t2 env
        | ResB false -> eval t3 env
        | t1' -> sprintf "Term %A is not a Boolean value at %A" t1' t |> WrongExpression |> raise
    | Fn(id, typ, t1) -> ResClosure(id, t1, env)
    | RecFn(id1, typ1, id2, typ2, t) -> ResRecClosure(id1, id2, t, env)
    | Let(id, typ, t1, t2) ->
        match eval t1 env with
        | ResRaise -> ResRaise
        | t1' -> eval t2 <| env.Add(id, t1')
    | Nil -> ResNil
    | IsEmpty(t1) ->
        match eval t1 env with
        | ResRaise -> ResRaise
        | ResNil -> ResB true
        | ResCons (_, _) -> ResB false
        | t1' -> sprintf "Term %A is not a list at %A" t1' t |> WrongExpression |> raise
    | Head(t1) -> 
        match eval t1 env with
        | ResRaise -> ResRaise
        | ResCons (head, tail) -> head
        | ResNil -> ResRaise
        | t1' -> sprintf "Term %A is not a list at %A" t1' t |> WrongExpression |> raise
    | Tail(t1) -> 
        match eval t1 env with
        | ResRaise -> ResRaise
        | ResCons (head, tail) -> tail
        | ResNil -> ResRaise
        | t1' -> sprintf "Term %A is not a list at %A" t1' t |> WrongExpression |> raise
    | Raise -> ResRaise
    | Try(t1, t2) ->
        match eval t1 env with
        | ResRaise -> eval t2 env
        | t1' -> t1'
    | Input ->
        Console.ReadLine().ToCharArray() |> Array.toList |> fromString
    | Output(t1) ->
        match eval t1 env with
        | ResRaise -> ResRaise
        | ResCons (ResC c, t) as t1' -> printf "%s" <| toString t1'; ResSkip
        | ResNil -> printfn ""; ResSkip
        | t1' -> sprintf "Term %A is not a string at %A" t1' t |> WrongExpression |> raise
    | Tuple(terms) ->
        if List.length terms < 2 then
            sprintf "Tuple must have more than 2 components at %A" t |> WrongExpression |> raise
    
        let f t =
            match eval t env with
            | ResRaise -> None
            | t' -> Some t'

        match mapOption f terms with
        | None -> ResRaise
        | Some results -> ResTuple results
    | Record(pairs) ->
        if Set(List.unzip pairs |> fst).Count < List.length pairs then
            sprintf "Record has duplicate fields at %A" t |> WrongExpression |> raise

        let f (name, t) =
            match eval t env with
            | ResRaise -> None
            | t' -> Some (name, t')

        match mapOption f pairs with
        | None -> ResRaise
        | Some results -> ResRecord results
    | ProjectIndex(n, t1) ->
        match eval t1 env with
        | ResRaise -> ResRaise
        | ResTuple values ->
            if n >= 0 && n < List.length values then
                List.nth values n
            else
                sprintf "Cannot acces index %A of tuple at %A" n t |> WrongExpression |> raise
        | t1' -> sprintf "Term %A is not a tuple at %A" t1' t |> WrongExpression |> raise
    | ProjectName(s, t1) ->
        match eval t1 env with
        | ResRaise -> ResRaise
        | ResRecord pairs ->
            let names, values = List.unzip pairs
            match Seq.tryFindIndex ((=) s) names with
            | Some i ->
                Seq.nth i values
            | None ->
                sprintf "Record has no entry %A at %A" s t |> WrongExpression |> raise
        | t1' -> sprintf "Term %A is not a record at %A" t1' t |> WrongExpression |> raise
    | X(id) -> 
        if env.ContainsKey id then
            env.[id]
        else
            sprintf "Could not find identifier %A" id |> WrongExpression |> raise


let evaluate t =
    eval t Map.empty
