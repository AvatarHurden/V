module Evaluation

open Definition

type private valueOption =
    | Values of term list
    | Raise
    | NonValue of term

let rec private evalSubterms terms env =
    let f acc x =
        match acc with
        | Values ls ->
            match eval x env with
            | Definition.Raise ->
                Raise
            | v when V(v) ->
                Values <| ls @ [v]
            | t -> 
                NonValue t
        | acc -> acc
    List.fold f (Values []) terms


and private eval t env =
    match t with
    | True -> 
        True
    | False -> 
        False
    | I(i) -> 
        I(i)
    | OP(t1, Application, t2) ->
        match evalSubterms [t1;t2] env with
        | Raise -> Definition.Raise
        | NonValue t' -> sprintf "Term %A is not a value at %A" t' t |> WrongExpression |> raise
        | Values [t1'; t2'] ->
        match t1' with
        | RecClosure(id1, id2, e, env') ->
                eval e <| env'.Add(id2, t2').Add(id1, t1')
        | Closure(id, e, env') ->
                eval e <| env'.Add(id, t2')
        | _ ->
            raise (WrongExpression(sprintf "First operand %A is not a function at %A" t1' t))
    | OP(t1, Cons, t2) ->
        match evalSubterms [t1;t2] env with
        | Raise -> Definition.Raise
        | NonValue t' -> sprintf "Term %A is not a value at %A" t' t |> WrongExpression |> raise
        | Values [t1'; t2'] ->
            match t2' with
            | OP(_, Cons, _) | Nil ->
                OP(t1', Cons, t2')
            | _ -> 
                raise (WrongExpression(sprintf "Term %A is not a list at %A" t2' t))
    | OP(t1, Equal, t2) ->
        match evalSubterms [t1;t2] env with
        | Raise -> Definition.Raise
        | NonValue t' -> sprintf "Term %A is not a value at %A" t' t |> WrongExpression |> raise
        | Values [t1'; t2'] ->
            match t1', t2' with
                | I i1, I i2 when i1 = i2 -> True
                | True, True -> True
                | False, False -> True
                | Nil, Nil -> True
                | OP (hd1, Cons, tl1), OP (hd2, Cons, tl2) ->
                    match evalSubterms [OP (hd1, Equal, hd2); OP (tl1, Equal, tl2)] env with
                    | Raise -> Definition.Raise
                    | NonValue t' -> sprintf "Term %A is not a value at %A" t' t |> WrongExpression |> raise
                    | Values [t1'; t2'] ->
                        match t1' with
                        | False -> False
                        | True -> t2'
                        | _ -> raise <| WrongExpression "Equal returned a non-expected value"    
                | _ -> False
    | OP(t1, Different, t2) ->
        let equals = eval (OP(t1, Equal, t2)) env
        match equals with
        | Definition.Raise -> Definition.Raise
        | True -> False
        | False -> True
        | _ -> raise <| WrongExpression "Equal returned a non-expected value"
    | OP(t1, (LessThan as op), t2)
    | OP(t1, (LessOrEqual as op), t2)
    | OP(t1, (GreaterOrEqual as op), t2)
    | OP(t1, (GreaterThan as op), t2) ->
        match evalSubterms [t1;t2] env with
        | Raise -> Definition.Raise
        | NonValue t' -> sprintf "Term %A is not a value at %A" t' t |> WrongExpression |> raise
        | Values [t1'; t2'] ->
            match t1', t2' with
            | I i1, I i2 ->
                match op with
                | LessThan -> if i1 < i2 then True else False
                | LessOrEqual -> if i1 <= i2 then True else False
                | GreaterOrEqual -> if i1 >= i2 then True else False
                | GreaterThan -> if i1 > i2 then True else False
            | Nil, Nil when op = LessOrEqual || op = GreaterOrEqual -> True
            | OP (hd1, Cons, tl1), OP (hd2, Cons, tl2) ->
                match evalSubterms [OP (hd1, Equal, hd2); OP (tl1, op, tl2)] env with
                | Raise -> Definition.Raise
                | NonValue t' -> sprintf "Term %A is not a value at %A" t' t |> WrongExpression |> raise
                | Values [t1'; t2'] ->
                    match t1' with
                    | False -> eval (OP(hd1, op, hd2)) env
                    | True -> t2'
                    | _ -> raise <| WrongExpression "Equal returned a non-expected value"    
            | OP _, Nil when op = GreaterThan || op = GreaterOrEqual -> True
            | Nil, OP _ when op = LessThan || op = LessOrEqual -> True
            | _ -> False
    | OP(t1, op, t2) ->
        match evalSubterms [t1;t2] env with
        | Raise -> Definition.Raise
        | NonValue t' -> sprintf "Term %A is not a value at %A" t' t |> WrongExpression |> raise
        | Values [t1'; t2'] ->
            match t1', t2' with
            | I n1, I n2 ->
                match op with
                | Add -> I(n1 + n2)
                | Subtract -> I(n1 - n2)
                | Multiply -> I(n1 * n2)
                | Divide when n2 <> 0 -> I(n1 / n2)
                | Divide when n2 = 0 -> Definition.Raise
                | _ -> sprintf "Term %A is not an operator at %A" op t |> WrongExpression |> raise
        | _ -> 
                sprintf "Operation %A requires numbers at %A" op t |> WrongExpression |> raise
    | Cond(t1, t2, t3) ->
        let t1' = eval t1 env
        match t1' with
        | Definition.Raise -> Definition.Raise
        | True -> eval t2 env
        | False -> eval t3 env
        | _ -> sprintf "Term %A is not a Boolean value at %A" t1' t |> WrongExpression |> raise
    | Fn(id, typ, t1) -> Closure(id, t1, env)
    | Let(id, typ, t1, t2) ->
        let t1' = eval t1 env
        match t1' with
        | Definition.Raise -> Definition.Raise
        | v when V(v) -> eval t2 <| env.Add(id, t1')
        | _ -> sprintf "Term %A is not a value at %A" t1' t |> WrongExpression |> raise
    | LetRec(id1, typ1, typ2, id2, t1, t2) ->
        let rec2 = LetRec(id1, typ1, typ2, id2, t1, t1)
        let fn = Fn(id2, typ1, rec2)
        eval t2 <| env.Add(id1, RecClosure(id1, id2, t1, env))
    | Nil -> Nil
    | IsEmpty(t1) ->
        let t1' = eval t1 env
        match t1' with
        | Nil -> True
        | OP(_, Cons, _) -> False
        | _ -> sprintf "Term %A is not a list at %A" t1' t |> WrongExpression |> raise
    | Head(t1) -> 
        let t1' = eval t1 env
        match t1' with
        | OP(head, Cons, tail) -> head
        | Nil -> Definition.Raise
        | _ -> sprintf "Term %A is not a list at %A" t1' t |> WrongExpression |> raise
    | Tail(t1) -> 
        let t1' = eval t1 env
        match t1' with
        | OP(head, Cons, tail) -> tail
        | Nil -> Definition.Raise
        | _ -> sprintf "Term %A is not a list at %A" t1' t |> WrongExpression |> raise
    | Definition.Raise -> Definition.Raise
    | Try(t1, t2) ->
        let t1' = eval t1 env
        match t1' with
        | Definition.Raise -> eval t2 env
        | _ -> t1'
    | X(id) -> 
        if env.ContainsKey id then
            env.[id]
        else
            sprintf "Could not find identifier %A" id |> WrongExpression |> raise
    | _ -> sprintf "%A is not a Term" t |> WrongExpression |> raise


let evaluate t =
    eval t Map.empty
