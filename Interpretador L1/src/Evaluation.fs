module Evaluation

open Definition

let rec private eval t env =
    match t with
    | True -> 
        ResTrue
    | False -> 
        ResFalse
    | I i -> 
         ResI i
    | OP(t1, Application, t2) ->
        let t1' = eval t1 env
        match t1' with
        | ResRaise -> 
            ResRaise
        | ResRecClosure(id1, id2, e, env') ->
            let t2' = eval t2 env
            match t2' with
            | ResRaise -> 
                ResRaise
            | v -> 
                eval e <| env'.Add(id2, t2').Add(id1, t1')
        | ResClosure(id, e, env') ->
            let t2' = eval t2 env
            match t2' with
            | ResRaise -> 
                ResRaise
            | v -> 
                eval e <| env'.Add(id, t2')
        | _ ->
            raise (WrongExpression(sprintf "First operand %A is not a function at %A" t1' t))
    | OP(t1, Cons, t2) ->
        let t1' = eval t1 env
        match t1' with
        | ResRaise -> 
            ResRaise
        | v ->
            let t2' = eval t2 env
            match t2' with
            | ResCons(_, _) as v2 -> 
                ResCons(v, v2)
            | ResNil -> 
                 ResCons(v, ResNil)
            | _ -> 
                raise (WrongExpression(sprintf "Term %A is not a list at %A" t2' t))
    | OP(t1, op, t2) ->
        let t1' = eval t1 env
        match t1' with
        | ResRaise ->
            ResRaise
        | ResI n1 ->
            let t2' = eval t2 env
            match t2' with
            | ResRaise ->
                ResRaise
            | ResI n2 ->
                match op with
                | Add -> ResI(n1 + n2)
                | Subtract -> ResI(n1 - n2)
                | Multiply -> ResI(n1 * n2)
                | Divide when n2 <> 0 -> ResI(n1 / n2)
                | Divide when n2 = 0 -> ResRaise
                | LessThan -> if n1 < n2 then ResTrue else ResFalse
                | LessOrEqual -> if n1 <= n2 then ResTrue else ResFalse
                | Equal -> if n1 = n2 then ResTrue else ResFalse
                | Different -> if n1 <> n2 then ResTrue else ResFalse
                | GreaterThan -> if n1 > n2 then ResTrue else ResFalse
                | GreaterOrEqual -> if n1 >= n2 then ResTrue else ResFalse
                | _ -> raise (WrongExpression(sprintf "Term %A is not an operator at %A" op t))
            | _ -> 
                raise (WrongExpression(sprintf "Second operand %A is not a number at %A" t2' t))
        | _ -> 
            raise (WrongExpression(sprintf "First operand %A is not a number at %A" t1' t))
    | Cond(t1, t2, t3) ->
        let t1' = eval t1 env
        match t1' with
        | ResRaise -> ResRaise
        | ResTrue -> eval t2 env
        | ResFalse -> eval t3 env
        | _ -> raise (WrongExpression(sprintf "Term %A is not a Boolean value at %A" t1' t))
    | Fn(id, typ, t1) -> ResClosure(id, t1, env)
    | RecFn(id1, typ1, id2, typ2, t) -> ResRecClosure(id1, id2, t, env)
    | Let(id, typ, t1, t2) ->
        let t1' = eval t1 env
        match t1' with
        | ResRaise -> ResRaise
        | v -> eval t2 <| env.Add(id, t1')
    | Nil -> ResNil
    | IsEmpty(t1) ->
        let t1' = eval t1 env
        match t1' with
        | ResRaise -> ResRaise
        | ResNil -> ResTrue
        | ResCons(_, _) -> ResFalse
        | _ -> raise (WrongExpression(sprintf "Term %A is not a list at %A" t1' t))
    | Head(t1) -> 
        let t1' = eval t1 env
        match t1' with
        | ResRaise -> ResRaise
        | ResCons(head, tail) -> head
        | ResNil -> ResRaise
        | _ -> raise (WrongExpression(sprintf "Term %A is not a list at %A" t1' t))
    | Tail(t1) -> 
        let t1' = eval t1 env
        match t1' with
        | ResRaise -> ResRaise
        | ResCons(head, tail) -> tail
        | ResNil -> ResRaise
        | _ -> raise (WrongExpression(sprintf "Term %A is not a list at %A" t1' t))
    | Raise -> ResRaise
    | Try(t1, t2) ->
        let t1' = eval t1 env
        match t1' with
        | ResRaise -> eval t2 env
        | _ -> t1'
    | X(id) -> 
        if env.ContainsKey id then
            env.[id]
        else
            sprintf "Could not find identifier %A" id |> WrongExpression |> raise


let evaluate t =
    eval t Map.empty
