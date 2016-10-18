module Evaluation

open Definition

let rec private eval t env =
    match t with
    | True -> 
        True
    | False -> 
        False
    | I(i) -> 
        I(i)
    | OP(t1, Application, t2) ->
        let t1' = eval t1 env
        match t1' with
        | Raise -> 
            Raise
        | RecClosure(id1, id2, e, env') ->
            let t2' = eval t2 env
            match t2' with
            | Raise -> 
                Raise
            | v when V(v) -> 
                eval e <| env'.Add(id2, t2').Add(id1, t1')
            |  _ -> 
                raise (WrongExpression(sprintf "Second operand %A is not a value at %A" t2' t))
        | Closure(id, e, env') ->
            let t2' = eval t2 env
            match t2' with
            | Raise -> 
                Raise
            | v when V(v) -> 
                eval e <| env'.Add(id, t2')
            |  _ -> 
                raise (WrongExpression(sprintf "Second operand %A is not a value at %A" t2' t))
        | _ ->
            raise (WrongExpression(sprintf "First operand %A is not a function at %A" t1' t))
    | OP(t1, Cons, t2) ->
        let t1' = eval t1 env
        match t1' with
        | Raise -> 
            Raise
        | v when V(v) ->
            let t2' = eval t2 env
            match t2' with
            | OP(_, Cons, _) when V(v) -> 
                OP(t1', Cons, t2')
            | Nil when V(v) -> 
                OP(t1', Cons, Nil)
            | _ -> 
                raise (WrongExpression(sprintf "Term %A is not a list at %A" t2' t))
        | _ ->
            raise (WrongExpression(sprintf "Term %A is not a value at %A" t1' t))
    | OP(t1, op, t2) ->
        let t1' = eval t1 env
        match t1' with
        | Raise ->
            Raise
        | I(n1) ->
            let t2' = eval t2 env
            match t2' with
            | Raise ->
                Raise
            | I(n2) ->
                match op with
                | Add -> I(n1 + n2)
                | Subtract -> I(n1 - n2)
                | Multiply -> I(n1 * n2)
                | Divide when n2 <> 0 -> I(n1 / n2)
                | Divide when n2 = 0 -> Raise
                | LessThan -> if n1 < n2 then True else False
                | LessOrEqual -> if n1 <= n2 then True else False
                | Equal -> if n1 = n2 then True else False
                | Different -> if n1 <> n2 then True else False
                | GreaterThan -> if n1 > n2 then True else False
                | GreaterOrEqual -> if n1 >= n2 then True else False
                | _ -> raise (WrongExpression(sprintf "Term %A is not an operator at %A" op t))
            | _ -> 
                raise (WrongExpression(sprintf "Second operand %A is not a number at %A" t2' t))
        | _ -> 
            raise (WrongExpression(sprintf "First operand %A is not a number at %A" t1' t))
    | Cond(t1, t2, t3) ->
        let t1' = eval t1 env
        match t1' with
        | Raise -> Raise
        | True -> eval t2 env
        | False -> eval t3 env
        | _ -> raise (WrongExpression(sprintf "Term %A is not a Boolean value at %A" t1' t))
    | Fn(id, typ, t1) -> Closure(id, t1, env)
    | Let(id, typ, t1, t2) ->
        let t1' = eval t1 env
        match t1' with
        | Raise -> Raise
        | v when V(v) -> eval t2 <| env.Add(id, t1')
        | _ -> raise (WrongExpression(sprintf "Term %A is not a value at %A" t1' t))
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
        | _ -> raise (WrongExpression(sprintf "Term %A is not a list at %A" t1' t))
    | Head(t1) -> 
        let t1' = eval t1 env
        match t1' with
        | OP(head, Cons, tail) -> head
        | Nil -> Raise
        | _ -> raise (WrongExpression(sprintf "Term %A is not a list at %A" t1' t))
    | Tail(t1) -> 
        let t1' = eval t1 env
        match t1' with
        | OP(head, Cons, tail) -> tail
        | Nil -> Raise
        | _ -> raise (WrongExpression(sprintf "Term %A is not a list at %A" t1' t))
    | Raise -> Raise
    | Try(t1, t2) ->
        let t1' = eval t1 env
        match t1' with
        | Raise -> eval t2 env
        | _ -> t1'
    | X(id) -> env.[id]
    | _ -> raise (WrongExpression(sprintf "%A is not a Term" t))


let evaluate t =
    eval t Map.empty
