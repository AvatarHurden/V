module Evaluation

open Definition

// Replace identifier x for value in term
let rec replace x value term = 
    match term with
    | True -> True
    | False -> False
    | I(i) -> I(i)
    | OP(t1, op, t2) -> OP((replace x value t1), op, (replace x value t2))
    | Cond(t1, t2, t3) -> Cond((replace x value t1), (replace x value t2), (replace x value t3))
    | X(id) ->
        if (id = x) then
            value
        else
            X(id)
    | Fn(id, typ, t1) ->
        if (id = x) then
            Fn(id, typ, t1)
        else
            Fn(id, typ, (replace x value t1))
    | Let(id, typ, t1, t2) ->
        if (id = x) then
            Let(id, typ, (replace x value t1), t2)
        else
            Let(id, typ, (replace x value t1), (replace x value t2))
    | LetRec(id1, typ1, typ2, id2, t1, t2) ->
        if (id1 = x) then
            LetRec(id1, typ1, typ2, id2, t1, t2)
        elif (id2 = x) then
            LetRec(id1, typ1, typ2, id2, t1, (replace x value t2))
        else
            LetRec(id1, typ1, typ2, id2,  (replace x value t1),  (replace x value t2))
    | Nil -> Nil
    | IsEmpty(t1) -> IsEmpty((replace x value t1))
    | Head(t1) -> Head((replace x value t1))
    | Tail(t1) -> Tail((replace x value t1))
    | Raise -> Raise
    | Try(t1, t2) -> Try((replace x value t1), (replace x value t2))

let rec eval t =
    match t with
    | True -> True
    | False -> False
    | I(i) -> I(i)
    | OP(t1, Application, t2) ->
        let t1' = eval t1 in
        let t2' = eval t2 in
        match t1', t2' with
        | Fn(id, typ, e), v when V(v) -> eval (replace id v e)
        | _, v when V(v) -> raise (WrongExpression(sprintf "First operand %A is not a function at %A" t1' t))
        | Fn(id, typ, e), _ -> raise (WrongExpression(sprintf "Second operand %A is not a value at %A" t2' t))
        | _, _ -> raise (WrongExpression(sprintf "Operands %A and %A do not match the Application operator at %A" t1' t2' t))
    | OP(t1, Cons, t2) ->
        let t2' = eval t2 in
        match t2' with
        | OP(_, Cons, _) -> OP(t1, Cons, t2')
        | Nil -> OP(t1, Cons, Nil)
        | _ -> raise (WrongExpression(sprintf "Term %A is not a list at %A" t2' t))
    | OP(t1, op, t2) ->
        let t1' = eval t1 in
        let t2' = eval t2 in
        match t1', t2' with
        | I(n1), I(n2) ->
            match op with
            | Add -> I(n1 + n2)
            | Subtract -> I(n1 - n2)
            | Multiply -> I(n1 * n2)
            | Divide when n2 <> 0 -> I(n1 / n2)
            | Divide when n2 = 0 -> raise (WrongExpression(sprintf "Can't divide by zero at %A" t))
            | LessThan -> if n1 < n2 then True else False
            | LessOrEqual -> if n1 <= n2 then True else False
            | Equal -> if n1 = n2 then True else False
            | Different -> if n1 <> n2 then True else False
            | GreaterThan -> if n1 > n2 then True else False
            | GreaterOrEqual -> if n1 >= n2 then True else False
            | _ -> raise (WrongExpression(sprintf "Term %A is not an operator at %A" op t))
        | _, I(n) -> raise (WrongExpression(sprintf "First operand %A is not a number at %A" t1' t))
        | I(n), _ -> raise (WrongExpression(sprintf "Second operand %A is not a number at %A" t2' t))
        | _, _ -> raise (WrongExpression(sprintf "Operands %A and %A are not numbers at %A" t1' t2' t))
    | Cond(t1, t2, t3) ->
        let t1' = eval t1 in
        match t1' with
        | True -> eval t2
        | False -> eval t3
        | _ -> raise (WrongExpression(sprintf "Term %A is not a Boolean value at %A" t1' t))
    | Fn(id, typ, t1) as fn -> fn
    | Let(id, typ, t1, t2) ->
        let t1' = eval t1 in
        if V(t1') then
            eval (replace id t1' t2)
        else
            raise (WrongExpression(sprintf "Term %A is not a value at %A" t1' t))
    | LetRec(id1, typ1, typ2, id2, t1, t2) ->
        let rec2 = LetRec(id1, typ1, typ2, id2, t1, t1) in
        let fn = Fn(id2, typ1, rec2) in
        eval (replace id1 fn t2)
    | Nil -> Nil
    | IsEmpty(t1) ->
        let t1' = eval t1
        match t1' with
        | Nil -> True
        | OP(_, Cons, _) -> False
        | _ -> raise (WrongExpression(sprintf "Term %A is not a list at %A" t1' t))
    | Head(t1) -> 
        let t1' = eval t1 in
        match t1' with
        | OP(head, Cons, tail) -> head
        | _ -> raise (WrongExpression(sprintf "Term %A is not a list at %A" t1' t))
    | Tail(t1) -> 
        let t1' = eval t1 in
        match t1' with
        | OP(head, Cons, tail) -> tail
        | _ -> raise (WrongExpression(sprintf "Term %A is not a list at %A" t1' t))
    | Raise -> Raise
    | Try(t1, t2) ->
        let t1' = eval t1 in
        match t1' with
        | Raise -> eval t2
        | _ -> t1'
    | _ -> raise (WrongExpression(sprintf "%A is not a Term" t))
