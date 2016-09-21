module Evaluation

open Definition

// Replace identifier x for value in term
let rec replace x value term = 
    match term with
    | V(v) -> V(v)
    | OP(t1, op, t2) -> OP((replace x value t1), op, (replace x value t2))
    | Cond(t1, t2, t3) -> Cond((replace x value t1), (replace x value t2), (replace x value t3))
    | X(id) ->
        if (id = x) then
            value
        else
            X(id)
    | App(t1, t2) -> App((replace x value t1), (replace x value t2))
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
    | Cons(t1, t2) -> Cons((replace x value t1), (replace x value t2))
    | IsEmpty(t1) -> IsEmpty((replace x value t1))
    | Head(t1) -> Head((replace x value t1))
    | Tail(t1) -> Tail((replace x value t1))
    | Raise -> Raise
    | Try(t1, t2) -> Try((replace x value t1), (replace x value t2))

let rec eval t =
    match t with
    | V(v) -> V(v)
    | OP(t1, Add, t2) ->
        let t1' = eval t1 in
        let t2' = eval t2 in
        match t1', t2' with
        | V(N(I(n1))), V(N(I(n2))) -> V(N(I(n1 + n2)))
        | _, _ -> raise WrongExpression
    | OP(t1, Subtract, t2) ->
        let t1' = eval t1 in
        let t2' = eval t2 in
        match t1', t2' with
        | V(N(I(n1))), V(N(I(n2))) -> V(N(I(n1 - n2)))
        | _, _ -> raise WrongExpression
    | OP(t1, Multiply, t2) ->
        let t1' = eval t1 in
        let t2' = eval t2 in
        match t1', t2' with
        | V(N(I(n1))), V(N(I(n2))) -> V(N(I(n1 * n2)))
        | _, _ -> raise WrongExpression
    | OP(t1, LessThan, t2) ->
        let t1' = eval t1 in
        let t2' = eval t2 in
        match t1', t2' with
        | V(N(I(n1))), V(N(I(n2))) when n1 < n2 -> V(B(True))
        | V(N(I(n1))), V(N(I(n2))) when not(n1 < n2) -> V(B(False))
        | _, _ -> raise WrongExpression
    | OP(t1, LessOrEqual, t2) ->
        let t1' = eval t1 in
        let t2' = eval t2 in
        match t1', t2' with
        | V(N(I(n1))), V(N(I(n2))) when n1 <= n2 -> V(B(True))
        | V(N(I(n1))), V(N(I(n2))) when not(n1 <= n2) -> V(B(False))
        | _, _ -> raise WrongExpression
    | OP(t1, Equal, t2) ->
        let t1' = eval t1 in
        let t2' = eval t2 in
        match t1', t2' with
        | V(N(I(n1))), V(N(I(n2))) when n1 = n2 -> V(B(True))
        | V(N(I(n1))), V(N(I(n2))) when not(n1 = n2) -> V(B(False))
        | _, _ -> raise WrongExpression
    | OP(t1, Different, t2) ->
        let t1' = eval t1 in
        let t2' = eval t2 in
        match t1', t2' with
        | V(N(I(n1))), V(N(I(n2))) when n1 <> n2 -> V(B(True))
        | V(N(I(n1))), V(N(I(n2))) when not(n1 <> n2) -> V(B(False))
        | _, _ -> raise WrongExpression
    | OP(t1, GreaterOrEqual, t2) ->
        let t1' = eval t1 in
        let t2' = eval t2 in
        match t1', t2' with
        | V(N(I(n1))), V(N(I(n2))) when n1 >= n2 -> V(B(True))
        | V(N(I(n1))), V(N(I(n2))) when not(n1 >= n2) -> V(B(False))
        | _, _ -> raise WrongExpression
    | OP(t1, GreaterThan, t2) ->
        let t1' = eval t1 in
        let t2' = eval t2 in
        match t1', t2' with
        | V(N(I(n1))), V(N(I(n2))) when n1 > n2 -> V(B(True))
        | V(N(I(n1))), V(N(I(n2))) when not(n1 > n2) -> V(B(False))
        | _, _ -> raise WrongExpression
    | Cond(t1, t2, t3) ->
        let t1' = eval t1 in
        match t1' with
        | V(B(True)) ->
            let t2' = eval t2 in
            match t2' with
            | V(v) -> V(v)
            | _ -> raise WrongExpression
        | V(B(False)) ->
            let t3' = eval t3 in
            match t3' with
            | V(v) -> V(v)
            | _ -> raise WrongExpression
        | _ -> raise WrongExpression
    | _ -> raise WrongExpression