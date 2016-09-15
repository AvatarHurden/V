// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

type Type =
    | X of string
    | Int
    | Bool
    | Function of Type * Type

type n =
    | I of int

type b =
    | True
    | False

type v =
    | B of b
    | N of n

type op =
    | Add
    | Subtract
    | Multiply
    | Divide
    | LessThan
    | LessOrEqual
    | Equal
    | Different
    | GreaterOrEqual
    | GreaterThan

type Ident =
    | X of string

type term =
    | V of v
    | OP of term * op * term
    | Cond of term * term * term
    | X of Ident
    | App of term * term
    | Fn of Ident * Type * term
    | Let of Ident * Type * term * term
    | LetRec of Type * Type * Ident * term * term
    | Nil
    | Cons of term * term
    | IsEmpty of term
    | Head of term
    | Tail of term
    | Raise
    | Try of term * term

exception WrongExpression

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

[<EntryPoint>]
let main argv = 
    printfn "%A" argv
    0 // return an integer exit code
