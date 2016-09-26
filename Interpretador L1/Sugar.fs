module Sugar

open Definition


let rec typeString typ =
    match typ with
    | Type.X(s) -> s
    | Int -> "Int"
    | Bool -> "Bool"
    | Function(t1, t2) ->  sprintf "%s -> %s" (typeString t1) (typeString t2)

let rec stringify term =
    match term with
    | True -> 
        "true"
    | False -> 
        "false"
    | I(i) -> 
        string i
    | OP(n1, op, n2) ->
        let opString = match op with
                        | Add -> "+"
                        | Subtract -> "-"
                        | Multiply -> "*"
                        | Divide -> "/"
                        | LessThan -> "<"
                        | LessOrEqual -> "<="
                        | Equal -> "="
                        | Different -> "!="
                        | GreaterOrEqual -> ">="
                        | GreaterThan -> ">"
        sprintf "(%s %s %s)" (stringify n1) opString (stringify n2)
    | X(id) -> 
        id
    | Fn(id, typ, t) -> 
        sprintf "fn(%s: %s) =\n\t%s" id (typeString typ) (stringify t)
    | App(t1, t2) ->
        sprintf "(%s) %s" (stringify t1) (stringify t2)
    | Let(id, typ, t1, t2) ->
        sprintf "let %s: %s = %s\n%s" id (typeString typ) (stringify t1) (stringify t2)
    | _ -> "hi"

type term with
    member public this.DisplayValue = stringify this