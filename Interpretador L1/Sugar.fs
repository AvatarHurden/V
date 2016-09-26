module Sugar

open System.Text.RegularExpressions
open Definition

exception InvalidEntryText of string

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
    | Cond(t1, t2, t3) ->
        sprintf "if %s then\n\t%s\nelse\n\t%s" (stringify t1) (stringify t2) (stringify t3)
    | X(id) -> 
        id
    | Fn(id, typ, t) -> 
        sprintf "fn(%s: %s):\n\treturn %s\n" id (typeString typ) (stringify t)
    | App(t1, t2) ->
        let t1' = (stringify t1)
        if t1'.EndsWith("\n") then
            sprintf "%s%s" t1' (stringify t2)
        else
            sprintf "%s %s" t1' (stringify t2)
    | Let(id, typ, t1, t2) ->
        sprintf "let %s: %s = %s in\n%s" id (typeString typ) (stringify t1) (stringify t2)
    | LetRec(id, typ1, typ2, id2, t1, t2) ->
        let typ1' = typeString typ1
        let typ2' = typeString typ2
        let t1' = stringify t1
        let t2' = stringify t2
        sprintf "let rec %s(%s: %s): %s\n\t%s\nin %s" id id2 typ1' typ2' t1' t2'
    | Nil -> 
        "nil"
    | Cons(t1, t2) ->
        sprintf "%s::%s" (stringify t1) (stringify t2)
    | IsEmpty(t) ->
        sprintf "empty? %s" (stringify t)
    | Head(t) ->
        sprintf "head %s" (stringify t)
    | Tail(t) ->
        sprintf "tail %s" (stringify t)
    | Raise ->
        "raise"
    | Try(t1, t2) ->
        sprintf "try\n\t%s\nexcept\n\t%s" (stringify t1) (stringify t2)

let (|Match|_|) pattern input =
    let re = new Regex(pattern, RegexOptions.Singleline)
    let m = re.Match(input) in
    if m.Success then 
        Some(List.tail [ for g in m.Groups -> g.Value ])
    else
        None

let rec parseType text =
    match text with
    | "Int" -> 
        Int
    | "Bool" -> 
        Bool
    | Match "?(.*) -> ?(.*)" [typ1; typ2] ->
        Function(parseType typ1, parseType typ2)
    | x -> Type.X(x)

let rec parse text =
    match text with
    | Match "^let rec (.*)\((.*): (.*)\): (.*)\r?\n\t(.*)\r?\nin (.*)" [id1; id2; typ1; typ2; t1; t2] ->
        LetRec(id1, parseType typ1, parseType typ2, id2, parse t1, parse t2)
    | Match "^let (.+?): (.+?) = (.+?) in\r?\n(.+)" [id; typ; t1; t2] ->
        Let(id, parseType typ, parse t1, parse t2)
    | Match "^fn\((.*): (.*)\):\r?\n\treturn (.*)\r?\n" [id; typ; t] ->
        Fn(id, parseType typ, parse t)
    | Match "^if (.+?) then\r?\n\t(.+)\r?\nelse\r?\n\t(.+)" [t1; t2; t3] ->
        Cond(parse t1, parse t2, parse t3)
    | Match "^try\r?\n\t(.*)\r?\nexcept\r?\n\t(.*)" [t1; t2] ->
        Try(parse t1, parse t2)
    | Match "^(.*)::(.*)" [t1; t2] ->
        Cons(parse t1, parse t2)
    | Match "^empty\? (.*)" [t] ->
        IsEmpty(parse t)
    | Match "^head (.*)" [t] ->
        Head(parse t)
    | Match "^tail (.*)" [t] ->
        Tail(parse t)
    | Match "^\((.+?) (\+|\-|\*|\/|<|<=|=|!=|>=|>) (.+?)\)" [n1; op; n2] ->
        let op' = 
            match op with
            | "+" -> Add
            | "-" -> Subtract
            | "*" -> Multiply
            | "/" -> Divide
            | "<" -> LessThan
            | "<=" -> LessOrEqual
            | "=" -> Equal
            | "!=" -> Different
            | ">=" -> GreaterOrEqual
            | ">" -> GreaterThan
            | _ -> raise (InvalidEntryText "Numeric operator not defined")
        OP(parse n1, op', parse n2)
    | Match "^\((.*) (.*)\)" [t1; t2] ->
        App(parse t1, parse t2)
    | Match "^([0-9]+)" [i] ->
        I(int i)
    | "true" ->
        True
    | "false" ->
        False
    | "nil" -> 
        Nil
    | "raise" ->
        Raise
    | x -> X(x)
    

type term with
    member public this.DisplayValue = stringify this