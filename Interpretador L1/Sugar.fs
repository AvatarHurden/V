module Sugar

open System.Text.RegularExpressions
open Definition
open System

exception InvalidEntryText of string


  ////////////////
 //  Printing  //
////////////////

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

type term with
    member public this.DisplayValue = stringify this



  ///////////////
 //  Parsing  //
///////////////

type DelimiterPairs =
    | Parenthesis
    | Brackets
    | IfThen
    | ThenElse
    | LetRecIn
    | LetSemicolon
    | TryExcept

let openings = 
    dict[
        "(", Parenthesis; 
        "{", Brackets;
        "if", IfThen;
        "then", ThenElse;
        "let rec", LetRecIn;
        "let", LetSemicolon;
        "try", TryExcept
        ]

let findClosing (text:string) =
    let pair = openings.Keys |> Seq.fold (fun acc x -> if text.StartsWith(x) then openings.Item(x) else acc) Parenthesis 
    let subtractor = 
        match pair with
        | Parenthesis -> ")"
        | Brackets -> "}"
        | IfThen -> "then"
        | ThenElse -> "else"
        | LetRecIn -> "in"
        | LetSemicolon -> ";"
        | TryExcept -> "except"
    let adder = 
        match pair with
        | Parenthesis -> "("
        | Brackets -> "{"
        | IfThen -> "if"
        | ThenElse -> "then"
        | LetRecIn -> "let rec"
        | LetSemicolon -> "let"
        | TryExcept -> "try"
    let mutable count = 1
    let mutable iterator = 1
    while count <> 0 && iterator < text.Length do
        if text.Substring(iterator).StartsWith(subtractor) then
            count <- count - 1
        else if text.Substring(iterator).StartsWith(adder) then
            count <- count + 1
        else 
            ()
        iterator <- iterator + 1
    if (count = 0) then
        text.Substring(0, iterator)
    elif count < 0 then
        raise (InvalidEntryText ("There is an extra opening " + adder))
    else
        raise (InvalidEntryText ("Missing a closing " + subtractor))

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

type Match = string * (string list)
    
let getWhile (allowed : string list) (term: string) =
    let mutable index = 0
    let mutable found = true
    while index < term.Length && found do
        found <- Seq.fold (fun acc x -> acc || term.Substring(index).StartsWith(x)) false allowed
        if found then index <- index + 1 else ()
    term.Substring(0, index)

let rec findOP (text: string) =
    let mutable curIndex = 1
    let term1, _: Match = findTerm (text.Substring(curIndex))
    curIndex <- curIndex + term1.Length
    let opString = text.Substring(curIndex)
    let opTrimmed = opString.TrimStart()
    let op = 
        if   opTrimmed.StartsWith "+"  then "+"
        elif opTrimmed.StartsWith "-"  then "-"
        elif opTrimmed.StartsWith "*"  then "*"
        elif opTrimmed.StartsWith "/"  then "/"
        elif opTrimmed.StartsWith "<=" then "<="
        elif opTrimmed.StartsWith "<"  then "<"
        elif opTrimmed.StartsWith "="  then "="
        elif opTrimmed.StartsWith "!=" then "!="
        elif opTrimmed.StartsWith ">=" then ">="
        elif opTrimmed.StartsWith ">"  then ">"
        else raise (InvalidEntryText ("Operator is unknown at " + text))
    let opString = getWhile [" "; op] opString
    curIndex <- curIndex + opString.Length
    let term2, _ = findTerm (text.Substring(curIndex))
    curIndex <- curIndex + term2.Length
    (text.Substring(0,curIndex+1), [term1; op; term2])
and
    findTerm (text: string) =
    if Char.IsDigit(text.Chars(0)) then
        let s = text.ToCharArray()
        let t = s |> Seq.takeWhile (fun x -> Char.IsDigit(x))
        (String.Concat(t), [String.Concat(t)])
    elif text.StartsWith("(") then
        findOP text
    else
        ("", [""])
    
let rec parseOP (text: string) =
    let term, [term1; opString; term2] = findOP text
    let op = 
        match opString with
        | "+" -> Add
        | "-" -> Subtract
        | "*" -> Multiply
        | "/" -> Divide
        | "<=" -> LessOrEqual
        | "<" -> LessThan
        | "=" -> Equal
        | "!=" -> Different
        | ">=" -> GreaterOrEqual
        | ">" -> GreaterThan
        | _ -> raise (InvalidEntryText ("Operator " + opString + " is unknown - in " + term))
    OP(parseTerm term1, op, parseTerm term2)
and
    parseTerm (text: string) =
    if text.StartsWith("(") then
        parseOP text
    elif Char.IsDigit(text.Chars(0)) then
        I(int text)
    else
        raise WrongExpression
//    elif text.StartsWith("if") then
//        parseCond text
//    elif text.StartsWith("fn") then
//        parseFn text
//    elif text.StartsWith("let rec") then
//        parseLetRec text
//    elif text.StartsWith("let") then
//        parseLet text
//    elif text.StartsWith("empty? ") then
//        IsEmpty(parse text.Substring(("empty? ".Length)))

// Will Delete this
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
    
