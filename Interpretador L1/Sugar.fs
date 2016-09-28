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
    | Function(t1, t2) ->  
        match t1 with
        | Function(_,_) -> 
            sprintf "(%s) -> %s" (typeString t1) (typeString t2)
        | _ ->
            sprintf "%s -> %s" (typeString t1) (typeString t2)


let rec stringify term lvl =
    let tabs = String.replicate(lvl) "\t"
    match term with
    | True -> 
        tabs + "true"
    | False -> 
        tabs + "false"
    | I(i) -> 
        tabs + (string i)
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
        sprintf "%s(%s %s %s)" tabs (stringify n1 0) opString (stringify n2 0)
    | Cond(t1, t2, t3) ->
        sprintf "%sif %s then\n%s\n%selse\n%s" 
            tabs (stringify t1 0) (stringify t2 (lvl+1)) tabs (stringify t3 (lvl+1))
    | X(id) -> 
        tabs + id
    | Fn(id, typ, t) -> 
        let term = (stringify t (lvl+1))
        if term.EndsWith("\n") then
            sprintf "%sfn(%s: %s) {\n%s%s}\n" 
                tabs id (typeString typ) (stringify t (lvl+1)) tabs
        else
            sprintf "%sfn(%s: %s) {\n%s\n%s}\n" 
                tabs id (typeString typ) (stringify t (lvl+1)) tabs
     | App(t1, t2) ->
        let t1' = (stringify t1 0)
        if t1'.EndsWith("\n") then
            sprintf "%s%s%s" tabs t1' (stringify t2 0)
        else
            sprintf "%s%s %s" tabs t1' (stringify t2 0)
    | Let(id, typ, t1, t2) ->
        sprintf "%slet %s: %s = %s;\n%s" 
            tabs id (typeString typ) (stringify t1 0) (stringify t2 lvl)
    | LetRec(id, typ1, typ2, id2, t1, t2) ->
        let typ1' = typeString typ1
        let typ2' = typeString typ2
        let t1' = stringify t1 (lvl+1)
        let t2' = stringify t2 0
        sprintf "%slet rec %s(%s: %s): %s {\n%s}\n%sin %s" 
            tabs id id2 typ1' typ2' t1' tabs t2'
    | Nil -> 
        "nil"
    | Cons(t1, t2) ->
        sprintf "%s%s::%s" tabs (stringify t1 0) (stringify t2 0)
    | IsEmpty(t) ->
        sprintf "%sempty? %s" tabs (stringify t 0)
    | Head(t) ->
        sprintf "%shead %s" tabs (stringify t 0)
    | Tail(t) ->
        sprintf "%stail %s" tabs (stringify t 0)
    | Raise ->
        tabs + "raise"
    | Try(t1, t2) ->
        sprintf "%stry\n%s\nexcept\n%s" 
            tabs (stringify t1 (lvl+1)) (stringify t2 (lvl+1))

let print term = stringify term 0

type term with
    member public this.DisplayValue = stringify this 0



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

type Match = string * term
    
let getWhile allowed (term: string) =
    let mutable index = 0
    let mutable found = true
    while index < term.Length && found do
        found <- Seq.fold (fun acc x -> acc || term.Substring(index).StartsWith(x)) false allowed
        if found then index <- index + 1 else ()
    term.Substring(0, index)

let rec findOP (text: string) =
    let mutable curIndex = 1

    let term1, t1: Match = findTerm (text.Substring(curIndex))
    curIndex <- curIndex + term1.Length

    let opString = text.Substring(curIndex)
    let opTrimmed = opString.TrimStart()
    let opChar, op = 
        if   opTrimmed.StartsWith "+"  then "+", Add
        elif opTrimmed.StartsWith "-"  then "-", Subtract
        elif opTrimmed.StartsWith "*"  then "*", Multiply
        elif opTrimmed.StartsWith "/"  then "/", Divide
        elif opTrimmed.StartsWith "<=" then "<=", LessOrEqual
        elif opTrimmed.StartsWith "<"  then "<", LessThan
        elif opTrimmed.StartsWith "="  then "=", Equal
        elif opTrimmed.StartsWith "!=" then "!=", Different
        elif opTrimmed.StartsWith ">=" then ">=", GreaterOrEqual
        elif opTrimmed.StartsWith ">"  then ">", GreaterThan
        else raise (InvalidEntryText ("Operator is unknown at " + text))
    let opString = getWhile [" "; "\n"; "\r"; "\t"; opChar] opString
    curIndex <- curIndex + opString.Length

    let term2, t2 = findTerm (text.Substring(curIndex))
    curIndex <- curIndex + term2.Length

    (text.Substring(0,curIndex+1), OP(t1, op, t2))
and
    findTerm (text: string) =

    let emptyText = getWhile [" "; "\n"; "\r"; "\t"] text
    let text = text.Substring(emptyText.Length)

    let subText, term = 
        if text.StartsWith("(") then
            let s, t = findOP text
            (emptyText + s, t)
        elif Char.IsDigit(text.Chars(0)) then
            let s = text.ToCharArray()
            let t = s |> Seq.takeWhile (fun x -> Char.IsDigit(x))
            (emptyText+String.Concat(t), I(int (String.Concat(t))))
        else
            (emptyText, Nil)
    (subText, term)
//    if (subText = text) then
//        (subText, term)
//    else
//        let restText, restTerm = findTerm (text.Substring(subText.Length))
//        (subText+restText, App(term, restTerm))
    
let rec parseTerm (text: string) =
    let mutable remaining = text
    let mutable sub, term = findTerm remaining
    remaining <- remaining.Substring(sub.Length)
    while remaining.Length > 0 do
        let temp = findTerm remaining
        term <- App(term, snd temp)
        remaining <- remaining.Substring((fst temp).Length)
    term

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
    
