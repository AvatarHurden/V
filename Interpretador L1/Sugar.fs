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
     | OP(t1, Application, t2) ->
        let t1' = (stringify t1 0)
        if t1'.EndsWith("\n") then
            sprintf "%s%s%s" tabs t1' (stringify t2 0)
        else
            sprintf "%s%s %s" tabs t1' (stringify t2 0)
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
        "if ", IfThen;
        "then ", ThenElse;
        "let rec ", LetRecIn;
        "let ", LetSemicolon;
        "try ", TryExcept
        ]

let findClosing (text:string) =
    let pair = openings.Keys |> Seq.fold (fun acc x -> if text.StartsWith(x) then openings.Item(x) else acc) Parenthesis 
    let subtractor = 
        match pair with
        | Parenthesis -> ")"
        | Brackets -> "}"
        | IfThen -> "then "
        | ThenElse -> "else "
        | LetRecIn -> "in "
        | LetSemicolon -> ";"
        | TryExcept -> "except "
    let adder = 
        match pair with
        | Parenthesis -> "("
        | Brackets -> "{"
        | IfThen -> "if "
        | ThenElse -> "then "
        | LetRecIn -> "let rec "
        | LetSemicolon -> "let "
        | TryExcept -> "try "
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
        adder, text.Substring(adder.Length, iterator - adder.Length - subtractor.Length), subtractor
    elif count < 0 then
        raise (InvalidEntryText ("There is an extra opening " + adder))
    else
        raise (InvalidEntryText ("Missing a closing " + subtractor))

let getSpaces (term: string) =
    String.Concat (term |> Seq.takeWhile Char.IsWhiteSpace)
  
// Encontra todo o texto entre a primeira ocorrência de StartText e a primeira 
// de endText. É permitido apenas espaços em branco entre o começo de text
// e a primeira ocorrência de startText. Caso endText seja vazio, vai até o fim
// de text. Caso startText seja vazio, texto do interior começa no começo do text
// Retorna uma tupla composta de:
//      espaços em branco + todo o texto até endText
//      texto do interior + espaços em branco
let findBetween startText endText text =
    let mutable processed = getSpaces text
    let trimmedText = text.Substring(processed.Length)
    if not (trimmedText.StartsWith(startText)) then
        raise (InvalidEntryText("Expected to find " + startText + ", but found " 
            + trimmedText.Substring(startText.Length) + " instead"))
    else
        processed <- processed + startText

        let mutable count = 0
        while not (text.Substring(processed.Length + count).StartsWith(endText)) do
            count <- count + 1
        
        let inside = text.Substring(processed.Length, count)
        processed <- processed + inside + endText

        (processed, inside)

// Avança em text até encontrar algum caractere inválido para nome de variáveis
// Se o nome encontrado for algum texto reservado, lança uma exceção.
// Permite espaços brancos no começo da string
// O retorno da função é uma tupla composto de (espaço em branco+ident, ident)
let findIdent text = 
    let emptyText = getSpaces text
    let trimmedText = text.Substring(emptyText.Length)
    let prohibited = " .,;:+-/*<=>(){}?".ToCharArray()
    let ident = String.Concat (trimmedText |> Seq.takeWhile (fun x -> not (Seq.exists ((=) x) prohibited)))
    (emptyText+ident, ident)   

// Recursively find the type information in the input string.
// The string must contain only a type definition (that is, it must end without any
// other characters except for empty spaces)
let rec findType (text:string) =
    let mutable processed = getSpaces text
    let trimmedText = text.Trim()
    let endingSpaces = text.Substring(processed.Length+trimmedText.Length)

    let typ1Text, typ1 = 
        if trimmedText.StartsWith("(") then
            let opening, inside, closing = findClosing trimmedText
            let s, t = findType inside
            (processed+opening+s+closing, t)
        elif trimmedText.StartsWith("Int") then
            (processed+"Int"+endingSpaces, Int)
        elif trimmedText.StartsWith("Bool") then
            (processed+"Bool"+endingSpaces, Bool)
        else
            raise (InvalidEntryText "Invalid Type information")
    
    if typ1Text.Equals(processed+trimmedText+endingSpaces) then
        (typ1Text, typ1)
    else
        processed <- typ1Text
        let emptyText = getSpaces (text.Substring(processed.Length))
        processed <- processed + emptyText
        if text.Substring(processed.Length).StartsWith("->") then
            processed <- processed + "->"
            let typ2Text, typ2 = text.Substring(processed.Length) |> findType 
            (processed+typ2Text, Function(typ1, typ2))
        else
            raise (InvalidEntryText "Invalid Type information")
        
// Finds an entire Let expression. After the ";", calls findTerms with the remaining text
let rec findLet text =
    let opening, definition, closing = findClosing text

    let s, id = findIdent definition
    let mutable processedText = s

    let s, typeString = findBetween ":" "=" (definition.Substring(processedText.Length))
    let _, typ = findType typeString
    processedText <- processedText + s

    let t1 = findTerms (definition.Substring(processedText.Length))
    processedText <- opening + definition + closing

    let t2 = findTerms (text.Substring(processedText.Length))

    (text, Let(id, typ, t1, t2))
// Finds a single term in the input string
// If this function finds a "subterm" (that is, an opening parenthesis), it calls
// findTerms resursively
// Returns a tuple made of (all the processed text, term)
and findTerm (text: string) =

    let emptyText = getSpaces text
    let trimmedText = text.Substring(emptyText.Length)
    
    if trimmedText.StartsWith("let ") then
        let s, t = findLet trimmedText
        (emptyText+s, t)
        //let opening, closing, subTerm = findClosing trimmedText
    elif trimmedText.StartsWith("(") then
        let opening, subTerm, closing = findClosing trimmedText
        let s, t = (opening+subTerm+closing, findTerms subTerm)
        (emptyText + s, t)
    elif Char.IsDigit(trimmedText.Chars(0)) then
        let s = trimmedText.ToCharArray()
        let t = s |> Seq.takeWhile (fun x -> Char.IsDigit(x))
        (emptyText+String.Concat(t), I(int (String.Concat(t))))
    else
        let text, ident = findIdent trimmedText
        (emptyText+text, X(ident))
and
// Repeatedly calls findTerm to find all terms defined in the input string
// This is needed to deal with the left-associativity of operations
// Returns the finished term (when more than one subterm exists, this is always an OP)
    findTerms text =
    let text = text.TrimEnd()
    let mutable subText, term = findTerm text
    while not (subText.Equals(text)) do

        let opString = text.Substring(subText.Length)
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
            else "", Application
        subText <- subText + (getSpaces opString) + opChar

        let newText, newTerm = findTerm (text.Substring(subText.Length).TrimEnd())
        subText <- subText + newText
        
        term <- OP(term, op, newTerm)
    term

let rec parseTerm (text: String) = 
    let text = ["\n"; "\t"; "\r"] |> Seq.fold (fun (acc: String) x -> acc.Replace(x, " ")) text
    findTerms text