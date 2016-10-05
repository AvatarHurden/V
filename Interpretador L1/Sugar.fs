module Sugar

open System.Text.RegularExpressions
open Definition
open System

exception InvalidEntryText of string


  ////////////////
 //  Printing  //
////////////////
//#region Printing

let rec private typeString typ =
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
    | List(t) ->
        sprintf "[%s]" (typeString t)

let rec private stringify term lvl =
    let tabs = String.replicate(lvl) "\t"
    match term with
    | True -> 
        tabs + "true"
    | False -> 
        tabs + "false"
    | I(i) -> 
        tabs + (string i)
    | OP (t1, Pipe, t2) ->
        let t1' = (stringify t1 0)
        sprintf "%s%s |> %s" tabs t1' (stringify t2 0)
    | OP(t1, Application, t2) ->
        let t1' = (stringify t1 0)
        if t1'.EndsWith("\n") then
            sprintf "%s%s%s" tabs t1' (stringify t2 0)
        else
            sprintf "%s%s %s" tabs t1' (stringify t2 0)
    | OP(t1, Cons, t2) ->
        match t1 with
        | OP(_, cons, _) ->
            sprintf "%s(%s)::%s" tabs (stringify t1 0) (stringify t2 0)
        | _ ->
            sprintf "%s%s::%s" tabs (stringify t1 0) (stringify t2 0)
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
                        | _ -> "nao sei o que é"
        sprintf "%s(%s %s %s)" tabs (stringify n1 0) opString (stringify n2 0)
    | Cond(t1, t2, t3) ->
        sprintf "%sif %s then\n%s\n%selse\n%s" 
            tabs (stringify t1 0) (stringify t2 (lvl+1)) tabs (stringify t3 (lvl+1))
    | X(id) -> 
        tabs + id
    | Fn(id, Some typ, t) -> 
        let term = (stringify t (lvl+1))
        if term.EndsWith("\n") then
            sprintf "%sfn(%s: %s) {\n%s%s}\n" 
                tabs id (typeString typ) (stringify t (lvl+1)) tabs
        else
            sprintf "%sfn(%s: %s) {\n%s\n%s}" 
                tabs id (typeString typ) (stringify t (lvl+1)) tabs
    | Fn(id, None, t) -> 
        let term = (stringify t (lvl+1))
        if term.EndsWith("\n") then
            sprintf "%sfn(%s) {\n%s%s}\n" 
                tabs id (stringify t (lvl+1)) tabs
        else
            sprintf "%sfn(%s) {\n%s\n%s}" 
                tabs id (stringify t (lvl+1)) tabs
    | Let(id, Some typ, t1, t2) ->
        sprintf "%slet %s: %s = %s;\n%s" 
            tabs id (typeString typ) (stringify t1 0) (stringify t2 lvl)
    | Let(id, None, t1, t2) ->
        sprintf "%slet %s = %s;\n%s" 
            tabs id (stringify t1 0) (stringify t2 lvl)
    | LetRec(id, Some typ1, Some typ2, id2, t1, t2) ->
        let typ1' = typeString typ1
        let typ2' = typeString typ2
        let t1' = stringify t1 (lvl+1)
        let t2' = stringify t2 lvl
        sprintf "%slet rec %s(%s: %s): %s {\n%s\n%s};\n%s" 
            tabs id id2 typ1' typ2' t1' tabs t2'
    | LetRec(id, None, None, id2, t1, t2) ->
        let t1' = stringify t1 (lvl+1)
        let t2' = stringify t2 lvl
        sprintf "%slet rec %s(%s) {\n%s\n%s};\n%s" 
            tabs id id2 t1' tabs t2'
    | Nil -> 
        sprintf "%snil" tabs
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

//#endregion Printing


  ///////////////
 //  Parsing  //
///////////////
//#region Parsing

type private DelimiterPairs =
    | Parenthesis
    | Brackets
    | SquareBrackets
    | IfThen
    | ThenElse
    | LetSemicolon
    | TryExcept
    | Custom of string * string

//#region Utilities
let operatorsAtPriority i =
    match i with             
    | 0 -> [Multiply; Divide]  
    | 1 -> [Add; Subtract]   
    | 2 -> [Cons]                                                 
    | 3 -> [Application]   
    | 4 -> [Pipe]  
    | 5 -> [LessOrEqual; LessThan; Equal; Different; GreaterThan; GreaterOrEqual]
    | _ -> []

let private splitSpaces (term: string) =
    let empty = String.Concat (term |> Seq.takeWhile Char.IsWhiteSpace)
    empty, term.Substring(empty.Length)
  
let private countPairs pair (text: string) =
    let adder, subtractor = 
        match pair with
        | Parenthesis -> "(", ")"
        | Brackets -> "{", "}"
        | SquareBrackets -> "[", "]"
        | IfThen -> "if ", " then "
        | ThenElse -> " then ", " else "
        | LetSemicolon -> "let ", ";"
        | TryExcept -> "try ", "except "
        | Custom(t1, t2) -> t1, t2

    let mutable count = 0
    let mutable iterator = 0
    while (iterator < text.Length) do
        if text.Substring(iterator).StartsWith(subtractor) then
            count <- count - 1
        elif text.Substring(iterator).StartsWith(adder) then
            count <- count + 1
        else
            ()
        iterator <- iterator + 1

    adder, subtractor, count

// Finds a string between the first level of the delimiter pairs specified.
// Identifies matching pairs (that is, the string "(())" will match the first opening
// parenthesis with the final closing one)
// If you wish to specify a starting "level" for the search, set startingCount to
// the number of "openings" you want to simulate already having processed
// Returns a tuple composed of:
//      all text until and including the closing delimiter
//      the text inside the opening and closing delimiter
let private findClosingPair pair (text:string) startingCount =
    let adder, subtractor = 
        match pair with
        | Parenthesis -> "(", ")"
        | Brackets -> "{", "}"
        | SquareBrackets -> "[", "]"
        | IfThen -> "if ", " then "
        | ThenElse -> " then ", " else "
        | LetSemicolon -> "let ", ";"
        | TryExcept -> "try ", " except "
        | Custom(t1, t2) -> t1, t2

    let mutable processed, trimmedText = splitSpaces text
    
    let mutable count = startingCount
    let mutable fresh = count = 0
    let mutable inside = ""

    while (fresh || count <> 0) && not (processed.Equals(text)) do
        let chars =
            if text.Substring(processed.Length).StartsWith(subtractor) then
                count <- count - 1
                subtractor.Length
            elif text.Substring(processed.Length).StartsWith(adder) then
                count <- count + 1
                adder.Length
            else
                1

        if not fresh && count > 0 then
            inside <- inside + text.Substring(processed.Length, chars)
        processed <- processed + text.Substring(processed.Length, chars)
        if count <> 0 then
            fresh <- false

    if (count = 0) then
        processed, inside
    elif count < 0 then
        raise (InvalidEntryText ("Missing an opening " + adder))
    else
        raise (InvalidEntryText ("Missing a closing " + subtractor))

//#endregion Utilities

// Avança em text até encontrar algum caractere inválido para nome de variáveis
// Se o nome encontrado for algum texto reservado, lança uma exceção.
// Permite espaços brancos no começo da string
// O retorno da função é uma tupla composto de (espaço em branco+ident, ident)
let private findIdent text = 
    let emptyText, trimmedText = splitSpaces text
    let prohibited = " .,;:+-/*<=>(){}[]?!\\".ToCharArray()
    let ident = String.Concat (trimmedText |> Seq.takeWhile (fun x -> not (Seq.exists ((=) x) prohibited)))
    match ident with
    | "let" | "true" | "false" | "if" | "then" | "else" | "fn" | "letrec"
    | "nil" | "head" | "tail" | "raise" | "try" | "except" | "for" | "in" ->
        raise (InvalidEntryText ("A variable cannot be called " + ident))
    | _ ->
        (emptyText+ident, ident)   

// Recursively find the type information in the input string.
// The string must contain only a type definition (that is, it must end without any
// other characters except for empty spaces)
let rec private findType (text:string) =
    let mutable processed, trimmedText = splitSpaces text
    trimmedText <- trimmedText.TrimEnd()
    let endingSpaces = text.Substring(processed.Length+trimmedText.Length)

    let typ1Text, typ1 = 
        if trimmedText.StartsWith("[") then
            let s, inside = findClosingPair SquareBrackets trimmedText 0
            let _, t = findType inside
            (processed+s+endingSpaces, List(t))
        elif trimmedText.StartsWith("(") then
            let s, inside = findClosingPair Parenthesis trimmedText 0
            let _, t = findType inside
            (processed+s, t)
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
        let emptyText, _ = splitSpaces (text.Substring(processed.Length))
        processed <- processed + emptyText
        if text.Substring(processed.Length).StartsWith("->") then
            processed <- processed + "->"
            let typ2Text, typ2 = text.Substring(processed.Length) |> findType 
            (processed+typ2Text, Function(typ1, typ2))
        else
            raise (InvalidEntryText "Invalid Type information")
           
let rec private findIdTypePair (text:string) =
    let s, id = findIdent text
    
    let emptyText, trimmedText = text.Substring(s.Length) |> splitSpaces
    
    let typ =
        if trimmedText.StartsWith(":") then
            trimmedText.Substring(1) |> findType |> snd |> Some
        else
            None

    (id, typ)

// Receives a string containing parameters and receives a term
// Returns a tuple with:
//  - First parameter id
//  - First parameter type
//  - Return term
//  - Return type
let private parseParameters (paramText: string) returnTerm (returnType: Definition.Type option)  =
    let paramArray = paramText.Split(',') |> Array.map findIdTypePair

    if Array.exists (fun pair -> ((snd pair):Definition.Type option).IsSome) paramArray &&
       Array.forall (fun pair -> ((snd pair):Definition.Type option).IsSome) paramArray |> not then
            InvalidEntryText "Either specify all types or none" |> raise
    else
        if paramArray.Length = 1 then
            (fst paramArray.[0], snd paramArray.[0], returnTerm, returnType)
        else
            let mutable fnTerm = returnTerm
            let mutable fnType = returnType
            for pair in Array.rev paramArray.[1..] do
                fnTerm <- Fn(fst pair, snd pair, fnTerm)
                if fnType.IsSome then
                    fnType <- Function((snd pair).Value, fnType.Value) |> Some
                else
                    ()
            (fst paramArray.[0], snd paramArray.[0], fnTerm, fnType)
            

// Finds an entire Let expression. After the ";", calls findTerms with the remaining text
let rec private findLet text =
    let total, definition = findClosingPair LetSemicolon text 0

    let emptyText, trimmedDefinition = splitSpaces definition
    if trimmedDefinition.StartsWith("rec ") then
        findLetRec text total (trimmedDefinition.Substring("rec ".Length))
    else

        let s, id = findIdent definition
        let mutable processedText = s

        let emptyText, _ = definition.Substring(processedText.Length) |> splitSpaces 
        processedText <- processedText + emptyText
        let trimmedText = definition.Substring(processedText.Length)

        if trimmedText.StartsWith("(") then
            findLetFunction text total trimmedDefinition
        else
            let typ = 
                if trimmedText.StartsWith(":") then
                    try 
                        let s, typeString = findClosingPair (Custom(":", "=")) (definition.Substring(processedText.Length)) 0
                        let _, typ = findType typeString
                        processedText <- processedText + s
                        Some typ
                    with
                    | InvalidEntryText _ -> 
                        InvalidEntryText(sprintf "Must set a type at %A" definition) |> raise
                elif trimmedText.StartsWith("=") then
                    processedText <- processedText + "="
                    None
                else
                    definition |> sprintf "Expected a \"=\" at %A" |> InvalidEntryText |> raise

            let t1 = findTerms (definition.Substring(processedText.Length))
            processedText <- total

            let t2 = findTerms (text.Substring(processedText.Length))

            (text, Let(id, typ, t1, t2))

and private findLetRec (text: string) (total: string) (definition: string) =

    let s, internalIds = findClosingPair Parenthesis definition 0
    
    let s2, id1 = findIdent definition
    
    let mutable remaining = definition.Replace(s.Substring(s2.Length), "")
    let s, externalIds = findClosingPair (Custom("}", "{")) remaining 1
    let id1, typ2 = findIdTypePair externalIds

    remaining <- remaining.Replace(s, "")
    let s, t1String = findClosingPair Brackets remaining 1
    let t1 = findTerms t1String

    let id2, typ1, t1', typ2' = parseParameters internalIds t1 typ2

    let t2 = findTerms (text.Substring(total.Length))

    match typ1, typ2 with
    | None, None | Some _, Some _ -> 
        (text, LetRec(id1, typ1, typ2', id2, t1', t2))
    | _, _ ->  
        InvalidEntryText "You must either specify all types for a function, or none" |> raise

and private findLetFunction (text: string) (total: string) (definition: string) =
    let _, LetRec(id1, typ1, typ2, id2, t1, t2) = findLetRec text total definition

    match typ1, typ2 with
    | None, None ->    
        (text, Let(id1, None, Fn(id2, None, t1), t2))    
    | Some typ1, Some typ2 ->
        (text, Let(id1, Function(typ1, typ2) |> Some, Fn(id2, Some typ1, t1), t2))


and private findFn (text: string) = 
    let mutable processed = "fn"

    let s, idString = findClosingPair Parenthesis (text.Substring(processed.Length)) 0
    processed <- processed + s

    let s, tString = findClosingPair Brackets (text.Substring(processed.Length)) 0
    let t = findTerms tString
    processed <- processed + s

    let id, typ, t1, _ = parseParameters idString t None // Passa qualquer retorno pois não usa

    (processed, Fn(id, typ, t1))

and private findLambda (text: string) =
    let mutable processed = "\\"

    let s, idString = findClosingPair (Custom("\\", "=>")) (text.Substring(processed.Length)) 1
    processed <- processed + s

    let t = findTerms (text.Substring(processed.Length))

    let id, typ, t1, _ = parseParameters idString t None // Passa qualquer retorno pois não usa

    (text, Fn(id, typ, t1))


and private findIf (text: string) =
    let total, t1String = findClosingPair IfThen text 0
    let t1 = findTerms t1String
    let mutable processed = total

    let total, t2String = findClosingPair ThenElse (text.Substring(processed.Length)) 1
    let t2 = findTerms t2String
    processed <- processed + total

    let t3 = text.Substring(processed.Length) |> findTerms

    (text, Cond(t1, t2, t3))

and private findTry (text: string) =
    let total, t1String = findClosingPair TryExcept text 0
    let t1 = findTerms t1String

    let t2 = text.Substring(total.Length) |> findTerms

    (text, Try(t1, t2))


and private findList (text: string) =
    let mutable index = 1
    while [|','; ']'|] |> Seq.exists ((=) (text.Chars(index))) |> not do
        if text.Substring(index).StartsWith("[") then
            let (s:string), _ = findList(text.Substring(index))
            index <- index + (s.Length)
        else
            index <- index + 1
    if text.Chars(index) = ',' then
        let s, t = text.Substring(index) |> findList
        text.Substring(0, index) + s, OP(findTerms (text.Substring(1, index-1)), Cons, t)
    else
        let s = text.Substring(0, index+1)
        let t =
            match index with
            | 1 -> 
                Nil
            | _ -> 
                OP(text.Substring(1, index-1) |> findTerms, Cons, Nil)
        s, t

and private findComprehension (text: string) =
    let mutable compr, inside = findClosingPair SquareBrackets text 0
    try
        let mutable index = 0;
        while index < inside.Length && inside.Substring(index).StartsWith(" for ") |> not do
            if (inside.Substring(index).StartsWith("[")) then
                let s, _ = findClosingPair SquareBrackets (inside.Substring(index)) 0
                index <- index + s.Length
            else
                index <- index + 1

        if index = inside.Length then
            InvalidEntryText "" |> raise

        let t1String = inside.Substring(0, index)
        let t1 = findTerms t1String
        inside <- inside.Substring(index)

        let s, idString = findClosingPair (Custom("for ", " in ")) inside 0
        let _, id = findIdent idString

        let t2String = inside.Substring(s.Length)
        let t2 = findTerms t2String

        let f = Fn(id, None, t1)
        let mapT = 
            Let("f", None, f, 
                Cond(IsEmpty(X("l")), 
                    Nil, 
                    OP(OP(X("f"), Application, Head(X("l"))), Cons, OP(X("map"), Application, Tail(X("l"))))
                ))

        compr, LetRec("map", None, None, "l", mapT, OP(X("map"), Application, t2))
    with
    | InvalidEntryText _ ->
        findList text

// Finds a single term in the input string
// If this function finds a "subterm" (that is, an opening parenthesis), it calls
// findTerms resursively
// Returns a tuple made of (all the processed text, term)
and private findTerm (text: string) =

    let mutable emptyText, trimmedText = splitSpaces text
    
    if trimmedText.StartsWith("let ") then
        let s, t = findLet trimmedText
        (emptyText+s, t)
    elif trimmedText.StartsWith("fn(") || trimmedText.StartsWith("fn ") then
        let s, t = findFn trimmedText
        (emptyText+s, t)
    elif trimmedText.StartsWith("\\") then
        let s, t = findLambda trimmedText
        (emptyText+s, t)
    elif trimmedText.StartsWith("if ") then
        let s, t = findIf trimmedText
        (emptyText+s, t)
    elif trimmedText.StartsWith("try ") then
        let s, t = findTry trimmedText
        (emptyText+s, t)
    elif trimmedText.StartsWith("empty? ") then
        let t = trimmedText.Substring("empty? ".Length) |> findTerms
        (emptyText+trimmedText, IsEmpty(t))
    elif trimmedText.StartsWith("head ") then
        let t = trimmedText.Substring("head ".Length) |> findTerms
        (emptyText+trimmedText, Head(t))
    elif trimmedText.StartsWith("tail ") then
        let t = trimmedText.Substring("tail ".Length) |> findTerms
        (emptyText+trimmedText, Tail(t))
    elif trimmedText.StartsWith("(") then
        let s, subTerm = findClosingPair Parenthesis trimmedText 0
        let s, t = (s, findTerms subTerm)
        (emptyText + s, t)
    elif trimmedText.StartsWith("[") then
        let s, t = findComprehension trimmedText
        (emptyText + s, t)
    elif Char.IsDigit(trimmedText.Chars(0)) then
        let s = trimmedText.ToCharArray()
        let t = s |> Seq.takeWhile (fun x -> Char.IsDigit(x))
        (emptyText+String.Concat(t), I(int (String.Concat(t))))
    elif trimmedText.StartsWith("true") && 
        (trimmedText.Length = 4 || trimmedText.Chars(4) |> Char.IsWhiteSpace) then
        (emptyText+"true", True)
    elif trimmedText.StartsWith("false") && 
        (trimmedText.Length = 5 || trimmedText.Chars(5) |> Char.IsWhiteSpace) then
        (emptyText+"false", False)
    elif trimmedText.StartsWith("raise") && 
        (trimmedText.Length = 5 || trimmedText.Chars(5) |> Char.IsWhiteSpace) then
        (emptyText+"raise", Raise)
    elif trimmedText.StartsWith("nil") &&
        (trimmedText.Length = 3 || trimmedText.Chars(3) |> Char.IsWhiteSpace) then
        (emptyText+"nil", Nil)
    else
        let text, ident = findIdent trimmedText
        (emptyText+text, X(ident))

// Repeatedly calls findTerm to find all terms defined in the input string
// This is needed to deal with the left-associativity of operations
// Returns the finished term (when more than one subterm exists, this is always an OP)
and private findTerms text =
    let text = text.TrimEnd()
    let mutable subText, term = findTerm text

    let mutable termList = [] |> List.toSeq
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
            elif opTrimmed.StartsWith "::" then "::", Cons
            elif opTrimmed.StartsWith "|>" then "|>", Pipe
            else "", Application
        subText <- subText + (opString |> splitSpaces |> fst) + opChar

        termList <- Seq.append termList [|(term, Some op)|]

        let newText, newTerm =
            if op = Cons then
                let rest = text.Substring(subText.Length)
                (rest, findTerms rest)
            else
                findTerm (text.Substring(subText.Length).TrimEnd())
        subText <- subText + newText
        
        term <- newTerm
    termList <- Seq.append termList [|(term, None)|]

    let mutable priority = 0;
    while (operatorsAtPriority priority).Length > 0 do
        let mutable index = 0;
        while termList |> Seq.nth index |> snd |> (=) None |> not do
            let op = (termList |> Seq.nth index |> snd).Value
            if (operatorsAtPriority priority) |> Seq.exists ((=) op) then
                let t1 = termList |> Seq.nth index |> fst
                let t2 = termList |> Seq.nth (index + 1) |> fst

                let nextOp = termList |> Seq.nth (index + 1) |> snd
                termList <- Seq.append (Seq.take index termList)
                    (Seq.append [(OP(t1, op, t2), nextOp)] (Seq.skip (index+2) termList))
                index <- if index = 0 then 0 else index - 1
            else
                index <- index + 1
            let t = termList |> Seq.toArray
            ()
        priority <- priority + 1

    termList |> Seq.nth 0 |> fst

let rec parseTerm (text: String) =
    let mutable text = ["\n"; "\t"; "\r"] |> Seq.fold (fun (acc: String) x -> acc.Replace(x, " ")) text
    text <- text + " "
    let pairs = [Parenthesis;Brackets;SquareBrackets;IfThen;
        ThenElse;LetSemicolon;TryExcept]
    for pair in pairs do
        let opening, closing, count = countPairs pair text
        if count < 0 then
            raise (InvalidEntryText ("There is an extra " + closing))
        elif count > 1 then
            raise (InvalidEntryText ("There is an extra " + opening))
        else
            ()
    findTerms text

//#endregion Parsing