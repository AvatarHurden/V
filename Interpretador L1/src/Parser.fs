module Parser

open System.Text.RegularExpressions
open Definition
open System
open stdlib

//#region Helper Types, Modules and Functions

module Path =
    let appDir = AppDomain.CurrentDomain.SetupInformation.ApplicationBase
    let makeAppRelative fileName = System.IO.Path.Combine(appDir, fileName)

exception InvalidEntryText of string

type associativity =
    | Left
    | Right
    | NonAssociative

type infixOP =
    // Infix operators
    | Def of op
    | Apply
    | Compose
    | Index
    | Remainder
    | Concat

type prefixOP =
    | Negate

type extendedTerm =
    | Term of term
    | Infix of infixOP
    | Prefix of prefixOP

let private associativityOf op =
    match op with
    | Concat
    | Apply
    | Compose
    | Def Cons
    | Def And
    | Def Or ->
        Right
    | Def Add
    | Def Subtract
    | Def Multiply
    | Def Divide
    | Remainder 
    | Index
    | Def Application 
    | Def Sequence ->
        Left
    | Def Equal
    | Def Different
    | Def GreaterOrEqual
    | Def GreaterThan
    | Def LessOrEqual
    | Def LessThan ->
        NonAssociative

let private priorityOf op =
    match op with        
    | Infix (Def Application) ->
        0
    | Infix Compose
    | Infix Index ->
        1
    | Infix (Def Multiply)
    | Infix (Def Divide) 
    | Infix Remainder ->
        2
    | Prefix Negate
    | Infix (Def Add)
    | Infix (Def Subtract) ->
        3
    | Infix (Def Cons) ->
        4
    | Infix Concat ->
        5
    | Infix (Def LessOrEqual)
    | Infix (Def LessThan)
    | Infix (Def Equal)
    | Infix (Def Different)
    | Infix (Def GreaterThan)
    | Infix (Def GreaterOrEqual) ->
        6
    | Infix (Def And) ->
        7
    | Infix (Def Or) ->
        8
    | Infix (Def Sequence) ->
        9
    | Infix Apply ->
        10

type closings = bool * string list

let private splitSpaces term =
    term |> Seq.skipWhile Char.IsWhiteSpace |> String.Concat

let rec private matchStart (text: string) matches =
    match matches with
    | [] -> 
        false, ""
    | x::rest when text.StartsWith(x) ->
        true, x
    | x::rest ->
        matchStart text rest

let private (|Number|_|) text =
    let trimmed = splitSpaces text
    if trimmed.Length > 0 && Char.IsDigit(trimmed.[0]) then
        Some trimmed
        else
        None
    
let private (|AnyStart|_|) starts text =
    let trimmed = splitSpaces text
    let doesStart, start = matchStart trimmed <| snd starts
    if doesStart then
        if fst starts then
            Some (trimmed.Substring start.Length, start)
        else
            Some (trimmed, start)
    else
        None
        
// If string starts with 'start' (after removing any leading whitespace),
// returns the remaining string after removing 'start' (and whitespace)
let private (|Start|_|) start text =
    let trimmed = splitSpaces text
    if trimmed.StartsWith start then
        Some <| trimmed.Substring start.Length
        else
            None

let private (|Trimmed|) text =
    splitSpaces text

let private raiseExp x = raise <| InvalidEntryText x

//#endregion
            
//#region Identifier and Type Functions

let parseIdent text = 
    match text with
    | Number rest ->
        raiseExp "An identifier cannot begin with a digit"
    | Trimmed rest ->
        let prohibited = " .,;:+-/*<=>(){}[]%$&|!@\\'\"\n\r\t".ToCharArray()
        let ident = String.Concat (rest |> 
                        Seq.takeWhile (fun x -> not <| Seq.exists ((=) x) prohibited))
        match ident with
        | "let" | "true" | "false" | "if" | "then" | "else" 
        | "fn" | "rec"| "nil" | "head" | "tail" | "raise" 
        | "skip" | "output" | "input"
        | "try" | "except" | "for" | "in" | "empty?" | "import" ->
            raiseExp <| sprintf "A variable cannot be called %A at %A" ident text
        | "" ->
            raiseExp <| sprintf "Cannot declare an empty identifier at %A" text
        | _ ->
            rest.Substring(ident.Length), ident

let rec parseType text closings =
    let remainingText, typ1 = 
        match text with
        | Start "(" rest ->
            parseType rest (true, [")"])
        | Start "[" rest ->
            let remaining, t = parseType rest (true, ["]"])
            remaining, List t
        | Start "Int" rest ->
            rest, Int
        | Start "Bool" rest ->
            rest, Bool
        | Start "Char" rest ->
            rest, Definition.Char
        | Start "Unit" rest ->
            rest, Unit
        | Start "String" rest ->
            rest, List Definition.Char
        | Trimmed rest ->
            raiseExp <| sprintf "Could not parse type at %A" rest

    match remainingText with
    | AnyStart closings (t, start) ->
        t, typ1
    | Start "->" rest ->
        let remaining, typ2 = parseType rest closings
        remaining, Function (typ1, typ2)
    | _ -> 
        raiseExp <| sprintf "Could not parse type at %A" remainingText
        
let parseSomeType text closings =
    let rest, typ = parseType text closings
    rest, Some typ

let rec parseIdentTypePair text closings =
    let typeString, id = parseIdent text

    let rest, typ =
        match typeString with
        | AnyStart closings (t, start) -> t, None
        | Start ":" rest -> parseSomeType rest closings
        | _ -> raiseExp <| sprintf "Expected %A, but found %A" closings typeString

    rest, (id, typ)

let rec parseParameters text closings =
    match text with
    | AnyStart closings (t, start) ->
        t, []
    | Trimmed rest -> 
        let removedFirst, (id, typ) = parseIdentTypePair rest (false, snd closings @ [","])

        let nextParameterText =
            match removedFirst with
            | Start "," rest -> rest
            | _ -> removedFirst

        let removedRest, restPairs = parseParameters nextParameterText closings
        removedRest, [id, typ] @ restPairs 

// Returns a tuple of ((id, type1), (term, type2), where
// id: Ident of first parameter
// type1: Type of first parameter
// term: return term of function
// type2: return type of function
let rec joinMultiParameters parameters returnTerm returnType =
    match parameters with
    | [] ->
        raiseExp "Must pass at least one parameter"
    | (id, typ)::[] -> 
        match typ, returnType with
        | None, None
        | Some _, Some _ ->
            (id, typ), (returnTerm, returnType)
        | _ ->
            raiseExp "Either specify all types or none"
    | _ ->
        let seq = parameters |> List.toSeq
        let id, typ = Seq.last seq
        let newParams = seq |> Seq.take (parameters.Length - 1) |> Seq.toList
        let newType = 
            match typ, returnType with
            | None, None ->
                    None
            | Some t1, Some t2 ->
                Some <| Function (t1, t2)
            | _ ->
                raiseExp "Either specify all types or none"
        joinMultiParameters newParams (Fn (id, typ, returnTerm)) newType
        
let rec parseStringLiteral (text: string) closing =
    match text.ToCharArray() |> Array.toList with
    | [] ->
        raiseExp <| sprintf "Could not find closing %A" closing
    | '\\'::tail ->
        let current = 
            match tail with
            | 'n'::rest -> "\n"
            | 'b'::rest -> "\b"
            | 'r'::rest  -> "\r"
            | 't'::rest -> "\t"
            | '\\'::rest -> "\\"
            | '"'::rest -> "\""
            | '\''::rest -> "'"
            | _ ->
                raiseExp <| sprintf "Invalid escaped char at %A" text
        let remaining, parsed = parseStringLiteral (String.Concat tail.Tail) closing
        remaining, current + parsed
    | t::tail when t = closing -> 
        text, ""
    | t::tail ->
        let remaining, parsed = parseStringLiteral (String.Concat tail) closing
        remaining, t.ToString() + parsed

//#endregion

//#region Unifying

let rec condenseTerms prev current nexts priority =
    match current with
    | Term x ->
        match nexts with
        | [] -> [Term x]
        | Term y :: rest -> 
            condenseTerms prev (Term <| OP (x, Application, y)) rest priority
        | t :: rest ->
            condenseTerms (Some current) t rest priority
    | Prefix Negate when priorityOf current = priority ->
        match prev, nexts with
        | None, Term y :: rest ->
            let term = OP (X "negate", Application, y)
            condenseTerms prev (Term term) rest priority
        | Some _, _ ->
            raise (InvalidEntryText <| sprintf "Prefix %A cannot be preceded by a term" Negate)
        | _ ->
            raiseExp <| sprintf "Prefix %A must be followed by a term" Negate
    | Prefix Negate ->
        match prev with
        | Some _ ->
            raise (InvalidEntryText <| sprintf "Prefix %A cannot be preceded by a term" Negate)
        | None ->
            [current] @ condenseTerms None nexts.Head nexts.Tail priority
    | Infix op when priorityOf current = priority ->
        let actualNexts =
            match associativityOf op with
            | Right ->
                match nexts with
                | cur :: Infix op2 :: rest when op2 = op ->
                    condenseTerms None cur nexts.Tail priority
                | _ ->
                    nexts
            | Left | NonAssociative ->
                nexts
        match prev, actualNexts with
        | Some (Term x), Term y :: rest ->
            let term = 
                match op with
                | Def op -> OP (x, op, y)
                | Remainder -> OP (OP (X "remainder", Application, x), Application, y)
                | Concat -> OP (OP (X "concat", Application, x), Application, y)
                | Apply -> OP(x, Application, y)
                | Compose -> Fn ("x", None, OP (x, Application, OP (y, Application, X "x")))
                | Index -> OP (OP (X "nth", Application, y), Application, x) 
            condenseTerms None (Term <| term) rest priority
        | _ ->
            raiseExp <| sprintf "Infix %A must be surrounded by terms" op
    | Infix op ->
        match prev with
        | Some (Term x) ->
            [Term x; current] @ condenseTerms None nexts.Head nexts.Tail priority
        | _ ->
            raiseExp <| sprintf "Infix %A must be preceded by a term" op

// Iterate through list of (Term, Operator), joining into one Term
let rec unifyTerms (terms: extendedTerm list) priority = 
    if terms.Length = 1 then
        match terms.Head with
        | Term t -> t
        | Prefix _ -> raiseExp "Cannot unify to a prefix"
        | Infix _ -> raiseExp "Cannot unify to an infix"
    else
        unifyTerms (condenseTerms None terms.Head terms.Tail priority) (priority + 1)

//#endregion
    
//#region Value Parsing

let parseChar text =
    let remaining, c = parseStringLiteral text '\''

    if not <| remaining.StartsWith "'" then
        raiseExp <| sprintf "Missing closing ' for char literal at %A" text

    if c.Length = 0 then
        raiseExp <| sprintf "A char literal cannot be empty at %A" text
    elif c.Length > 1 then
        raiseExp <| sprintf "A char literal must have length 1 at %A" text

    remaining.Substring 1, C c.[0]

let parseString text =
    let remaining, s = parseStringLiteral text '"'

    if not <| remaining.StartsWith "\"" then
        raiseExp <| sprintf "Missing closing \" for string literal at %A" text

    let revArray = s.ToCharArray() |> Array.rev
    let ret = Array.fold (fun acc x -> OP (C x, Cons, acc)) Nil revArray

    remaining.Substring 1, ret

//#endregion

//#region Extensions Parsing

let removeComments (text: string) =
    let lines = text.Split('\n') |> Array.toSeq
    let lines = Seq.map (fun (x:string) -> x.Split([|"//"|], StringSplitOptions.None).[0]) lines
    Seq.reduce (fun acc x -> acc + "\n" + x) lines

let rec parseImport text closings =
    let remaining, libname = 
        match text with
        | Start "\"" rest ->
            let rem, name = parseStringLiteral rest '"'
            rem.Substring 1, name
        | _ ->
            raiseExp <| sprintf "Must have a string literal at %A" text

    let libContent =
        let pathName = 
            if not <| libname.EndsWith ".l1" then
                libname + ".l1"
            else
                libname        
        if Path.makeAppRelative libname |> IO.File.Exists then
            Path.makeAppRelative libname |> IO.File.ReadAllText
        else
            raiseExp <| sprintf "Could not find library file at %A" libname

    parseTerm (removeComments libContent + " " + remaining) (false, snd closings)

//#endregion

//#region Term parsing        

and parseLet text closings =
    match text with
    | Start "rec" rest ->
        parseLetRec rest closings
    | _ ->
        let rest, id = parseIdent text
        match rest with
        | Start "(" rest ->
            parseNamedFunction text closings
        | _ ->
            parseLetDefinition text closings

and parseLetDefinition text closings =
    let rest, id = parseIdent text
    let rest, typ =
        match rest with
        | Start ":" rest -> parseSomeType rest (true, ["="])
        | Start "=" rest -> rest, None
        | _ -> raiseExp <| sprintf "Expected a \"=\" at %A" text
    let rest, t1 = parseTerm rest (true, [";"])
    let rest, t2 = parseTerm rest (false, snd closings)
    rest, Let(id, typ, t1, t2)

and parseLetRec text closings =
    let rest, recFn = parseRecFunction text closings
    let rest =
        match rest with
        | Start ";" rest -> rest
        | _ -> raiseExp <| sprintf "Expected a \";\" at %A" text
    let rest, t2 = parseTerm rest (false, snd closings)

    match recFn with
    | RecFn (id, Some retType, id2, Some paramTyp, t1) ->
        rest, Let(id, Some <| Function(paramTyp, retType), recFn, t2)
    | RecFn (id, None, id2, None, t1) ->
        rest, Let(id, None, recFn, t2)
    | _ -> raiseExp <| sprintf "Wrong recurive function at %A" text

and parseNamedFunction text closings =
    let rest, t = parseLetRec text closings
    
    match t with
    | Let (_, None, RecFn (id1, None, id2, None, t1), t2) ->
        rest, Let (id1, None, Fn (id2, None, t1), t2)
    | Let (_, Some typ, RecFn (id1, Some typ1, id2, Some typ2, t1), t2) ->
        rest, Let (id1, Some typ, Fn (id2, Some typ2, t1), t2)
    | _ ->
        raiseExp <| sprintf "Wrong named function declaration at %A" text

and parseRecFunction text closings =
    let rest, id = parseIdent text
    let rest, parameters =
        match rest with
        | Start "(" rest -> parseParameters rest (true, [")"])
        | _ -> raiseExp <| sprintf "Expected a \"(\" at %A" text
    let rest, retType =
        match rest with
        | Start ":" rest -> parseSomeType rest (true, ["{"])
        | Start "{" rest -> rest, None
        | _ -> raiseExp "Expected a \"{\" at %A" text
    let rest, retTerm = parseTerm rest (true, ["}"])
    
    let (id2, typ1), (retTerm, retType) = joinMultiParameters parameters retTerm retType

    rest, RecFn(id, retType, id2, typ1, retTerm)

and parseFunction text closings =
    let rest, parameters =
        match text with
        | Start "(" rest -> parseParameters rest (true, [")"])
        | _ -> raiseExp <| sprintf "Expected a \"(\" at %A" text
    let rest, retTerm =
        match rest with
        | Start "{" rest -> parseTerm rest (true, ["}"])
        | _ -> raiseExp <| sprintf "Expected a \"{\" at %A" text

    // A function does not need a return type, but I must know if the
    // parameters have a type so that joining them will not cause an error
    let (paramId, paramTyp), (retTerm, _) = 
        joinMultiParameters parameters retTerm <| snd parameters.Head

    rest, Fn(paramId, paramTyp, retTerm)

and parseLambda text closings =
    let rest, parameters = parseParameters text (true, ["=>"])
    let rest, retTerm = parseTerm rest (false, snd closings)

    // A function does not need a return type, but I must know if the
    // parameters have a type so that joining them will not cause an error
    let (paramId, paramTyp), (retTerm, _) = 
        joinMultiParameters parameters retTerm <| snd parameters.Head

    rest, Fn(paramId, paramTyp, retTerm)

and parseIf text closings =
    let rest, t1 = parseTerm text (true, ["then"])
    let rest, t2 = parseTerm rest (true, ["else"])
    let rest, t3 = parseTerm rest (false, snd closings)
   
    rest, Cond(t1, t2, t3)

and parseTry text closings =
    let rest, t1 = parseTerm text (true, ["except"])
    let rest, t2 = parseTerm rest (false, snd closings)

    rest, Try(t1, t2)

and parseList text closings =
    match text with
    | Start "]" rest -> rest, Nil
    | Trimmed rest ->
        let rest, t = parseTerm rest (false, [",";"..";"for";"]"])
        match rest with
        | Start "," rest -> 
            let rest, t2 = parseTerm rest (false, [",";"..";"]"])
            match rest with
            | Start ".." rest -> parseRange text closings
            | Trimmed rest -> parseMultiList text closings
        | Start ".." rest -> parseRange text closings
        | Start "for" rest -> parseComprehension text closings
        | Start "]" rest -> rest, OP(t, Cons, Nil) 
        | Trimmed rest -> raiseExp <| sprintf "Expected \",\" at %A" rest

and parseMultiList text closings =
    let rest, t = parseTerm text (false, [",";"]"])
    match rest with
    | Start "," rest -> 
        let rest, t2 = parseMultiList rest closings
        rest, OP(t, Cons, t2) 
    | Start "]" rest -> 
        rest, OP(t, Cons, Nil) 
    | Trimmed rest ->
        raiseExp <| sprintf "Expected \"]\" at %A" rest

and parseComprehension text closings =
    let rest, t1 = parseTerm text (true, ["for"])
    let rest, id = parseIdent rest
    let rest, t2 = 
        match rest with
        | Start "in" rest -> parseTerm rest (true, ["]"])
        | _ -> raiseExp <| sprintf "Expected \"in\" at %A" rest

    let f = Fn(id, None, t1)
    rest, OP (OP (X "map", Application, f), Application, t2)

and parseRange text closings = 
    let rest, first = parseTerm text (false, [",";".."])
    let rest, increment =
        match rest with
        | Start "," rest -> 
            let rest, second = parseTerm rest (true, [".."])
            rest, OP(second, Subtract, first)
        | Start ".." rest -> rest, I 1
        | Trimmed rest -> raiseExp <| sprintf "Expected \"..\" at %A" rest
    let rest, last = parseTerm rest (true, ["]"])
    
    rest, OP (OP (OP (X "range", Application, first), Application, last), Application, increment)

and addToTerms string extendedTerm closings =
    let isTerm =
        match extendedTerm with
        | Term t -> true
        | _ -> false
    let rem, rest = collectTerms string closings isTerm
    rem, extendedTerm :: rest

// Iterate through the string, collecting single terms and operators
and collectTerms text closings isAfterTerm = 
        try
        let rem, id = parseIdent text
        addToTerms rem (Term <| X id) closings
        with
        | InvalidEntryText t ->
        match text with
        | AnyStart closings (t, start) ->
            t, []
        | Start "(" rest ->
            let rem, term = parseTerm rest (true, [")"])
            addToTerms rem (Term term) closings
        // Matching value terms
        | Number rest ->
            let s = rest.ToCharArray()
            let num = s |> Seq.takeWhile (fun x -> Char.IsDigit(x)) |> String.Concat
            addToTerms (rest.Substring num.Length) (Term <| I (int num)) closings
        | Start "true" rest ->
            addToTerms rest (Term True) closings
        | Start "false" rest ->
            addToTerms rest (Term False) closings
        | Start "raise" rest ->
            addToTerms rest (Term Raise) closings
        | Start "nil" rest ->
            addToTerms rest (Term Nil) closings
        | Start "skip" rest ->
            addToTerms rest (Term Skip) closings
        | Start "\"" rest ->
            let rem, term = parseString rest
            addToTerms rem (Term term) closings
        | Start "'" rest ->
            let rem, term = parseChar rest
            addToTerms rem (Term term) closings
        // Matching normal terms
        | Start "import" rest ->
            let rem, term = parseImport rest closings
            addToTerms rem (Term term) closings
        | Start "let" rest ->
            let rem, term = parseLet rest closings
            addToTerms rem (Term term) closings
        | Start "rec" rest ->
            let rem, term = parseRecFunction rest closings
            addToTerms rem (Term term) closings
        | Start "fn" rest ->
            let rem, term = parseFunction rest closings
            addToTerms rem (Term term) closings
        | Start "\\" rest ->
            let rem, term = parseLambda rest closings
            addToTerms rem (Term term) closings
        | Start "if" rest ->
            let rem, term = parseIf rest closings
            addToTerms rem (Term term) closings
        | Start "try" rest ->
            let rem, term = parseTry rest closings
            addToTerms rem (Term term) closings
        | Start "[" rest ->
            let rem, term = parseList rest closings
            addToTerms rem (Term term) closings
        | Start "input" rest ->
            addToTerms rest (Term Input) closings
        // Matching prefix operators
        | Start "-" rest when not isAfterTerm ->
            addToTerms rest (Prefix Negate) closings
        | Start "empty?" rest ->
            addToTerms rest 
                (Term <| Fn ("x", None, IsEmpty <| X "x")) closings
        | Start "head" rest ->
            addToTerms rest 
                (Term <| Fn ("x", None, Head <| X "x")) closings
        | Start "tail" rest ->
            addToTerms rest 
                (Term <| Fn ("x", None, Tail <| X "x")) closings
        | Start "output" rest ->
            addToTerms rest 
                (Term <| Fn ("x", None, Output <| X "x")) closings
        // Matching infix operators
        | Start "!!" rest ->
            addToTerms rest (Infix Index) closings  
        | Start "%" rest ->
            addToTerms rest (Infix Remainder) closings        
        | Start "@" rest ->
            addToTerms rest (Infix Concat) closings
        | Start "+" rest ->
            addToTerms rest (Infix <| Def Add) closings
        | Start "-" rest when isAfterTerm ->
            addToTerms rest (Infix <| Def Subtract) closings
        | Start "*" rest ->
            addToTerms rest (Infix <| Def Multiply) closings
        | Start "/" rest ->
            addToTerms rest (Infix <| Def Divide) closings
        | Start "<=" rest ->
            addToTerms rest (Infix <| Def LessOrEqual) closings
        | Start "<" rest ->
            addToTerms rest (Infix <| Def LessThan) closings
        | Start "=" rest ->
            addToTerms rest (Infix <| Def Equal) closings
        | Start "!=" rest ->
            addToTerms rest (Infix <| Def Different) closings
        | Start ">=" rest ->
            addToTerms rest (Infix <| Def GreaterOrEqual) closings
        | Start ">" rest ->
            addToTerms rest (Infix <| Def GreaterThan) closings
        | Start ";" rest ->
            addToTerms rest (Infix <| Def Sequence) closings
        // Right associative operators
        | Start "$" rest ->
            addToTerms rest (Infix Apply) closings
        | Start "." rest ->
            addToTerms rest (Infix Compose) closings
        | Start "::" rest ->
            addToTerms rest (Infix <| Def Cons) closings
        | Start "&&" rest ->
            addToTerms rest (Infix <| Def And) closings
        | Start "||" rest ->
            addToTerms rest (Infix <| Def Or) closings
        | _ when (snd closings).IsEmpty ->
            "", []
        | _ ->
            raiseExp <| sprintf "Expected \"%A\" at %A" closings text

   
// Calls collectTerms and unify, testing if the return is a term
and parseTerm text closings = 
    let rem, collected = collectTerms text closings false
    if collected.Length = 0 then
        raiseExp <| sprintf "Must have at least one term to process at %A" text
    rem, unifyTerms collected 0

let parse text =
    let rem, t = parseTerm (removeComments <| stdlib.content + text) (true, [])
    if rem.Length > 0 then
        raiseExp "Something went very wrong with parsing"
    else
        t

let parsePure text =
    let rem, t = parseTerm (removeComments <| text) (true, [])
    if rem.Length > 0 then
        raiseExp "Something went very wrong with parsing"
    else
        t