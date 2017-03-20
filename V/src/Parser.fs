module Parser

open System.Text.RegularExpressions
open Definition
open System
open System.IO
open Compiler
open stdlib
open System.Runtime.Serialization

//#region Helper Types, Modules and Functions

let mutable baseFolder = AppDomain.CurrentDomain.SetupInformation.ApplicationBase
let makeRelative fileName = Path.Combine(baseFolder, fileName)

type associativity =
    | Left
    | Right
    | NonAssociative

type infixOP =
    // Infix operators
    | Def of op
    | Custom of string

type prefixOP =
    | Negate

type extendedTerm =
    | Term of term
    | Infix of infixOP
    | Prefix of prefixOP

let private associativityOf op =
    match op with
    | Custom "@"
    | Custom "$"
    | Custom "."
    | Def Cons
    | Def And
    | Def Or ->
        Right
    | Custom _
    | Def Add
    | Def Subtract
    | Def Multiply
    | Def Divide
    | Custom "%" 
    | Custom "!!"
    | Def Application ->
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
    | Term _ 
    | Infix (Def Application) ->
        0
    | Infix (Custom ".")
    | Infix (Custom "!!") ->
        1
    | Infix (Def Multiply)
    | Infix (Def Divide) 
    | Infix (Custom "%")  ->
        2
    | Prefix Negate
    | Infix (Def Add)
    | Infix (Def Subtract) ->
        3
    | Infix (Def Cons) ->
        4
    | Infix (Custom "@") ->
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
    | Infix (Custom "$") ->
        9
    | Infix (Custom _) ->
        1


type InterfaceElement =
    | IdentifierEl of string
    | OperatorEl of string * priority:int * associativity 

type State = InterfaceElement list
type ParserText = string * int

type ParserResult<'a> =
    | Success of ParserText * State * 'a
    | Failure of position:int * message:string
    
type closings = bool * string list

type ParserInput = ParserText * State * closings



let private splitSpaces term =
    term |> Seq.skipWhile Char.IsWhiteSpace |> String.Concat

let private (|Trimmed|) text =
    splitSpaces text

let private (|Number|_|) text =
    let trimmed = splitSpaces text
    if trimmed.Length > 0 && Char.IsDigit trimmed.[0] then
        let s = trimmed.ToCharArray()
        let num = s |> Seq.takeWhile (fun x -> Char.IsDigit(x)) |> String.Concat
        Some (int num, trimmed.Substring num.Length)
    else
        None

let private (|Operator|_|) acceptDefined text =
    match text with
    | Number rest ->
        None
    | Trimmed rest ->
        let accepted = "?!%$&*+-./<=>@^|~".ToCharArray()
        let opString = String.Concat (rest |> 
                        Seq.takeWhile (fun x -> Seq.exists ((=) x) accepted))

        if String.IsNullOrEmpty opString then
            None
        else
            let op =
                match opString with
                | "+" -> Def Add
                | "-" -> Def Subtract
                | "*" -> Def Multiply
                | "/" -> Def Divide
                | "<=" -> Def LessOrEqual
                | "<" -> Def LessThan
                | "=" -> Def Equal
                | "!=" -> Def Different
                | ">=" -> Def GreaterOrEqual
                | ">" -> Def GreaterThan
                | "::" -> Def Cons
                | "&&" -> Def And
                | "||" -> Def Or
                | c -> Custom c
        
            if not acceptDefined then
                match op with
                | Custom c -> Some (op, opString, rest.Substring opString.Length)
                | op -> None
            else
                Some (op, opString, rest.Substring opString.Length)

let private (|Identifier|_|) text =
    match text with
    | Number rest ->
        None
    | Trimmed rest when rest.Length > 0 ->
        let prohibited = Array.toList <| " `_.,;:+-/*<=>(){}[]%$&|!@#\\'\"\n\r\t".ToCharArray()
        let firstProhibited = '?' :: prohibited

        if Seq.exists ((=) (rest.Chars 0)) firstProhibited then
            None
        else
            let ident = String.Concat (rest.Substring 1 |> 
                            Seq.takeWhile (fun x -> not <| Seq.exists ((=) x) prohibited))
            let ident = Char.ToString (rest.Chars 0) + ident
            match ident with
            | "let" | "true" | "false" | "if" | "then" | "else" 
            | "rec"| "nil" | "raise"  | "when"
            | "skip" | "output" | "input" | "match" | "with"
            | "try" | "except" | "for" | "in" | "import" ->
                None
            | "" ->
                None
            | _ ->
                Some (ident, rest.Substring ident.Length)
    | _ -> None
    
type Start =
    | Space
    | EndOfString
    | S of string

let rec private matchStart (text: string) matches =
    match matches with
    | [] -> 
        None
    | Space :: rest when Char.IsWhiteSpace (text.Chars 0) ->
        Some (Space, text)
    | EndOfString :: rest when (splitSpaces text).Length = 0 ->
        Some (EndOfString, text)
    | S x :: rest when (splitSpaces text).StartsWith(x) ->
        Some (S x, splitSpaces text)
    | _ :: rest ->
        matchStart text rest
            
let private (|AnyStart|_|) (starts: bool * Start list) (text: string) =
    match matchStart text <| snd starts with
    | None -> None
    | Some (S start, text) ->
        if fst starts then
            Some (text.Substring start.Length, S start)
        else
            Some (text, S start)
    | Some (start, text) ->
        Some (splitSpaces text, start)
        
// If string starts with 'start' (after removing any leading whitespace),
// returns the remaining string after removing 'start' (and whitespace)
let private (|Start|_|) start text =
    let trimmed = splitSpaces text
    if trimmed.StartsWith start then
        Some <| trimmed.Substring start.Length
    else
        None

let private raiseExp x = raise <| ParseException x

let rec parseMultipleComponents f text closings =
    match text with
    | AnyStart closings (t, start) ->
        t, []
    | Trimmed rest -> 
        let removedFirst, ret = f rest (false, snd closings @ [S ","])

        let rest =
            match removedFirst with
            | Start "," rest -> rest
            | _ -> removedFirst

        let removedRest, restPairs = parseMultipleComponents f rest closings
        removedRest, ret :: restPairs 

//#endregion
           
//#region Value Parsing

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

//#region Identifier and Type Functions

let parseIdent text = 
    match text with
    | Identifier (ident, rest) ->
        rest, ident
    | Trimmed rest ->
        raiseExp <| sprintf "Did not find a valid identifier at %A" text

let parseOperator text acceptDefined = 
    match text with
    | Operator acceptDefined (op, opString, rest) ->
        rest, op, opString
    | Trimmed rest ->
        raiseExp <| sprintf "Did not find a valid operator at %A" text

let rec parseType text closings =
    let remainingText, typ1 = 
        match text with
        | Start "(" rest ->
            parseTupleType rest (true, [S ")"])
        | Start "{" rest ->
            parseRecordType rest (true, [S "}"])
        | Start "[" rest ->
            let remaining, t = parseType rest (true, [S "]"])
            remaining, List t
        | Start "Int" rest ->
            rest, Int
        | Start "Bool" rest ->
            rest, Bool
        | Start "Char" rest ->
            rest, Definition.Char
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

and parseRecordTypeComponent text closings =
    let rest, label = parseIdent text
    let rest, typ = 
        match rest with
        | Start ":" rest ->
            parseType rest closings
        | _ -> 
            raiseExp <| sprintf "Expected %A, but found %A" closings rest
    rest, (label, typ)

and parseTupleType text closings =
    let rest, pairs = 
        parseMultipleComponents parseType text closings
    match pairs with
    | [] -> raiseExp <| sprintf "Tuple type must contain at least 2 components at %A" text
    | [typ] -> rest, typ
    | _ -> 
        rest, Type.Tuple pairs
    
and parseRecordType text closings =
    let rest, pairs =
        parseMultipleComponents parseRecordTypeComponent text closings
    match pairs with
    | [] -> raiseExp <| sprintf "Record type must contain at least 1 component at %A" text
    | _ ->  
        rest, Type.Record pairs
        
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

let rec parsePattern text closings = 
    let rest, value = parsePatternValue text closings
    match rest with
    | AnyStart closings (rest, start) ->
        rest, value
    | Start "::" rest ->
        let rest, value2 = parsePattern rest closings
        let rest, typ = 
            match rest with
            | ":" -> parseSomeType rest closings
            | AnyStart closings (rest, start) -> rest, None
            | Trimmed rest ->
                raiseExp <| sprintf "Could not parse pattern at %A" rest
        rest, Pat(ConsPat(value, value2), typ)
    | Start ":" rest ->
        let rest, typ = parseSomeType rest closings
        match value with
        | Pat(p, None) ->
            rest, Pat(p, typ)
        | Pat(p, Some typ') ->
            raiseExp <| sprintf "Cannot declare type twice for pattern at %A" text
    | Trimmed rest ->
        raiseExp <| sprintf "Expected \"%A\" at %A" closings rest

and parsePatternValue text closings = 
    match text with
    | Identifier (id, rest) -> rest, Pat(XPat id, None)
    | Number (n, rest) -> rest, Pat(IPat n, None)
    | Start "true" rest -> rest, Pat(BPat true, None)
    | Start "false" rest -> rest, Pat(BPat false, None)
    
    | Start "'" rest ->
        let rest, term = parseChar rest
        match term with
        | C c -> rest, Pat(CPat c, None)
        | _ -> raiseExp <| sprintf "ParseChar didn't return a char at %A" text

    | Start "\"" rest ->
        let rest, term = parseString rest
        let rec iter t =
            match t with
            | OP (C c, Cons, t') ->
                Pat (ConsPat(Pat (CPat c, None), iter t'), None)
            | Nil ->
                Pat(NilPat, None)
            | _ ->
                raiseExp <| sprintf "ParseString didn't return a string at %A" text
        let pat = iter term
        rest, pat

    | Start "_" rest -> rest, Pat(IgnorePat, None)
    | Start "nil" rest -> rest, Pat(NilPat, None)
    | Start "(" rest ->
        let rest, pairs = parseMultipleComponents parsePattern rest (true, [S ")"])
        match pairs with
        | [] -> raiseExp <| sprintf "Invalid pattern at %A" text
        | [p] -> rest, p
        | _ -> rest, Pat(TuplePat pairs, None)
    | Start "{" rest ->
        let rest, pairs = parseMultipleComponents parseRecordPattern rest (true, [S "}"])
        match pairs with
        | [] -> raiseExp <| sprintf "Invalid pattern at %A" text
        | _ -> rest, Pat(RecordPat pairs, None)
    | Start "[" rest ->
        let rest, pairs = parseMultipleComponents parsePattern rest (true, [S "]"])
        match pairs with
        | [] -> rest, Pat(NilPat, None)
        | _ -> 
            rest, List.fold (fun acc p -> Pat (ConsPat(p, acc), None)) (Pat(NilPat, None)) pairs
    | Trimmed rest ->
        raiseExp <| sprintf "No pattern to parse at %A" rest

and parseRecordPattern text closings =
    let rest, label = parseIdent text
    let rest, pattern = 
        match rest with
        | Start ":" rest ->
            parsePattern rest closings
        | _ -> 
            raiseExp <| sprintf "Expected %A, but found %A" closings rest
    rest, (label, pattern)

let rec parseParameters text closings = 
    match text with
    | AnyStart closings (rest, start) ->
        rest, []
    | Trimmed rest ->
        let rest, curParameter = parsePattern rest (false, Space :: snd closings)
        let rest, otherParameters = parseParameters rest closings
        rest, curParameter :: otherParameters

// Returns a tuple of (p, (term, type2), where
// p: pattern of first paremeter
// term: return term of function
// type2: return type of function
let rec joinMultiParameters parameters returnTerm returnType =
    match parameters with
    | [] ->
        raiseExp "Must pass at least one parameter"
    | (Pat _ as p) :: [] -> 
        p, (returnTerm, returnType)
    | _ ->
        let seq = parameters |> List.toSeq
        let p = Seq.last seq
        let (Pat(p', typ)) = p
        let newParams = seq |> Seq.take (parameters.Length - 1) |> Seq.toList
        let newType = 
            match typ, returnType with
            | Some t1, Some t2 ->
                Some <| Function (t1, t2)
            | _, _ ->
                None
        joinMultiParameters newParams (Fn (p, returnTerm)) newType
        
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
            raise (ParseException <| sprintf "Prefix %A cannot be preceded by a term" Negate)
        | _ ->
            raiseExp <| sprintf "Prefix %A must be followed by a term" Negate
    | Prefix Negate ->
        match prev with
        | Some _ ->
            raise (ParseException <| sprintf "Prefix %A cannot be preceded by a term" Negate)
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
                | Custom s -> OP (OP (X s, Application, x), Application, y)
            condenseTerms None (Term <| term) rest priority
        | _ ->
            raiseExp <| sprintf "Infix %A must be surrounded by terms" op
    | Infix op ->
        match prev, nexts with
        | Some (Term x), head :: tail ->
            [Term x; current] @ condenseTerms None head tail priority
        | _ ->
            match op with
            | Def op ->
                raiseExp <| sprintf "Infix %A must be surrounded by terms" op
            | op ->
                raiseExp <| sprintf "Infix %A must be surrounded by terms" op

let rec unifyTerms (terms: extendedTerm list) = 
    let priorities = 
            Seq.map (fun x -> priorityOf x) terms |>
            Seq.distinct |>
            Seq.sort
    let func = fun (acc: extendedTerm List) x -> condenseTerms None acc.Head acc.Tail x
    let terms = Seq.fold func terms priorities
    if terms.Length = 1 then
        match terms.Head with
        | Term t -> t
        | Prefix _ -> raiseExp "Cannot unify to a prefix"
        | Infix _ -> raiseExp "Cannot unify to a infix"
    else
        raiseExp "Unification resulted in more than one term"
         

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

    let rest, finalTerm = parseTerm remaining (false, snd closings)

    let pathName = 
        if not <| Path.HasExtension libname then
            if Path.ChangeExtension(libname, "vl") |> makeRelative |> File.Exists then
                Path.ChangeExtension(libname, "vl") |> makeRelative
            elif Path.ChangeExtension(libname, "v") |> makeRelative |> File.Exists then
               Path.ChangeExtension(libname, "v") |> makeRelative
            else
                raiseExp <| sprintf "Could not find library file at %A" libname
        else
            if libname |> makeRelative |> File.Exists then
                libname        
            else
                raiseExp <| sprintf "Could not find library file at %A" libname

    try
        let libContent = loadLib (makeRelative pathName) finalTerm
        rest, libContent
    with
    | :? SerializationException ->
        let content = makeRelative pathName |> IO.File.ReadAllText

        parseTerm (removeComments content + " " + remaining) (false, snd closings)


//#endregion

//#region Term parsing        

and parseMatchComponents text closings =
    match text with
    | AnyStart closings (t, start) ->
        t, []
    | Start "|" rest ->
        let rest, patter = parsePattern rest (false, [S "when"; S "->"])
        let rest, cond = 
            match rest with
            | Start "when" rest ->
                let rest, cond = parseTerm rest (true, [S "->"])
                rest, Some cond
            | Start "->" rest ->
                rest, None
        let rest, ret = parseTerm rest (false, S "|" :: snd closings)
        let single = (patter, cond, ret)
        let rest, components = parseMatchComponents rest closings
        rest, single :: components
    | Trimmed rest ->
        rest, []

and parseMatch text closings =
    let rest, t1 = parseTerm text (true, [S "with"])

    let rest, patterns = parseMatchComponents rest (false, snd closings)

    if patterns.Length = 0 then
        raiseExp <| sprintf "Match expression requires at least one pattern at %A" text
    else
        rest, Match (t1, patterns)

and parseLet text closings = 
    let isRec, start =
        match text with
        | Start "rec" rest ->
            true, rest
        | Trimmed rest ->
            false, rest
    
    let rest, pattern, parameters = 
        try
            let rest, pattern = parsePattern start (false, [S "="])
            rest, pattern, []
        with
        | _ ->
            match start with
            | Identifier (id, rest) ->
                let rest, parameters = parseParameters rest (false, [S "="; S ":"])
                rest, Pat(XPat id, None), parameters
            | Start "(" rest ->
                let rest, op, opString = parseOperator rest false
                match rest with
                | Start ")" rest ->
                    let rest, parameters = parseParameters rest (false, [S "="; S ":"])
                    rest, Pat(XPat opString, None), parameters
                | Trimmed rest ->
                    raiseExp <| sprintf "Expected closing parenthesis at %A" rest
            | Trimmed rest ->
                raiseExp <| sprintf "Expected identifier at %A" rest

    let rest, retType =
        match rest with
        | Start ":" rest -> parseSomeType rest (true, [S "="])
        | Start "=" rest -> rest, None
        | _ -> raiseExp "Expected a \"=\" at %A" text

    let rest, retTerm = parseTerm rest (true, [S ";"])
    let rest, t2 = parseTerm rest (false, snd closings)
    
    match isRec, parameters with
    | false, [] ->
        rest, Let(pattern, retTerm, t2)
    | false, _ ->
        let id =
            match pattern with
            | Pat (XPat id, None) -> id
            | _ ->
                raiseExp "Functions cannot be named with a pattern at %A" text
        let p, (retTerm, retType) = joinMultiParameters parameters retTerm retType
        let (Pat(p', typ1)) = p
        let fn = Fn(p, retTerm)
        match retType, typ1 with
        | Some retType, Some typ1 ->
            rest, Let(Pat(XPat id, Some <| Function(typ1, retType)), fn, t2)
        | _ ->
            rest, Let(pattern, fn, t2)
    | true, _ ->
        let id =
            match pattern with
            | Pat (XPat id, None) -> id
            | _ ->
                raiseExp "Recursive functions cannot be named with a pattern at %A" text
        let p, (retTerm, retType) = joinMultiParameters parameters retTerm retType
        let (Pat(p', typ1)) = p
        let recFn = RecFn(id, retType, p, retTerm)
        match recFn with
        | RecFn(id, Some retType, Pat (p, Some typ1), retTerm) ->
            rest, Let(Pat(XPat id, Some <| Function(typ1, retType)), recFn, t2)
        | RecFn(id, None, p, retTerm) ->
            rest, Let(pattern, recFn, t2)
        | _ -> raiseExp <| sprintf "Wrong recurive function at %A" text

and parseRecFunction text closings =
    let rest, id = parseIdent text
    let rest, parameters = parseParameters rest (false, [S "->"; S ":"])
    let rest, retType =
        match rest with
        | Start ":" rest -> parseSomeType rest (true, [S "->"])
        | Start "->" rest -> rest, None
        | _ -> raiseExp "Expected a \"->\" at %A" text
    let rest, retTerm = parseTerm rest closings
    
    let p, (retTerm, retType) = joinMultiParameters parameters retTerm retType

    rest, RecFn(id, retType, p, retTerm)

and parseLambda text closings =
    let rest, parameters = parseParameters text (true, [S "->"])
    let rest, retTerm = parseTerm rest (false, snd closings)

    // A function does not need a return type, but I must know if the
    // parameters have a type so that joining them will not cause an error
    let (Pat (_, firstType)) = parameters.Head
    let p, (retTerm, _) = 
        joinMultiParameters parameters retTerm firstType

    rest, Fn(p, retTerm)

and parseIf text closings =
    let rest, t1 = parseTerm text (true, [S "then"])
    let rest, t2 = parseTerm rest (true, [S "else"])
    let rest, t3 = parseTerm rest (false, snd closings)
   
    rest, Cond(t1, t2, t3)

and parseTry text closings =
    let rest, t1 = parseTerm text (true, [S "except"])
    let rest, t2 = parseTerm rest (false, snd closings)

    rest, Try(t1, t2)

and parseList text closings =
    match text with
    | Start "]" rest -> rest, Nil
    | Trimmed rest ->
        let rest, t = parseTerm rest (false, [S ","; S ".."; S "for"; S "]"])
        match rest with
        | Start "," rest -> 
            let rest, t2 = parseTerm rest (false, [S ","; S ".."; S "]"])
            match rest with
            | Start ".." rest -> parseRange text closings
            | Trimmed rest -> parseMultiList text closings
        | Start ".." rest -> parseRange text closings
        | Start "for" rest -> parseComprehension text closings
        | Start "]" rest -> rest, OP(t, Cons, Nil) 
        | Trimmed rest -> raiseExp <| sprintf "Expected \",\" at %A" rest

and parseMultiList text closings =
    let rest, t = parseTerm text (false, [ S ","; S "]"])
    match rest with
    | Start "," rest -> 
        let rest, t2 = parseMultiList rest closings
        rest, OP(t, Cons, t2) 
    | Start "]" rest -> 
        rest, OP(t, Cons, Nil) 
    | Trimmed rest ->
        raiseExp <| sprintf "Expected \"]\" at %A" rest

and parseComprehension text closings =
    let rest, t1 = parseTerm text (true, [S "for"])
    let rest, p = parsePattern rest (false, [S " "; S "in"])
    let rest, t2 = 
        match rest with
        | Start "in" rest -> parseTerm rest (true, [S "]"])
        | _ -> raiseExp <| sprintf "Expected \"in\" at %A" rest

    let f = Fn(p, t1)
    rest, OP (OP (X "map", Application, f), Application, t2)

and parseRange text closings = 
    let rest, first = parseTerm text (false, [S ","; S ".."])
    let rest, increment =
        match rest with
        | Start "," rest -> 
            let rest, second = parseTerm rest (true, [S ".."])
            rest, OP(second, Subtract, first)
        | Start ".." rest -> rest, I 1
        | Trimmed rest -> raiseExp <| sprintf "Expected \"..\" at %A" rest
    let rest, last = parseTerm rest (true, [S "]"])
    
    rest, OP (OP (OP (X "range", Application, first), Application, last), Application, increment)

//#region Record/Tuple parsing

and parseRecordComponent text closings =
    let rest, label = parseIdent text
    let rest, term = 
        match rest with
        | Start ":" rest ->
            parseTerm rest closings
        | _ -> 
            raiseExp <| sprintf "Expected %A, but found %A" closings rest
    rest, (label, term)

and parseRecord text closings =
    let rest, pairs =
        parseMultipleComponents parseRecordComponent text closings
    match pairs with
    | [] -> raiseExp <| sprintf "Record must contain at least 1 component at %A" text
    | _ ->  
        rest, Record pairs
        
and parseParenthesis text closings =
    let rest, pairs = 
        parseMultipleComponents (fun x y -> collectTerms x y false) text closings
    match pairs with
    | [] -> raiseExp <| sprintf "Tuple must contain at least 2 components at %A" text
    | [terms] -> 
        match terms with
        | [Infix op] ->
            match op with
            | Def op ->
                rest, Fn(Pat(XPat "x", None), Fn(Pat(XPat "y", None), OP(X "x", op, X "y"))) 
            | Custom s -> rest, X s
        | [Prefix Negate] ->
            rest, Fn(Pat(XPat "x", None), Fn(Pat(XPat "y", None), OP(X "x", Subtract, X "y")))
        | _ -> rest, unifyTerms terms
    | _ -> 
        rest, term.Tuple <| List.map unifyTerms pairs
        
and parseProjection (text: string) closings =
    if Char.IsWhiteSpace text.[0] then
        raiseExp <| sprintf "Incomplete projection expression"
    else
        match text with
        | Number (num, rest) ->
            rest, Fn (Pat(XPat "x", None), ProjectIndex (num, X "x"))
        | Trimmed rest ->
            let rest, label = parseIdent rest
            rest, Fn (Pat(XPat "x", None), ProjectName (label, X "x"))

//#endregion

and addToTerms string extendedTerm closings =
    let isTerm =
        match extendedTerm with
        | Term t -> true
        | _ -> false
    let rem, rest = collectTerms string closings isTerm
    rem, extendedTerm :: rest

// Iterate through the string, collecting single terms and operators
and collectTerms text closings isAfterTerm = 
    match text with
    | Identifier (ident, rest) ->
        addToTerms rest (Term <| X ident) closings
    | AnyStart closings (t, start) ->
        t, []
    | Start "`" rest ->
        let rest, id = parseIdent rest
        if rest.Chars 0 <> '`' then
            raiseExp <| sprintf "Expected ` at %A" text
        addToTerms (rest.Substring 1) (Infix <| Custom id) closings
    | Start "(" rest ->
        let rest, term = parseParenthesis rest (true, [S ")"])
        addToTerms rest (Term term) closings
    | Start "{" rest ->
        let rest, term = parseRecord rest (true, [S "}"])
        addToTerms rest (Term term) closings
    // Matching value terms
    | Number (num, rest) ->
        addToTerms rest (Term <| I num) closings
    | Start "true" rest ->
        addToTerms rest (Term <| B true) closings
    | Start "false" rest ->
        addToTerms rest (Term <| B false) closings
    | Start "raise" rest ->
        addToTerms rest (Term Raise) closings
    | Start "nil" rest ->
        addToTerms rest (Term Nil) closings
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
    | Start "match" rest ->
        let rem, term = parseMatch rest closings
        addToTerms rem (Term term) closings
    | Start "rec" rest ->
        let rem, term = parseRecFunction rest closings
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
    | Operator true (op, opString, rest) ->
        match op with
        | Def Subtract when not isAfterTerm ->
            addToTerms rest (Prefix Negate) closings
        | _ ->
            addToTerms rest (Infix op) closings
    // List cons is special, since : is not allowed in operators
    | Start "::" rest ->
        addToTerms rest (Infix <| Def Cons) closings
    | Start "#" rest ->
        let rest, term = parseProjection rest closings
        addToTerms rest (Term term) closings
    | _ when (snd closings).IsEmpty ->
        "", []
    | _ ->
        raiseExp <| sprintf "Expected \"%A\" at %A" closings text

   
// Calls collectTerms and unify, testing if the return is a term
and parseTerm text closings = 
    let rem, collected = collectTerms text closings false
    if collected.Length = 0 then
        raiseExp <| sprintf "Must have at least one term to process at %A" text
    rem, unifyTerms collected

let parse text =
    let rem, t = parseTerm (removeComments text) (true, [EndOfString])
    let complete = stdlib.loadCompiled t
    if rem.Length > 0 then
        raiseExp "Something went very wrong with parsing"
    else
        complete

let parsePure text =
    let rem, t = parseTerm (removeComments text) (true, [EndOfString])
    if rem.Length > 0 then
        raiseExp "Something went very wrong with parsing"
    else
        t