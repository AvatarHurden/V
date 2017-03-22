module Parser2

open FParsec
open Definition

type UserState = unit

let ws = spaces

//#region Basic Value Parsing

let pBool = (stringReturn "true"  (B true))
            <|> (stringReturn "false" (B false))

let pNum = pint32 |>> (fun ui -> I <| int(ui))

let pNil = (stringReturn "nil" Nil)
            <|> (pstring "[" >>. ws >>. stringReturn "]" Nil)

let pRaise = stringReturn "raise" Raise

//#endregion

//#region String Value Parsing

let pNonEscapeChar quote = satisfy (fun c -> c <> quote && c <> '\\')
let pEscapeChar = 
    let codes = ['b';  'n';  'r';  't';  '\\'; '"'; '\'']
    let repls = ['\b'; '\n'; '\r'; '\t'; '\\'; '\"'; ''']
    let funEscape code repl = pchar code >>. preturn repl
    pchar '\\' >>. choice (Seq.map2 funEscape codes repls)

let pChar = 
    between (pstring "\'") (pstring "\'") 
        ((pEscapeChar <|> pNonEscapeChar '\'' <?> "character") |>> C)

let pString = 
    let fold s =
        let rev = List.rev s
        List.fold (fun acc x -> OP (C x, Cons, acc)) Nil rev

    between (pstring "\"") (pstring "\"") 
        (many ((pEscapeChar <|> pNonEscapeChar '"'))) |>> fold

//#endregion      

//#region Identifier and Operator Parsing

let keywords = 
    Set["let"; "true"  ; "false"; "if"  ; "then"  ; "else";
        "rec"; "nil"   ; "raise"; "when"; "match" ; "with";
        "try"; "except"; "for"  ; "in"  ; "import"]

let isAsciiIdStart c =
    isAsciiLetter c || c = '_'

let isAsciiIdContinue c =
    isAsciiLetter c || isDigit c || c = '_' || c = '\''
    

let pIdentifier: Parser<string, UserState> =
    fun stream ->
        let state = stream.State
        let reply = identifier (IdentifierOptions(isAsciiIdStart = isAsciiIdStart,
                                        isAsciiIdContinue = isAsciiIdContinue)) stream
        if reply.Status <> Ok || not (keywords.Contains reply.Result) then 
            reply
        else // result is keyword, so backtrack to before the string
            stream.BacktrackTo(state)
            Reply(Error, expected <| sprintf "identifier ('%O' is a reserved keyword)" reply.Result)


let manyApplication p =
  // the compiler expands the call to Inline.Many to an optimized sequence parser
  Inline.Many(elementParser = p,
              stateFromFirstElement = (fun x -> x),
              foldState = (fun acc x -> OP(acc, Application, x)),
              resultFromState = (fun acc -> acc))

let pTerm, pTermRef = createParserForwardedToRef<term, unit>()

let pParen =
    between (pstring "(" >>. ws) (pstring ")" >>. ws) 
        <| sepBy1 pTerm (pstring "," .>> ws) |>>
            (function
            | [x] -> x
            | xs -> Tuple xs)

let pRecordComp =
    tuple2 (pIdentifier .>> ws .>> pstring ":" .>> ws) pTerm

let pBrackets =
    between (pstring "{" >>. ws) (pstring "}" >>. ws) 
        <| sepBy1 pRecordComp (pstring "," .>> ws) |>> Record

let pValue = choice [pIdentifier |>> X;
                        pBool;
                        pNum;
                        pNil;
                        pRaise;
                        pChar;
                        pString;
                        pParen;
                        pBrackets]


let opp = new OperatorPrecedenceParser<term,unit,unit>()
let expr = opp.ExpressionParser
let term = manyApplication (pValue .>> ws)
opp.TermParser <- term

opp.AddOperator(InfixOperator("*", ws, 2, Associativity.Left, fun x y -> OP(x, Multiply, y)))
opp.AddOperator(InfixOperator("&&", ws, 7, Associativity.Right, fun x y -> OP(x, And, y)))



do pTermRef := expr .>> ws

let pProgram = ws >>. pTerm .>> eof

let parse text =
    run pProgram text