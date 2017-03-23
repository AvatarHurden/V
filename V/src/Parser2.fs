module Parser2

open FParsec
open System.Collections.Generic
open Definition

//#region Helper Types

type extendedOP =
    | Def of Definition.op
    | Custom of string

type Fixity =
    | Prefix of int * func:string
    | Infix of int * Associativity * extendedOP

type OperatorSpec =
    | OpSpec of fix:Fixity * string:string


type UserState = 
    {operators: OperatorSpec list}
    
//#endregion

let ws = spaces

//#region Basic Value Parsing

let pBool = (stringReturn "true"  (B true))
            <|> (stringReturn "false" (B false))

let pNum = puint32 |>> (fun ui -> I <| int(ui))

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

//#endregion

let pTerm, pTermRef = createParserForwardedToRef<term, UserState>()

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

//#region Expression Parsing

let defaultOPs =[
    OpSpec (Infix  (2, Associativity.Left , Def Multiply      ), "*" );
    OpSpec (Infix  (2, Associativity.Left , Def Divide        ), "/" );
     
    OpSpec (Prefix (3,                     "negate"          ), "-" ); 
    OpSpec (Infix  (3, Associativity.Left , Def Add           ), "+" );
    OpSpec (Infix  (3, Associativity.Left , Def Subtract      ), "-" );

    OpSpec (Infix  (4, Associativity.Right, Def Cons          ), "::");

    OpSpec (Infix  (6, Associativity.None , Def LessOrEqual   ), "<=");
    OpSpec (Infix  (6, Associativity.None , Def LessThan      ), "<" );
    OpSpec (Infix  (6, Associativity.None , Def Equal         ), "=" );
    OpSpec (Infix  (6, Associativity.None , Def Different     ), "!=");
    OpSpec (Infix  (6, Associativity.None , Def GreaterThan   ), ">" );
    OpSpec (Infix  (6, Associativity.None , Def GreaterOrEqual), ">=");
 
    OpSpec (Infix  (7, Associativity.Right, Def And           ), "&&");
    OpSpec (Infix  (8, Associativity.Right, Def Or            ), "||")]

let defaultUserState =
    {operators = defaultOPs}

let toOPP x: Operator<term, unit, UserState> = 
    match x with
    | OpSpec (Prefix (pri, func), string) -> 
        upcast PrefixOperator(string, ws, 9-pri, false, fun x -> OP (X func, Application, x))
            : Operator<term, unit, UserState>
    | OpSpec (Infix (pri, assoc, Def op), string) ->
        upcast InfixOperator(string, ws, 9-pri, assoc, fun x y -> OP(x, op, y))
            : Operator<term, unit, UserState>
    | OpSpec (Infix (pri, assoc, Custom op), string) ->
        upcast InfixOperator(string, ws, 9-pri, assoc, fun x y -> OP (OP (X op, Application, x), Application, y))
            : Operator<term, unit, UserState>

let manyApplication p =
  Inline.Many(elementParser = p,
              stateFromFirstElement = (fun x -> x),
              foldState = (fun acc x -> OP(acc, Application, x)),
              resultFromState = (fun acc -> acc))

let getExpressionParser state =
    let operators = state.operators
    let opp = new OperatorPrecedenceParser<term,unit,UserState>()
    let expr = opp.ExpressionParser
    opp.TermParser <- manyApplication (pValue .>> ws)

    for op in operators do
        opp.AddOperator <| toOPP op
    opp.ExpressionParser

do pTermRef := 
    fun stream ->
        let expr = getExpressionParser (stream.UserState)
        (expr .>> ws) stream

let pProgram = ws >>. pTerm .>> eof

let parse text =
    runParserOnString pProgram defaultUserState "" text