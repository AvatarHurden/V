module Parser2

open FParsec
open Definition

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
    let codes        = ['b';  'n';  'r';  't';  '\\'; '"'; '\'']
    let replacements = ['\b'; '\n'; '\r'; '\t'; '\\'; '\"'; ''']
    let escapedChar code repl = pchar code >>. preturn repl
    pchar '\\' >>. choice (List.map2 escapedChar codes replacements)

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


let pTerm, pTermRef = createParserForwardedToRef<term, unit>()

do pTermRef := choice [pBool;
                        pNum;
                        pNil;
                        pRaise;
                        pChar;
                        pString]

let parse text =
    run pTerm text