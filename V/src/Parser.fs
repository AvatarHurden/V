module Parser

open FParsec
open Definition
open Translation
open Compiler

//#region Helper Types

type UserState = 
    {operators: OperatorSpec list}

    member this.addOperator op =
        let (OpSpec (fix, name)) = op
        let ops = List.filter (fun (OpSpec (_, s)) -> s <> name) this.operators

        {this with operators = op :: ops}

    member this.addOperators ops =
        let internalF = (fun s (OpSpec (_, name)) -> name <> s)
        let externalF = (fun (OpSpec (_, s)) -> List.forall (internalF s) ops)
        let ops' = List.filter externalF this.operators
        
        {this with operators = ops @ ops'}

let defaultOPs =[
    OpSpec (Infix  (8, Left , BuiltInOp Multiply      ), "*" );
    OpSpec (Infix  (8, Left , BuiltInOp Divide        ), "/" );
     
    OpSpec (Prefix (7,        BuiltInOp Negate        ), "-" ); 
    OpSpec (Infix  (7, Left , BuiltInOp Add           ), "+" );
    OpSpec (Infix  (7, Left , BuiltInOp Subtract      ), "-" );

    OpSpec (Infix  (6, Right, ConstructorOp Cons      ), "::");

    OpSpec (Infix  (4, Non  , BuiltInOp LessOrEqual   ), "<=");
    OpSpec (Infix  (4, Non  , BuiltInOp LessThan      ), "<" );
    OpSpec (Infix  (4, Non  , BuiltInOp Equal         ), "=" );
    OpSpec (Infix  (4, Non  , BuiltInOp Different     ), "!=");
    OpSpec (Infix  (4, Non  , BuiltInOp GreaterThan   ), ">" );
    OpSpec (Infix  (4, Non  , BuiltInOp GreaterOrEqual), ">=");

    OpSpec (Infix  (3, Right, BuiltInOp And           ), "&&");
    OpSpec (Infix  (2, Right, BuiltInOp Or            ), "||")]

let defaultUserState =
    {operators = defaultOPs}

//#endregion

//#region Whitespace and helper Functions

let private pComment = pstring "//" >>. skipRestOfLine true

let private ws = many (spaces1 <|> pComment)

let private pBetween s1 s2 p = 
    between (pstring s1 .>> ws) (pstring s2 .>> ws) p

//#endregion

//#region Identifier and Operator Parsing

let keywords = 
    Set["let" ; "true"  ; "false" ; "if"   ; "then"   ; "else"  ;
        "rec" ; "nil"   ; "raise" ; "when" ; "match"  ; "with"  ;
        "for" ; "in"    ; "import"; "infix"; "infixl" ; "infixr";
        "type"; "alias" ; "get"   ; "_"]

let typeKeywords = Set["Int"; "Bool"; "Char"] 

let private isAsciiIdStart c =
    isAsciiLower c || c = '_'

let private isTypeIdStart c =
    isAsciiUpper c || c = '_'

let private isAsciiIdContinue c =
    isAsciiLetter c || isDigit c || c = '_' || c = '\'' || c = '?'

let private parseIdentifierTemplate start cont (keywords: Set<string>) (stream: CharStream<UserState>) =
    let state = stream.State
    let reply = identifier (IdentifierOptions(isAsciiIdStart = start,
                                    isAsciiIdContinue = cont)) stream
    if reply.Status <> Ok || not (keywords.Contains reply.Result) then 
        reply
    else // result is keyword, so backtrack to before the string
        stream.BacktrackTo(state)
        Reply(Error, unexpected <| sprintf "keyword '%O' is reserved" reply.Result)

let private pIdentifier: Parser<string, UserState> =
    parseIdentifierTemplate isAsciiIdStart isAsciiIdContinue keywords

let private pTypeIdentifier: Parser<string, UserState> =
    parseIdentifierTemplate isTypeIdStart isAsciiIdContinue typeKeywords

let private pOperator = 
    many1Chars (anyOf ":?!%$&*+-./<=>@^|~") |>>
        (function
        | "+" -> BuiltInOp Add
        | "-" -> BuiltInOp Subtract
        | "*" -> BuiltInOp Multiply
        | "/" -> BuiltInOp Divide
        | "<=" -> BuiltInOp LessOrEqual
        | "<" -> BuiltInOp LessThan
        | "=" -> BuiltInOp Equal
        | "!=" -> BuiltInOp Different
        | ">=" -> BuiltInOp GreaterOrEqual
        | ">" -> BuiltInOp GreaterThan
        | "::" -> ConstructorOp Cons
        | c -> CustomOp c)

let private pCustomOperator: Parser<string, UserState> = 
    fun stream ->
        let state = stream.State
        let reply = pOperator stream
        if reply.Status <> Ok then
            Reply(Error, reply.Error)
        else
            match reply.Result with
            | CustomOp c -> Reply(c)
            | ConstructorOp _
            | BuiltInOp _ -> 
                stream.BacktrackTo state
                Reply(Error, unexpected "cannot redefine built-in operators")

//#endregion

//#region String Value Parsing

let private pNonEscapeChar quote = satisfy (fun c -> c <> quote && c <> '\\')
let private pEscapeChar = 
    let codes = ['b';  'n';  'r';  't';  '\\'; '"'; '\'']
    let repls = ['\b'; '\n'; '\r'; '\t'; '\\'; '\"'; ''']
    let funEscape code repl = pchar code >>. preturn repl
    pchar '\\' >>. choice (Seq.map2 funEscape codes repls)

let private pChar = 
    between (pstring "\'") (pstring "\'") 
        ((pEscapeChar <|> pNonEscapeChar '\'' <?> "character") 
            |>> (fun c -> ExConstructor (C c)))

let private pString = 
    between (pstring "\"") (pstring "\"") 
        (many ((pEscapeChar <|> pNonEscapeChar '"'))) 
        |>> fun l -> ExListTerm <| List.map (fun c -> ExConstructor (C c)) l

//#endregion   

//#region Type Parsing

let private pType, private pTypeRef = createParserForwardedToRef<ExType, UserState>()

let private pVarType = pTypeIdentifier |>> ExTypeAlias
let private pIntType = stringReturn "Int" (ExConstType (Int, []))
let private pBoolType = stringReturn "Bool" (ExConstType (Bool, []))
let private pCharType = stringReturn "Char" (ExConstType (Char, []))

let private pParenType = 
    pBetween "(" ")" (sepBy1 pType (pstring "," .>> ws))
        |>> (function | [x] -> x | xs -> ExTupleType xs)

let private pRecordCompType = tuple2 (pIdentifier .>> ws .>> pstring ":" .>> ws) pType

let private pRecordType =
    pBetween "{" "}" (sepBy1 pRecordCompType (pstring "," .>> ws)) |>> ExRecordType

let private pListType = pBetween "[" "]" pType |>> (fun t -> ExConstType (List, [t]))

let private pTypeValue = choice [pVarType;
                        pParenType;
                        pRecordType;
                        pIntType;
                        pBoolType;
                        pCharType;
                        pListType] <?> "type"

do pTypeRef :=
    let fold = List.reduceBack (fun x acc -> ExFunction(x, acc))
    fun stream ->
        let state = stream.State
        let reply = (sepBy1 (pTypeValue .>> ws) 
                        (pstring "->" >>. ws) |>> fold) stream
        if reply.Status <> Ok then
            stream.BacktrackTo state
            (pTypeValue .>> ws) stream
        else
            reply

//#endregion

//#region Pattern Parsing

let private pPattern, private pPatternRef = createParserForwardedToRef<ExVarPattern, UserState>()

let private pIdentPattern = pIdentifier |>> fun id -> (ExXPat id, None)

let private pIgnorePattern = stringReturn "_" <| (ExIgnorePat, None)

let private pBoolPattern = 
        (stringReturn "true" <| (ExConstructorPat (B true, []), None))
            <|> (stringReturn "false" <| (ExConstructorPat (B false, []), None))
let private pNumPattern = pint32 |>> fun ui -> (ExConstructorPat (I ui, []), None)
let private pNilPattern = stringReturn "nil" <| (ExConstructorPat (Nil, []), None)

let private pCharPattern = 
    pChar |>> 
         function | ExConstructor (C c) -> (ExConstructorPat (C c, []), None)
                  | _ -> raise <| invalidArg "char" "Parsing char did not return char"
let private pStringPattern = 
    let convertToPat =
        function
        | ExConstructor (C c) -> (ExConstructorPat (C c, []), None)
        | _ -> raise <| invalidArg "string" "Parsing string did not return string"
    pString |>> function | (ExListTerm l) -> ExListPat <| List.map convertToPat l, None
                         | _ -> raise <| invalidArg "string" "Parsing string did not return string"

let private pParenPattern = 
    pBetween "(" ")" (sepBy1 pPattern (pstring "," .>> ws))
        |>> (function | [x] -> x | xs -> (ExTuplePat xs, None))

let private pRecordCompPattern = tuple2 (pIdentifier .>> ws .>> pstring ":" .>> ws) pPattern

let private pRecord' p f =
    Inline.ManyTill(stateFromFirstElement = (fun x -> [x]),
                     foldState = (fun acc x -> x :: acc),
                     resultFromStateAndEnd = (fun acc allowsExtra -> f acc allowsExtra),
                     elementParser = (pstring "," >>. ws >>. p),
                     endParser = 
                        (attempt (opt (pstring "," >>. ws >>. pstring "..." .>> ws)) 
                            .>> pstring "}" |>> fun x -> x.IsSome),
                     firstElementParser = (pstring "{" >>. ws >>. p))

let private pRecordPattern =
    pRecord' pRecordCompPattern (fun x y -> (ExRecordPat (y, x), None))

let private pListPattern =
    pBetween "[" "]" (sepBy pPattern (pstring "," .>> ws)) 
        |>> fun l -> ExListPat l, None

let private pPatternValue = 
    pIdentPattern <|> 
    (choice [pIgnorePattern;
            pCharPattern;
            pStringPattern;
            pBoolPattern;
            pNumPattern;
            pNilPattern;
            pParenPattern;
            pRecordPattern;
            pListPattern] <?> "pattern")

let private pConsPattern =
    let reduce ls =
        let rev = List.rev ls
        List.reduce (fun acc p -> (ExConstructorPat (Cons, [p; acc]), None)) rev

    sepBy1 (pPatternValue .>> ws) (pstring "::" >>. ws) |>> reduce

do pPatternRef := 
    fun stream ->
        let state = stream.State
        let firstReply = pPatternValue .>> ws <| stream
        let afterFirstState = stream.State
        let secondReply = (pstring ":" >>. ws >>. pType) stream
        if firstReply.Status <> Ok || secondReply.Status <> Ok then
            stream.BacktrackTo state
            pConsPattern stream
        else
            match firstReply.Result, secondReply.Result with
            | (p, None), typ -> Reply((p, Some typ))
            | (p, Some _), typ -> 
                stream.BacktrackTo afterFirstState
                Reply(Error, unexpected "repeated type declaration")

//#region Basic Value Parsing

let private pBool = 
    (stringReturn "true"  (ExConstructor (B true)))
        <|> (stringReturn "false" (ExConstructor (B false)))

let private pNum = puint32 |>> fun ui -> ExConstructor (I <| int(ui))

let private pNil = stringReturn "nil" <| ExConstructor Nil

let private pRaise = stringReturn "raise" ExRaise

let private pProjection = pstring "#" >>. pIdentifier |>> fun s -> ExBuiltIn (RecordAccess s)

let private pGet = pstring "get" >>. ws |>> fun _ -> ExBuiltIn Get

//#endregion   

let private pTerm, private pTermRef = createParserForwardedToRef<ExTerm, UserState>()

//#region Parse Functions

let private pParameter =
    let tupled = pParenPattern .>> ws
    let enclosed = pBetween "(" ")" pPattern
    let normal = pPatternValue .>> ws
    tupled <|> enclosed <|> normal

let private pLambda: Parser<ExTerm, UserState> =
    tuple2 
        (pstring "\\" >>. ws >>. many1 pParameter)
        (pstring "->" >>. ws >>. pTerm) |>> fun x -> ExFn <| ExLambda x

let private pRecLambda: Parser<ExTerm, UserState> =
    tuple4
        (pstring "rec" >>. ws >>. pIdentifier .>> ws) 
        (many1 pParameter)
        (opt (pstring ":" >>. pType))
        (pstring "->" >>. ws >>. pTerm) |>> fun x -> ExFn <| ExRecursive x

//#endregion

//#region Compound Value Parsing (Tuple, Record, List)

let private pParen =
    let pTuple = sepBy1 pTerm (pstring "," .>> ws) |>> (function | [x] -> x | xs -> ExTuple xs)

    let pPrefixOP =
        pBetween "(" ")" (pOperator .>> ws)
            |>> (function
                  | ConstructorOp c -> ExConstructor c
                  | BuiltInOp op -> ExBuiltIn op
                      //ExFn <| ExLambda([(ExXPat "x", None); (ExXPat "y", None)], 
                        //ExOP(ExX "x", op, ExX "y"))
                  | CustomOp c ->
                      ExX c)

    attempt pPrefixOP <|> pBetween "(" ")" pTuple

let private pRecordComp =
    tuple2 (pIdentifier .>> ws .>> pstring ":" .>> ws) pTerm

let private pRecord =
    pBetween "{" "}" (sepBy1 pRecordComp (pstring "," .>> ws)) |>> ExRecord

let private pRange: Parser<ExTerm, UserState> =
    fun stream ->
        let state = stream.State
        let reply = tuple2 pTerm (opt (pstring "," >>. ws >>. pTerm)) <| stream
        if reply.Status <> Ok then
            stream.BacktrackTo state
            Reply(Error, reply.Error)
        else
            let dots = pstring ".." >>. ws <| stream
            if dots.Status <> Ok then
                stream.BacktrackTo state
                Reply(Error, dots.Error)
            else
                let first, middle = reply.Result
                pTerm |>> (fun last -> Range (first, middle, last)) <| stream
    
let private pComprehension: Parser<ExTerm, UserState> =
    tuple3 
        (pTerm .>>? pstring "for" .>> ws) 
        (pParameter .>> pstring "in" .>> ws)
        pTerm |>> Comprehension

let private pList =
    sepBy pTerm (pstring "," .>> ws) |>> ExListTerm

let private pSquareBrackets =
    pBetween "[" "]" (pComprehension <|> pRange <|> pList)

//#endregion


//#region Library Parsing

let private pDecl, private pDeclRef = createParserForwardedToRef<ExDeclaration, UserState>()

let private pOperatorName =
    fun stream ->
        let explicit =
            tuple2
                ((stringReturn "infixl" Left <|> 
                    stringReturn "infixr" Right <|> 
                    stringReturn "infix" Non) .>> ws)
                (anyOf "0123456789" .>> ws |>> (fun x -> int x - int '0'))
        let reply = 
            (tuple2
                (opt explicit)
                (pBetween "(" ")" (pCustomOperator .>> ws))) <| stream
        if reply.Status <> Ok then
            Reply(Error, reply.Error)
        else
            let explicit, name = reply.Result
            let newOp =
                match explicit with
                | Some (assoc, prec) ->
                    OpSpec(Infix (prec, assoc, CustomOp name), name)
                | None ->
                    OpSpec(Infix (9, Left, CustomOp name), name)
            stream.UserState <- stream.UserState.addOperator newOp
            Reply(name)

let private pFunctionDecl =
    tuple5
        (opt (pstring "rec" >>. ws) |>> (fun x -> x.IsSome))
        ((pIdentifier .>> ws) <|> pOperatorName) 
        (many pParameter)
        (opt (pstring ":" >>. ws >>. pType))
        (pstring "=" >>. ws >>. pTerm)
         |>> DeclFunc

let private pConstantDecl =
    tuple2 (pPattern .>> pstring "=" .>> ws) pTerm |>> DeclConst

let private pLibrary =
    fun stream ->
        let reply = ws >>. many1 pDecl .>> eof <| stream
        reply

let parseLibWith text (sourceLib: Library) =
    let state = defaultUserState.addOperators sourceLib.operators
    let res = runParserOnString pLibrary state "" text
    match res with
    | Failure (err, _, _) -> raise (ParseException err)
    | Success (decls, state, _) -> 
        let terms, env = translateLib decls sourceLib.translationEnv
        let ops = List.filter (fun op -> not <| List.exists ((=) op) defaultOPs) state.operators
        {terms = terms; operators=ops; translationEnv = env}

let parseLib text = parseLibWith text <| stdlib.loadCompiled ()

let private pImport: Parser<ExDeclaration, UserState> =
    fun stream ->
        let reply = 
            pstring "import" >>. ws >>.
                (between (pstring "\"") (pstring "\"" .>> ws) 
                    (manyChars ((pEscapeChar <|> pNonEscapeChar '"')))) <| stream
        if reply.Status <> Ok then
            Reply(Error, reply.Error)
        else
            let libReply = 
                try
                    Reply(loadLib reply.Result)
                with
                | UncompiledLib text ->
                    try 
                        Reply(parseLib text)
                    with
                    | ParseException err ->
                        Reply(Error, unexpected err)
                | :? LibNotFound ->
                    Reply(Error, messageError <| sprintf "Could not find library file at %A" reply.Result)
            if libReply.Status <> Ok then
                Reply(Error, libReply.Error)
            else
                let lib = libReply.Result
                stream.UserState <- stream.UserState.addOperators lib.operators
                Reply(DeclImport lib.terms)

let pAlias = 
    tuple2
        (pstring "type" >>. ws >>. pstring "alias" >>. ws >>. pTypeIdentifier .>> ws .>> pstring "=" .>> ws)
        pType |>> DeclAlias

do pDeclRef :=
    let pName = pstring "let" >>. ws >>. ((attempt pConstantDecl) <|> pFunctionDecl)
    (pImport <|> pAlias <|> pName) .>> pstring ";" .>> ws

//#endregion

let private pLet: Parser<ExTerm, UserState> =
    fun stream ->
        let op = stream.UserState.operators
        let compReply = pDecl stream
        if compReply.Status <> Ok then
            Reply(Error, compReply.Error)
        else
            let decl = compReply.Result
            let t2Reply = pTerm stream
            stream.UserState <- {stream.UserState with operators = op}
            if t2Reply.Status <> Ok then
                Reply(Error, t2Reply.Error)
            else
                Reply(ExLet(decl, t2Reply.Result))

//#endregion

//#region Parse Branching Expressions

let private pIf =
    let first = pstring "if" >>. ws >>. pTerm
    let second = pstring "then" >>. ws >>. pTerm
    let third = pstring "else" >>. ws >>. pTerm
    pipe3 first second third (fun x y z -> Cond(x, y, z))
    
let private pMatch = 
    pipe2
        (pstring "match" >>. ws >>. pTerm .>> pstring "with" .>> ws)
        (many1 
            (tuple3 
                (pstring "|" >>. ws >>. pPattern)
                (opt (pstring "when" >>. ws >>. pTerm))
                (pstring "->" >>. ws >>. pTerm))) <|
    fun first triplets -> ExMatch(first, triplets)

//#endregion

let private pValue = 
    pIdentifier |>> ExX <|>
    (choice [pBool;
            pNum;
            pNil;
            pRaise;
            pChar;
            pString;
            pParen;
            pRecord;
            pProjection;
            pSquareBrackets;
            pIf;
            pMatch;
            pLambda;
            pRecLambda;
            pLet;
            pGet] <?> "term")

//#region Expression Parsing

let private manyApplication p =
  Inline.Many(elementParser = p,
              stateFromFirstElement = (fun x -> x),
              foldState = (fun acc x -> ExApp(acc, x)),
              resultFromState = (fun acc -> acc))

let private toOPP x: Operator<ExTerm, string, UserState> = 
    let updateAssoc = 
        function 
        | Left -> Associativity.Left 
        | Right -> Associativity.Right 
        | Non -> Associativity.None
    match x with
    | OpSpec (Prefix (pri, BuiltInOp op), string) ->
        upcast PrefixOperator(string, (notFollowedBy pOperator) >>. ws >>. preturn "", pri, false, fun x -> ExApp (ExBuiltIn op, x))
            : Operator<ExTerm, string, UserState>
    | OpSpec (Prefix (pri, ConstructorOp op), string) ->
        upcast PrefixOperator(string, (notFollowedBy pOperator) >>. ws >>. preturn "", pri, false, fun x -> ExApp (ExConstructor op, x))
            : Operator<ExTerm, string, UserState>
    | OpSpec (Prefix (pri, CustomOp op), string) ->
        upcast PrefixOperator(string, (notFollowedBy pOperator) >>. ws >>. preturn "", pri, false, fun x -> ExApp (ExX op, x))
            : Operator<ExTerm, string, UserState>
    | OpSpec (Infix (pri, assoc, BuiltInOp op), string) ->
        upcast InfixOperator(string, (notFollowedBy pOperator) >>. ws >>. preturn "", pri, updateAssoc assoc, fun x y -> ExApp (ExApp (ExBuiltIn op, x), y))
            : Operator<ExTerm, string, UserState>
    | OpSpec (Infix (pri, assoc, ConstructorOp op), string) ->
        upcast InfixOperator(string, (notFollowedBy pOperator) >>. ws >>. preturn "", pri, updateAssoc assoc, fun x y -> ExApp (ExApp (ExConstructor op, x), y))
            : Operator<ExTerm, string, UserState>
    | OpSpec (Infix (pri, assoc, CustomOp op), string) ->
        upcast InfixOperator(string, (notFollowedBy pOperator) >>. ws >>. preturn "", pri, updateAssoc assoc, fun x y -> ExApp (ExApp (ExX op, x), y))
            : Operator<ExTerm, string, UserState>

let private getExpressionParser state =
    let operators = state.operators
    let opp = new OperatorPrecedenceParser<ExTerm,string,UserState>()
    let expr = opp.ExpressionParser
    opp.TermParser <- manyApplication (pValue .>> ws)

    for op in operators do
        opp.AddOperator <| toOPP op
    opp.AddOperator (InfixOperator("`", pIdentifier .>> pstring "`" .>> ws, 9, Associativity.Left,
                        (), (fun id x y -> ExApp (ExApp (ExX id, x), y))))
    opp.ExpressionParser

//#endregion

do pTermRef := 
    fun stream ->
        let expr = getExpressionParser (stream.UserState)
        (expr .>> ws) stream

let private pProgram = ws >>. pTerm .>> eof

let parseWith (lib: Library) text =
    let state = defaultUserState.addOperators lib.operators
    let res = runParserOnString pProgram state "" text
    match res with
    | Success (a, _, _) -> ExLet(DeclImport(lib.terms), a)
    | Failure (err, _, _) -> raise (ParseException err)

let parse text = parseWith (stdlib.loadCompiled ()) text

let parsePure text =
    let res = runParserOnString pProgram defaultUserState "" text
    match res with
    | Success (a, _, _) -> a
    | Failure (err, _, _) -> raise (ParseException err)

let parseStdlib unit =
    let res = runParserOnString pLibrary defaultUserState "" stdlib.content
    match res with
    | Failure (err, _, _) -> raise (ParseException err)
    | Success (decls, state, _) -> 
        let terms, env = translateLib decls emptyTransEnv
        let ops = List.filter (fun op -> not <| List.exists ((=) op) defaultOPs) state.operators
        {terms = terms; operators=ops; translationEnv = env}

