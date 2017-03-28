module Parser2

open FParsec
open Definition

//#region Helper Types

type DeclarationContainer =
    | ConstantDeclaration of VarPattern
    | NamedFunctionDeclaration of bool * string * VarPattern list * Type option
    | LambdaDeclaration of VarPattern list

type extendedOP =
    | Def of Definition.op
    | Custom of string

type Fixity =
    | Prefix of int * func:string
    | Infix of int * Associativity * extendedOP

type OperatorSpec =
    | OpSpec of fix:Fixity * string:string


type UserState = 
    {operators: OperatorSpec list;
    identifiersInPattern: Set<string>}
    
//#endregion

let pComment = pstring "//" >>. skipRestOfLine true

let ws = many (spaces1 <|> pComment)

//#region Identifier and Operator Parsing

let keywords = 
    Set["let"; "true"  ; "false"; "if"  ; "then"  ; "else";
        "rec"; "nil"   ; "raise"; "when"; "match" ; "with";
        "try"; "except"; "for"  ; "in"  ; "import"]

let isAsciiIdStart c =
    isAsciiLetter c || c = '_'

let isAsciiIdContinue c =
    isAsciiLetter c || isDigit c || c = '_' || c = '\'' || c = '?'
    

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

let pOperator = many1Chars (anyOf "?!%$&*+-./<=>@^|~") |>>
                    (function
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
                    | c -> Custom c)

let pCustomOperator: Parser<string, UserState> = 
    fun stream ->
        let state = stream.State
        let reply = pOperator stream
        if reply.Status <> Ok then
            Reply(Error, reply.Error)
        else
            match reply.Result with
            | Custom c -> Reply(c)
            | Def _ -> 
                stream.BacktrackTo state
                Reply(Error, unexpected "cannot redefine built-in operators")

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

//#region Type Parsing

let pType, pTypeRef = createParserForwardedToRef<Type, UserState>()

let pIntType = stringReturn "Int" Int
let pBoolType = stringReturn "Bool" Bool
let pCharType = stringReturn "Char" Char
let pStringType = stringReturn "String" (List Definition.Char)

let pParenType = 
    between (pstring "(" >>. ws) (pstring ")" >>. ws)
        <| sepBy1 pType (pstring "," .>> ws) |>> (function | [x] -> x | xs -> Type.Tuple xs)

let pRecordCompType = tuple2 (pIdentifier .>> ws .>> pstring ":" .>> ws) pType

let pRecordType =
    between (pstring "{" >>. ws) (pstring "}" >>. ws) 
        <| sepBy1 pRecordCompType (pstring "," .>> ws) |>> Type.Record

let pListType = between (pstring "[" >>. ws) (pstring "]" >>. ws) pType |>> List

let pTypeValue = choice [pParenType;
                        pRecordType;
                        pIntType;
                        pBoolType;
                        pCharType;
                        pStringType;
                        pListType]

do pTypeRef :=
    let fold ls =
        let rev = List.rev ls
        List.reduce (fun acc x -> Function(x, acc)) rev
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

let pPattern, pPatternRef = createParserForwardedToRef<VarPattern, UserState>()

let pIdentPattern: Parser<VarPattern, UserState> = 
    fun stream ->
        let state = stream.State
        let reply = pIdentifier stream
        if reply.Status <> Ok then
            Reply(Error, reply.Error)
        else 
            let userState = stream.UserState
            let id = reply.Result
            let identifiers = userState.identifiersInPattern
            if not (identifiers.Contains id) then 
                let newIds = identifiers.Add id
                stream.UserState <- {userState with identifiersInPattern = newIds}
                Reply(Pat(XPat id, None))
            else
                stream.BacktrackTo state
                Reply(Error, expected ("identifier (" + id + " is already bound)"))

let pIgnorePattern = stringReturn "_" <| Pat(IgnorePat, None)

let pBoolPattern = (stringReturn "true" <| Pat(BPat true, None))
                    <|> (stringReturn "false" <| Pat(BPat true, None))
let pNumPattern = puint32 |>> fun ui -> Pat(IPat (int ui), None)
let pNilPattern = stringReturn "nil" <| Pat(NilPat, None)

let pCharPattern = pChar |>> function | C c -> Pat(CPat c, None)
let pStringPattern = 
    let convert term =
        let rec t = 
            function
            | OP (C c, Cons, t') -> Pat (ConsPat(Pat (CPat c, None), t t'), None)
            | Nil -> Pat(NilPat, None)
        t term 
    pString |>> convert 

let pParenPattern = 
    between (pstring "(" >>. ws) (pstring ")" >>. ws)
        <| sepBy1 pPattern (pstring "," .>> ws) |>> (function | [x] -> x | xs -> Pat(TuplePat xs, None))

let pRecordCompPattern = tuple2 (pIdentifier .>> ws .>> pstring ":" .>> ws) pPattern

let pRecordPattern =
    between (pstring "{" >>. ws) (pstring "}" >>. ws) 
        <| sepBy1 pRecordCompPattern (pstring "," .>> ws) |>> (fun x -> Pat(RecordPat x, None))

let pListPattern =
    let fold ls =
        let rev = List.rev ls
        List.fold (fun acc p -> Pat (ConsPat(p, acc), None)) (Pat(NilPat, None)) rev

    between (pstring "[" >>. ws) (pstring "]" >>. ws)
        <| sepBy pPattern (pstring "," .>> ws) |>> fold

let pPatternValue = choice [pIgnorePattern;
                            pIdentPattern;
                            pCharPattern;
                            pStringPattern;
                            pBoolPattern;
                            pNumPattern;
                            pNilPattern;
                            pParenPattern;
                            pRecordPattern;
                            pListPattern]

let pConsPattern =
    let reduce ls =
        let rev = List.rev ls
        List.reduce (fun acc p -> Pat (ConsPat(p, acc), None)) rev

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
            | Pat (p, None), typ -> Reply(Pat(p, Some typ))
            | Pat (p, Some _), typ -> 
                stream.BacktrackTo afterFirstState
                Reply(Error, unexpected "repeated type declaration")

//#region Basic Value Parsing

let pBool = (stringReturn "true"  (B true))
            <|> (stringReturn "false" (B false))

let pNum = puint32 |>> fun ui -> I <| int(ui)

let pNil = stringReturn "nil" Nil

let pRaise = stringReturn "raise" Raise

//#endregion   

let pTerm, pTermRef = createParserForwardedToRef<term, UserState>()

//#region Compound Value Parsing (Tuple, Record, List)

let pParen =
    let pTuple = sepBy1 pTerm (pstring "," .>> ws) |>> (function | [x] -> x | xs -> Tuple xs)

    let pPrefixOP = 
        pstring "(" >>. ws >>. pOperator .>> ws .>> pstring ")" .>> ws
            |>> (function
                  | Def op ->
                      Fn(Pat(XPat "x", None), Fn(Pat(XPat "y", None), OP(X "x", op, X "y")))
                  | Custom c ->
                      X c)

    attempt pPrefixOP <|>
        between (pstring "(" >>. ws) (pstring ")" >>. ws) pTuple

let pRecordComp =
    tuple2 (pIdentifier .>> ws .>> pstring ":" .>> ws) pTerm

let pRecord =
    between (pstring "{" >>. ws) (pstring "}" >>. ws) 
        <| sepBy1 pRecordComp (pstring "," .>> ws) |>> Record

let pList =
    let fold ls =
        let rev = List.rev ls
        List.fold (fun acc x -> OP (x, Cons, acc)) Nil rev

    between (pstring "[" >>. ws) (pstring "]" >>. ws)
        <| sepBy pTerm (pstring "," .>> ws) |>> fold

//#endregion

//#region Parse Functions and Declarations

let pParameter =
    let tupled = pParenPattern .>> ws
    let enclosed = (pstring "(" >>. ws >>. pPattern .>> pstring ")" .>> ws)
    let normal = pPatternValue .>> ws
    tupled <|> enclosed <|> normal

let joinParameters letName returnTerm =
    let f p (func, funcType: Type option) = 
        match p with
        | Pat(_, Some typ) when funcType.IsSome ->
            Fn(p, func), Some <| Function(typ, funcType.Value) 
        | Pat (_, _) ->
            Fn(p, func), None
    
    match letName with
    | ConstantDeclaration p -> 
        p, returnTerm
    | LambdaDeclaration parameters ->
        Pat(XPat "", None), fst <| List.foldBack f parameters (returnTerm, None)
    | NamedFunctionDeclaration (isRec, name, [], returnType) -> 
        Pat(XPat name, returnType), returnTerm
    | NamedFunctionDeclaration (isRec, name, parameters, returnType) -> 
        let head = parameters.Head
        let retTerm, retTyp = 
            List.foldBack f parameters.Tail (returnTerm, returnType)

        let fnTyp = 
            match head with
            | Pat(_, Some typ) when retTyp.IsSome -> 
                Some <| Function(typ, retTyp.Value)
            | Pat(_, _) -> None

        if isRec then
            Pat(XPat name, fnTyp), RecFn(name, retTyp, head, retTerm)
        else
            Pat(XPat name, fnTyp), Fn(head, retTerm)

let pLambda: Parser<term, UserState> =
    fun stream ->
        let replyParams = (pstring "\\" >>. ws >>. (many1 pParameter)) stream
        if replyParams.Status <> Ok then
            Reply(Error, replyParams.Error )
        else
            let userState = stream.UserState
            stream.UserState <- {userState with identifiersInPattern = Set[]}
            let replyTerm = (pstring "->" >>. ws >>. pTerm) stream
            if replyTerm.Status <> Ok then
                Reply(Error, replyTerm.Error)
            else
                let (parameters, term) = (replyParams.Result, replyTerm.Result)
                Reply(snd (joinParameters (LambdaDeclaration parameters) term))

let pOperatorName =
    fun stream ->
        let reply = 
            between (pstring "(" >>. ws) (pstring ")" >>. ws)
                (pCustomOperator .>> ws) <| stream
        if reply.Status <> Ok then
            reply
        else
            let userState = stream.UserState
            let name = reply.Result
            let newOp = OpSpec(Infix (9, Associativity.Left, Custom name), name)
            let newOps = newOp :: userState.operators
            stream.UserState <- {userState with operators = newOps}
            reply

let pFunctionName =
    tuple4
        (opt (pstring "rec" >>. ws) |>> (fun x -> x.IsSome))
        ((pIdentifier .>> ws) <|> pOperatorName) 
        (many pParameter)
        (opt (pstring ":" >>. ws >>. pType))
         |>> NamedFunctionDeclaration

let pConstantName =
    pPattern |>> ConstantDeclaration

let pLet: Parser<term, UserState> =
    fun stream ->
        let nameParser =
            (attempt (pConstantName .>> pstring "=")) 
                <|> (pFunctionName .>> pstring "=")
        let reply = pstring "let" >>. ws >>. nameParser <| stream
        if reply.Status <> Ok then
            Reply(Error, reply.Error)
        else
            let name = reply.Result
            let userState = stream.UserState
            stream.UserState <- {userState with identifiersInPattern = Set[]}
            let termReply = 
                (tuple2
                    (ws >>. pTerm)
                    (pstring ";" >>. ws >>. pTerm)) stream
            if termReply.Status <> Ok then
                Reply(Error, termReply.Error)
            else
                let (term1, term2) = termReply.Result
                let p, fn = joinParameters name term1 
                Reply(Let(p, fn, term2))

//#endregion

//#region Parse Branching Expressions

let pIf =
    let first = pstring "if" >>. ws >>. pTerm
    let second = pstring "then" >>. ws >>. pTerm
    let third = pstring "else" >>. ws >>. pTerm
    pipe3 first second third (fun x y z -> Cond(x, y, z))
    
let pTry =
    let first = pstring "try" >>. ws >>. pTerm
    let second = pstring "except" >>. ws >>. pTerm
    pipe2 first second (fun x y -> Try(x, y))

let pMatch = 
    let first = pstring "match" >>. ws >>. pTerm .>> pstring "with" .>> ws
    let triplets = 
        fun stream ->
            let replyPattern = 
                (pstring "|" >>. ws >>. pPattern) <| stream
            if replyPattern.Status <> Ok then
                Reply(Error, replyPattern.Error)
            else
                let userState = stream.UserState
                stream.UserState <- {userState with identifiersInPattern = Set[]}
                let replyRest = 
                    tuple2 
                        (opt (pstring "when" >>. ws >>. pTerm))
                        (pstring "->" >>. ws >>. pTerm) <| stream
                if replyRest.Status <> Ok then
                    Reply(Error, replyRest.Error)
                else
                    let comp1, (comp2, comp3) = replyPattern.Result, replyRest.Result
                    Reply((comp1, comp2, comp3))

    pipe2 first (many1 triplets)
        <| (fun x triplets -> Match(x, triplets))

//#endregion

let pValue = choice [pIdentifier |>> X;
                        pBool;
                        pNum;
                        pNil;
                        pRaise;
                        pChar;
                        pString;
                        pParen;
                        pRecord;
                        pList;
                        pIf;
                        pTry;
                        pMatch;
                        pLambda;
                        pLet]

//#region Expression Parsing

let defaultOPs =[
    OpSpec (Infix  (8, Associativity.Left , Def Multiply      ), "*" );
    OpSpec (Infix  (8, Associativity.Left , Def Divide        ), "/" );
     
    OpSpec (Prefix (7,                     "negate"          ), "-" ); 
    OpSpec (Infix  (7, Associativity.Left , Def Add           ), "+" );
    OpSpec (Infix  (7, Associativity.Left , Def Subtract      ), "-" );

    OpSpec (Infix  (6, Associativity.Right, Def Cons          ), "::");

    OpSpec (Infix  (4, Associativity.None , Def LessOrEqual   ), "<=");
    OpSpec (Infix  (4, Associativity.None , Def LessThan      ), "<" );
    OpSpec (Infix  (4, Associativity.None , Def Equal         ), "=" );
    OpSpec (Infix  (4, Associativity.None , Def Different     ), "!=");
    OpSpec (Infix  (4, Associativity.None , Def GreaterThan   ), ">" );
    OpSpec (Infix  (4, Associativity.None , Def GreaterOrEqual), ">=");
 
    OpSpec (Infix  (3, Associativity.Right, Def And           ), "&&");
    OpSpec (Infix  (2, Associativity.Right, Def Or            ), "||")]

let defaultUserState =
    {operators = defaultOPs;
    identifiersInPattern = Set[]}

let toOPP x: Operator<term, string, UserState> = 
    match x with
    | OpSpec (Prefix (pri, func), string) -> 
        upcast PrefixOperator(string, (notFollowedBy pOperator) >>. ws >>. preturn "", pri, false, fun x -> OP (X func, Application, x))
            : Operator<term, string, UserState>
    | OpSpec (Infix (pri, assoc, Def op), string) ->
        upcast InfixOperator(string, (notFollowedBy pOperator) >>. ws >>. preturn "", pri, assoc, fun x y -> OP(x, op, y))
            : Operator<term, string, UserState>
    | OpSpec (Infix (pri, assoc, Custom op), string) ->
        upcast InfixOperator(string, (notFollowedBy pOperator) >>. ws >>. preturn "", pri, assoc, fun x y -> OP (OP (X op, Application, x), Application, y))
            : Operator<term, string, UserState>

let manyApplication p =
  Inline.Many(elementParser = p,
              stateFromFirstElement = (fun x -> x),
              foldState = (fun acc x -> OP(acc, Application, x)),
              resultFromState = (fun acc -> acc))

let getExpressionParser state =
    let operators = state.operators
    let opp = new OperatorPrecedenceParser<term,string,UserState>()
    let expr = opp.ExpressionParser
    opp.TermParser <- manyApplication (pValue .>> ws)

    for op in operators do
        opp.AddOperator <| toOPP op
    opp.AddOperator (InfixOperator("`", pIdentifier .>> pstring "`" .>> ws, 9, Associativity.Left,
                        (), (fun id x y -> OP (OP (X id, Application, x), Application, y))))
    opp.ExpressionParser

//#endregion

do pTermRef := 
    fun stream ->
        let expr = getExpressionParser (stream.UserState)
        (expr .>> ws) stream

let pProgram = ws >>. pTerm .>> eof

let parse text =
    runParserOnString pProgram defaultUserState "" text