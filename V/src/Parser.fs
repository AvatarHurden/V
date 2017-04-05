module Parser

open FParsec
open Definition
open Compiler

//#region Helper Types

type private DeclarationContainer =
    | ConstantDeclaration of VarPattern
    | NamedFunctionDeclaration of bool * string * VarPattern list * Type option
    | LambdaDeclaration of VarPattern list
    | RecLambdaDeclaration of string * VarPattern list * Type option

type UserState = 
    {operators: OperatorSpec list;
    identifiersInPattern: Set<string>}

    member this.resetIdentifiers = 
        {this with identifiersInPattern = Set[]}

    member this.addIdentifier id =
        let ids = this.identifiersInPattern
        {this with identifiersInPattern = ids.Add id}

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
    OpSpec (Infix  (8, Left , Def Multiply      ), "*" );
    OpSpec (Infix  (8, Left , Def Divide        ), "/" );
     
    OpSpec (Prefix (7,       "negate"          ), "-" ); 
    OpSpec (Infix  (7, Left , Def Add           ), "+" );
    OpSpec (Infix  (7, Left , Def Subtract      ), "-" );

    OpSpec (Infix  (6, Right, Def Cons          ), "::");

    OpSpec (Infix  (4, Non  , Def LessOrEqual   ), "<=");
    OpSpec (Infix  (4, Non  , Def LessThan      ), "<" );
    OpSpec (Infix  (4, Non  , Def Equal         ), "=" );
    OpSpec (Infix  (4, Non  , Def Different     ), "!=");
    OpSpec (Infix  (4, Non  , Def GreaterThan   ), ">" );
    OpSpec (Infix  (4, Non  , Def GreaterOrEqual), ">=");
 
    OpSpec (Infix  (3, Right, Def And           ), "&&");
    OpSpec (Infix  (2, Right, Def Or            ), "||")]

let defaultUserState =
    {operators = defaultOPs;
    identifiersInPattern = Set[]}

//#endregion

let private pComment = pstring "//" >>. skipRestOfLine true

let private ws = many (spaces1 <|> pComment)

let private pBetween s1 s2 p = 
    between (pstring s1 .>> ws) (pstring s2 .>> ws) p

//#region Identifier and Operator Parsing

let keywords = 
    Set["let"; "true"  ; "false"; "if"  ; "then"  ; "else";
        "rec"; "nil"   ; "raise"; "when"; "match" ; "with";
        "try"; "except"; "for"  ; "in"  ; "import"; "infix";
        "infixl"; "infixr"]

let private isAsciiIdStart c =
    isAsciiLetter c || c = '_'

let private isAsciiIdContinue c =
    isAsciiLetter c || isDigit c || c = '_' || c = '\'' || c = '?'
    

let private pIdentifier: Parser<string, UserState> =
    fun stream ->
        let state = stream.State
        let reply = identifier (IdentifierOptions(isAsciiIdStart = isAsciiIdStart,
                                        isAsciiIdContinue = isAsciiIdContinue)) stream
        if reply.Status <> Ok || not (keywords.Contains reply.Result) then 
            reply
        else // result is keyword, so backtrack to before the string
            stream.BacktrackTo(state)
            Reply(Error, expected <| sprintf "identifier ('%O' is a reserved keyword)" reply.Result)

let private pOperator = 
    many1Chars (anyOf "?!%$&*+-./<=>@^|~") |>>
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

let private pCustomOperator: Parser<string, UserState> = 
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

let private pNonEscapeChar quote = satisfy (fun c -> c <> quote && c <> '\\')
let private pEscapeChar = 
    let codes = ['b';  'n';  'r';  't';  '\\'; '"'; '\'']
    let repls = ['\b'; '\n'; '\r'; '\t'; '\\'; '\"'; ''']
    let funEscape code repl = pchar code >>. preturn repl
    pchar '\\' >>. choice (Seq.map2 funEscape codes repls)

let private pChar = 
    between (pstring "\'") (pstring "\'") 
        ((pEscapeChar <|> pNonEscapeChar '\'' <?> "character") |>> C)

let private pString = 
    between (pstring "\"") (pstring "\"") 
        (many ((pEscapeChar <|> pNonEscapeChar '"'))) 
        |>> fun l -> List.foldBack (fun x acc -> OP (C x, Cons, acc)) l Nil

//#endregion   

//#region Type Parsing

let private pType, private pTypeRef = createParserForwardedToRef<Type, UserState>()

let private pIntType = stringReturn "Int" Int
let private pBoolType = stringReturn "Bool" Bool
let private pCharType = stringReturn "Char" Char
let private pStringType = stringReturn "String" (List Definition.Char)

let private pParenType = 
    pBetween "(" ")" (sepBy1 pType (pstring "," .>> ws))
        |>> (function | [x] -> x | xs -> Type.Tuple xs)

let private pRecordCompType = tuple2 (pIdentifier .>> ws .>> pstring ":" .>> ws) pType

let private pRecordType =
    pBetween "{" "}" (sepBy1 pRecordCompType (pstring "," .>> ws)) |>> Type.Record

let private pListType = pBetween "[" "]" pType |>> List

let private pTypeValue = choice [pParenType;
                        pRecordType;
                        pIntType;
                        pBoolType;
                        pCharType;
                        pStringType;
                        pListType]

do pTypeRef :=
    let fold = List.reduceBack (fun x acc -> Function(x, acc))
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

let private pPattern, private pPatternRef = createParserForwardedToRef<VarPattern, UserState>()

let private pIdentPattern: Parser<VarPattern, UserState> = 
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
                stream.UserState <- stream.UserState.addIdentifier id
                Reply(Pat(XPat id, None))
            else
                stream.BacktrackTo state
                Reply(Error, expected ("identifier (" + id + " is already bound)"))

let private pIgnorePattern = stringReturn "_" <| Pat(IgnorePat, None)

let private pBoolPattern = 
        (stringReturn "true" <| Pat(BPat true, None))
            <|> (stringReturn "false" <| Pat(BPat false, None))
let private pNumPattern = puint32 |>> fun ui -> Pat(IPat (int ui), None)
let private pNilPattern = stringReturn "nil" <| Pat(NilPat, None)

let private pCharPattern = 
    pChar |>> 
         function | C c -> Pat(CPat c, None)
                  | _ -> raise <| invalidArg "char" "Parsing char did not return char"
let private pStringPattern = 
    let convert term =
        let rec t = 
            function
            | OP (C c, Cons, t') -> Pat (ConsPat(Pat (CPat c, None), t t'), None)
            | Nil -> Pat(NilPat, None)
            | _ -> raise <| invalidArg "string" "Parsing string did not return string"
        t term 
    pString |>> convert 

let private pParenPattern = 
    pBetween "(" ")" (sepBy1 pPattern (pstring "," .>> ws))
        |>> (function | [x] -> x | xs -> Pat(TuplePat xs, None))

let private pRecordCompPattern = tuple2 (pIdentifier .>> ws .>> pstring ":" .>> ws) pPattern

let private pRecordPattern =
    pBetween "{" "}" (sepBy1 pRecordCompPattern (pstring "," .>> ws))
        |>> (fun x -> Pat(RecordPat x, None))

let private pListPattern =
    pBetween "[" "]" (sepBy pPattern (pstring "," .>> ws)) 
        |>> fun l -> List.foldBack (fun p acc -> Pat (ConsPat(p, acc), None)) l (Pat(NilPat, None))

let private pPatternValue = choice [pIgnorePattern;
                            pIdentPattern;
                            pCharPattern;
                            pStringPattern;
                            pBoolPattern;
                            pNumPattern;
                            pNilPattern;
                            pParenPattern;
                            pRecordPattern;
                            pListPattern]

let private pConsPattern =
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

let private pBool = 
    (stringReturn "true"  (B true))
        <|> (stringReturn "false" (B false))

let private pNum = puint32 |>> fun ui -> I <| int(ui)

let private pNil = stringReturn "nil" Nil

let private pRaise = stringReturn "raise" Raise

let private pProjection = 
    pstring "#" >>. 
        ((puint32 |>> (fun x -> Choice1Of2 (int x)))
        <|> (pIdentifier |>> Choice2Of2)) |>>
        function
        | Choice1Of2 num -> Fn (Pat(XPat "x", None), ProjectIndex (num, X "x"))
        | Choice2Of2 s -> Fn (Pat(XPat "x", None), ProjectName (s, X "x"))

//#endregion   

let private pTerm, private pTermRef = createParserForwardedToRef<term, UserState>()

//#region Parse Functions

let private pParameter =
    let tupled = pParenPattern .>> ws
    let enclosed = pBetween "(" ")" pPattern
    let normal = pPatternValue .>> ws
    tupled <|> enclosed <|> normal

let private joinParameters letName returnTerm =
    let f p (func, funcType: Type option) = 
        match p with
        | Pat(_, Some typ) when funcType.IsSome ->
            Fn(p, func), Some <| Function(typ, funcType.Value) 
        | Pat (_, _) ->
            Fn(p, func), None
    
    let join isRec name (parameters: VarPattern list) returnType = 
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

    match letName with
    | ConstantDeclaration p -> 
        p, returnTerm
    | LambdaDeclaration parameters ->
        Pat(XPat "", None), fst <| List.foldBack f parameters (returnTerm, None)
    | NamedFunctionDeclaration (isRec, name, [], returnType) -> 
        Pat(XPat name, returnType), returnTerm
    | RecLambdaDeclaration (name, parameters, returnType) ->
        join true name parameters returnType
    | NamedFunctionDeclaration (isRec, name, parameters, returnType) -> 
        join isRec name parameters returnType

let private pLambda: Parser<term, UserState> =
    fun stream ->
        let replyParams = (pstring "\\" >>. ws >>. (many1 pParameter)) stream
        if replyParams.Status <> Ok then
            Reply(Error, replyParams.Error )
        else
            stream.UserState <- stream.UserState.resetIdentifiers
            let replyTerm = (pstring "->" >>. ws >>. pTerm) stream
            if replyTerm.Status <> Ok then
                Reply(Error, replyTerm.Error)
            else
                let (parameters, term) = (replyParams.Result, replyTerm.Result)
                Reply(snd (joinParameters (LambdaDeclaration parameters) term))

let private pRecLambda: Parser<term, UserState> =
    fun stream ->
        let replyParams = 
            tuple3 
                (pstring "rec" >>. ws >>. pIdentifier .>> ws) 
                (many1 pParameter)
                (opt (pstring ":" >>. pType)) <| stream
        if replyParams.Status <> Ok then
            Reply(Error, replyParams.Error)
        else 
            stream.UserState <- stream.UserState.resetIdentifiers
            let replyTerm = (pstring "->" >>. ws >>. pTerm) stream
            if replyTerm.Status <> Ok then
                Reply(Error, replyTerm.Error)
            else
                let (parameters, term) = (replyParams.Result, replyTerm.Result)
                Reply(snd (joinParameters (RecLambdaDeclaration parameters) term))

//#endregion

//#region Compound Value Parsing (Tuple, Record, List)

let private pParen =
    let pTuple = sepBy1 pTerm (pstring "," .>> ws) |>> (function | [x] -> x | xs -> Tuple xs)

    let pPrefixOP =
        pBetween "(" ")" (pOperator .>> ws)
            |>> (function
                  | Def op ->
                      Fn(Pat(XPat "x", None), Fn(Pat(XPat "y", None), OP(X "x", op, X "y")))
                  | Custom c ->
                      X c)

    attempt pPrefixOP <|> pBetween "(" ")" pTuple

let private pRecordComp =
    tuple2 (pIdentifier .>> ws .>> pstring ":" .>> ws) pTerm

let private pRecord =
    pBetween "{" "}" (sepBy1 pRecordComp (pstring "," .>> ws)) |>> Record

let private pRange =
    (pipe3 pTerm (opt (pstring "," >>. ws >>. pTerm)) (pstring ".." >>. ws >>. pTerm)) <|
    fun first middle last ->
        match middle with
        | None -> OP (OP (OP (X "range", Application, first), Application, last), Application, I 1)
        | Some num ->
            let increment = OP(num, Subtract, first)
            OP (OP (OP (X "range", Application, first), Application, last), Application, increment)
    
let private pComprehension: Parser<term, UserState> =
    fun stream ->
        let reply = tuple2 (pTerm .>> pstring "for" .>> ws) 
                        (pParameter .>> pstring "in" .>> ws) <| stream
        if reply.Status <> Ok then
            Reply(Error, reply.Error)
        else
            stream.UserState <- stream.UserState.resetIdentifiers
            let reply2 = pTerm stream
            if reply2.Status <> Ok then
                Reply(Error, reply2.Error)
            else
                let (retTerm, pat), source = reply.Result, reply2.Result
                let f = Fn (pat, retTerm)
                Reply(OP (OP (X "map", Application, f), Application, source))

let private pList =
    sepBy pTerm (pstring "," .>> ws) |>> 
    fun l -> List.foldBack (fun x acc -> OP (x, Cons, acc)) l Nil

let private pSquareBrackets =
    pBetween "[" "]" ((attempt pComprehension) <|> (attempt pRange) <|> pList)

//#endregion


//#region Library Parsing

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
                    OpSpec(Infix (prec, assoc, Custom name), name)
                | None ->
                    OpSpec(Infix (9, Left, Custom name), name)
            stream.UserState <- stream.UserState.addOperator newOp
            Reply(name)

let private pFunctionName =
    tuple4
        (opt (pstring "rec" >>. ws) |>> (fun x -> x.IsSome))
        ((pIdentifier .>> ws) <|> pOperatorName) 
        (many pParameter)
        (opt (pstring ":" >>. ws >>. pType))
         |>> NamedFunctionDeclaration

let private pConstantName =
    pPattern |>> ConstantDeclaration

let private pLibComponent: Parser<LibComponent, UserState> =
    fun stream ->
        let nameParser =
            (attempt (pConstantName .>> pstring "=")) 
                <|> (pFunctionName .>> pstring "=")
        let reply = pstring "let" >>. ws >>. nameParser <| stream
        if reply.Status <> Ok then
            Reply(Error, reply.Error)
        else
            let name = reply.Result
            stream.UserState <- stream.UserState.resetIdentifiers
            let termReply = (ws >>. pTerm .>> pstring ";" .>> ws) stream
            if termReply.Status <> Ok then
                Reply(Error, termReply.Error)
            else
                let term1 = termReply.Result
                let p, fn = joinParameters name term1 
                Reply((p, fn))

let private pLibrary =
    fun stream ->
        let reply = ws >>. many1 pLibComponent .>> eof <| stream
        if reply.Status <> Ok then
            Reply(Error, reply.Error)
        else
            let state = stream.UserState
            let terms = reply.Result
            let ops = List.filter (fun op -> not <| List.exists ((=) op) defaultOPs) state.operators
            Reply({terms = terms; operators=ops})

let private pImport: Parser<term, UserState> =
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
                    match runParserOnString pLibrary defaultUserState "" text with
                    | Success(lib, _, _) -> Reply(lib)
                    | Failure(_, error, _) -> 
                        Reply(Error, mergeErrors error.Messages (messageError <| "The error was at library " + reply.Result))
                | :? LibNotFound ->
                    Reply(Error, messageError <| sprintf "Could not find library file at %A" reply.Result)
            if libReply.Status <> Ok then
                Reply(Error, libReply.Error)
            else
                let lib = libReply.Result
                stream.UserState <- stream.UserState.addOperators lib.operators
                pTerm |>> List.foldBack (fun (p, def) acc -> Let(p, def, acc)) lib.terms <| stream

//#endregion

let private pLet: Parser<term, UserState> =
    fun stream ->
        let op = stream.UserState.operators
        let compReply = pLibComponent stream
        if compReply.Status <> Ok then
            Reply(Error, compReply.Error)
        else
            let (p, t1) = compReply.Result
            let t2Reply = pTerm stream
            stream.UserState <- {stream.UserState with operators = op}
            if t2Reply.Status <> Ok then
                Reply(Error, t2Reply.Error)
            else
                Reply(Let(p, t1, t2Reply.Result))

//#endregion

//#region Parse Branching Expressions

let private pIf =
    let first = pstring "if" >>. ws >>. pTerm
    let second = pstring "then" >>. ws >>. pTerm
    let third = pstring "else" >>. ws >>. pTerm
    pipe3 first second third (fun x y z -> Cond(x, y, z))
    
let private pTry =
    let first = pstring "try" >>. ws >>. pTerm
    let second = pstring "except" >>. ws >>. pTerm
    pipe2 first second (fun x y -> Try(x, y))

let private pMatch = 
    let first = pstring "match" >>. ws >>. pTerm .>> pstring "with" .>> ws
    let triplets = 
        fun stream ->
            let replyPattern = 
                (pstring "|" >>. ws >>. pPattern) <| stream
            if replyPattern.Status <> Ok then
                Reply(Error, replyPattern.Error)
            else
                stream.UserState <- stream.UserState.resetIdentifiers
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

let private pValue = choice [pIdentifier |>> X;
                        pBool;
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
                        pTry;
                        pMatch;
                        pLambda;
                        pRecLambda;
                        pLet;
                        pImport]

//#region Expression Parsing

let private manyApplication p =
  Inline.Many(elementParser = p,
              stateFromFirstElement = (fun x -> x),
              foldState = (fun acc x -> OP(acc, Application, x)),
              resultFromState = (fun acc -> acc))

let private toOPP x: Operator<term, string, UserState> = 
    let updateAssoc = 
        function 
        | Left -> Associativity.Left 
        | Right -> Associativity.Right 
        | Non -> Associativity.None
    match x with
    | OpSpec (Prefix (pri, func), string) -> 
        upcast PrefixOperator(string, (notFollowedBy pOperator) >>. ws >>. preturn "", pri, false, fun x -> OP (X func, Application, x))
            : Operator<term, string, UserState>
    | OpSpec (Infix (pri, assoc, Def op), string) ->
        upcast InfixOperator(string, (notFollowedBy pOperator) >>. ws >>. preturn "", pri, updateAssoc assoc, fun x y -> OP(x, op, y))
            : Operator<term, string, UserState>
    | OpSpec (Infix (pri, assoc, Custom op), string) ->
        upcast InfixOperator(string, (notFollowedBy pOperator) >>. ws >>. preturn "", pri, updateAssoc assoc, fun x y -> OP (OP (X op, Application, x), Application, y))
            : Operator<term, string, UserState>

let private getExpressionParser state =
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

let private pProgram = ws >>. pTerm .>> eof

let parseWith (lib: Library) text =
    let state = defaultUserState.addOperators lib.operators
    let res = runParserOnString pProgram state "" text
    match res with
    | Success (a, _, _) -> a |> List.foldBack (fun (p, def) acc -> Let(p, def, acc)) lib.terms
    | Failure (err, _, _) -> raise (ParseException err)

let parse text = parseWith (stdlib.loadCompiled ()) text

let parsePure text =
    let res = runParserOnString pProgram defaultUserState "" text
    match res with
    | Success (a, _, _) -> a
    | Failure (err, _, _) -> raise (ParseException err)

let parseLib text =
    let res = runParserOnString pLibrary defaultUserState "" text
    match res with
    | Failure (err, _, _) -> raise (ParseException err)
    | Success (lib, state, _) -> lib

