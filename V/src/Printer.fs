module Printer

open Definition

//#region Helpers


let rec printTuple printer terms =
    match terms with
    | [] -> ""
    | term :: [] -> printer term
    | term :: rest -> printer term + ", " + printTuple printer rest

and printRecord printer pairs =
    match pairs with
    | [] -> ""
    | (x, term) :: [] -> 
        sprintf "%s: %s" x <| printer term
    | (x, term) :: rest -> 
        sprintf "%s: %s, %s" x (printer term) (printRecord printer rest)
    

//#endregion

let printConstrType constrType =
    match constrType with
    | Int -> "Int"
    | Char -> "Char"
    | Bool -> "Bool"
    | List -> "List"
    | IOType -> "IO"
    | Unit -> "()"
    | ConstructorType.Tuple n -> "Tuple " + string n
    | CustomType s -> s

let printConstructor constr =
    match constr with
    | I i -> string i
    | C c -> string c
    | B b -> string b
    | Cons -> "Cons"
    | Nil -> "Nil"
    | Tuple n -> "Tuple " + string n
    | Void -> "()"
    | IO -> "IO"
    | Custom s -> s

let rec printPatternList (Pat (p, t)) =
    match p with
    | ConstructorPat (Cons, [head; Pat (ConstructorPat (Nil, []), _)]) -> printPattern head
    | ConstructorPat (Cons, [head; tail]) -> printPattern head + ", " + printPatternList tail
    | p -> sprintf "Pattern %A is not list to be printed" p

and printPattern (Pat(pat, typ)) =

    let addSomeType typ s =
        match typ with
        | None -> s
        | Some typ -> sprintf "(%O : %O)" s (printType typ)

    match pat with
    | IgnorePat -> 
        addSomeType typ "_" 
    | XPat x -> 
        addSomeType typ x
    | ConstructorPat (c, pats) -> 
        match c with
        | I _ | C _ | B _ ->  
            addSomeType typ <| printConstructor c
        | Cons -> 
            let isComplete =
                let rec f (Pat (p, _)) =
                    match p with
                    | ConstructorPat (Cons, [_; Pat (ConstructorPat (Nil, []), _)]) -> true
                    | ConstructorPat (Cons, [_; p]) -> f p
                    | _ -> false
                f (Pat (pat, None))
            
            if isComplete then
                addSomeType typ <| "[" + printPatternList (Pat (pat, typ)) + "]"
            else
                match pats with
                | [p1; p2] ->
                    addSomeType typ <| (printPattern p1) + " :: " + (printPattern p2)
                | _ ->
                    sprintf "Printing pattern %A failed" pat |> ParseException |> raise
        | Nil -> 
            addSomeType typ "[]"
        | Tuple n -> 
            addSomeType typ <| "(" + printTuple printPattern pats + ")"
        | Void -> addSomeType typ "()"
        | Custom s -> s
    | RecordPat (partial, fields) -> 
        let t = printRecord printPattern fields
        match partial with
        | true -> "{" + t + ", ... }"
        | false -> "{" + t + "}"

and printSemiPattern p = printPattern (Pat (p, None))    

and printTrait trt =
    match trt with
    | Orderable -> "Orderable"
    | Equatable -> "Equatable"
    | Monad -> "Monad"
    | RecordLabel (label, typ) ->
        sprintf "%O at label %A" (printType typ) label

and printTraits traits =
    match traits with
    | [] -> ""
    | trt :: [] -> printTrait trt
    | trt :: rest -> printTrait trt + ", " + printTraits rest
    
and printType typ =
    match typ with
    | VarType(s, traits) -> 
        match traits with
        | [] -> s
        | _ -> s + " (" + printTraits traits + ")"
    | ConstType (Int, []) -> "Int"
    | ConstType (Bool, []) -> "Bool"
    | ConstType (Char, []) -> "Char"
    | ConstType (List, [ConstType (Char, [])]) -> "String"
    | ConstType (List, [t]) -> sprintf "[%s]" (printType t)
    | ConstType (ConstructorType.Tuple _, types) ->
        sprintf "(%s)" (printTuple printType types)
    | ConstType (Unit, []) -> "()"
    | ConstType (IOType, [t]) -> "IO " + printType t
    | ConstType _ -> sprintf "The type %A is invalid" typ |> TypeException |> raise
    | Accessor (t1, t2) ->
        sprintf "#(%O -> %O)" (printType t1) (printType t2)
    | Function(t1, t2) ->  
        match t1 with
        | Function(_,_) -> 
            sprintf "(%s) -> %s" (printType t1) (printType t2)
        | _ ->
            sprintf "%s -> %s" (printType t1) (printType t2)
    | Type.Record (pairs) ->
        sprintf "{%s}" (printRecord printType pairs)

let rec printResultList result =
    match result with
    | ResConstructor (Cons, [head; ResConstructor (Nil, [])]) -> printResult head
    | ResConstructor (Cons, [head; tail]) -> printResult head + ", " + printResultList tail
    | t -> sprintf "Result %A is not list to be printed" t

and printResultString result =
    match result with
    | ResConstructor (Cons, [ResConstructor (C head, []); ResConstructor (Nil, [])]) -> string head
    | ResConstructor (Cons, [ResConstructor (C head, []); tail]) -> string head + printResultString tail
    | t -> sprintf "Result %A is not list to be printed" t

and printResult result =
    match result with
    | ResConstructor (B true, []) -> "true"
    | ResConstructor (B false, []) -> "false"
    | ResConstructor (C c, []) -> string c
    | ResConstructor (I i, []) -> string i
    | ResRaise -> "raise"
    | ResConstructor (Nil, []) -> "[]"
    | ResConstructor (Cons, [ResConstructor (C head, []); tail]) -> "\"" + printResultString result + "\""
    | ResConstructor (Cons, [head; tail]) -> "[" + printResultList result + "]"
    | ResConstructor (Tuple _, v) -> "(" + printTuple printResult v + ")"
    | ResConstructor (Void, []) -> "()"
    | ResConstructor (IO, [t]) -> "IO " + printResult t
    | ResConstructor _ -> sprintf "The value %A is invalid" result |> EvalException |> raise
    | ResRecordAcess path ->
        let rec f path =
            match path with
            | ResComponent s -> s
            | ResStacked (p1, p2) ->
                sprintf "%O.%O" (f p1) (f p2)
            | ResJoined paths ->
                String.concat ", " <| List.map f paths
            | ResDistorted (p, getter, setter) ->
                sprintf "(%O, %O, %O)" (f p) getter setter
//            | ResLabel s -> sprintf "%O.%O" acc s
//            | ResReadWrite (s, res1, res2) -> 
//                sprintf "%O.(%O, %O, %O)" acc s (printResult res1) (printResult res2)
        //List.fold f "#" paths
        sprintf "#%O" <| f path
    | ResRecord v -> 
        "{" + printRecord printResult v + "}"
    | ResFn (Lambda (id, t), env) ->
        sprintf "Function with parameter %A" id
    | ResFn (Recursive(id, t1, id2, t), env) -> 
        sprintf "Recursive function with name %A and parameter %A" id id2
    | ResPartial (b, _) -> 
        sprintf "Partial application of builtin function %A" b

let parseChar (char: char) =
    ResConstructor (C char, [])

let formatChar (vChar: result) =
    match vChar with
    | ResConstructor (C c, []) -> c
     | t ->
        sprintf "Tried to print %A, but it is not a char" (printResult t) |> EvalException |> raise

let parseString (string: string) =
    let f acc x =
        ResConstructor (Cons, [ResConstructor (C x, []); acc])
    string.ToCharArray () |> Array.rev |> Array.fold f (ResConstructor (Nil, []))

let rec formatString (vString: result) =
    match vString with
    | ResConstructor (Cons, [ResConstructor (C x, []); rest]) ->
        string x + formatString rest
    | ResConstructor (Nil, []) ->
        ""
    | t ->
        sprintf "Tried to print %A, but it is not a string" (printResult t) |> EvalException |> raise
