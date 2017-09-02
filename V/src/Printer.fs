module Printer

open Definition

let rec printTrait trt =
    match trt with
    | Orderable -> "Orderable"
    | Equatable -> "Equatable"
    | RecordLabel (label, typ) ->
        sprintf "%O at label %A" (printType typ) label

and printTraits traits =
    match traits with
    | [] -> ""
    | trt :: [] -> printTrait trt
    | trt :: rest -> printTrait trt + ", " + printTraits rest

and printTuple types =
    match types with
    | [] -> ""
    | typ :: [] -> printType typ
    | typ :: rest -> printType typ + ", " + printTuple rest
    
and printRecord pairs =
    match pairs with
    | [] -> ""
    | (x, typ) :: [] -> 
        sprintf "%s: %s" x <| printType typ
    | (x, typ) :: rest -> 
        sprintf "%s: %s, %s" x (printType typ) (printRecord rest)

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
        sprintf "(%s)" (printTuple types)
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
        sprintf "{%s}" (printRecord pairs)

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
    | ResConstructor (Tuple _, v) -> 
        "(" + 
        (List.fold (fun acc v -> acc + ", " + printResult v) 
        (printResult v.Head) v.Tail) 
        + ")"
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
        let headName, headV = v.Head
        "{" + 
        (List.fold (fun acc (name, v) -> acc + ", " + name + ":" + printResult v) 
        (headName + ":" + printResult headV) v.Tail) 
        + "}"
    | ResFn (Lambda (id, t), env) ->
        sprintf "Function with parameter %A" id
    | ResFn (Recursive(id, t1, id2, t), env) -> 
        sprintf "Recursive function with name %A and parameter %A" id id2
    | ResPartial (b, _) -> 
        sprintf "Partial application of builtin function %A" b