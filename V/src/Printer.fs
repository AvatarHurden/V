module Printer

open Definition

let rec printTrait trt =
    match trt with
    | Orderable -> "Orderable"
    | Equatable -> "Equatable"
    | RecordLabel (label, typ) ->
        sprintf "%A at label %A" (printType typ) label

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
        s + " (" + printTraits traits + ")"
    | Int -> "Int"
    | Bool -> "Bool"
    | Char -> "Char"
    | List Char -> "String"
    | Function(t1, t2) ->  
        match t1 with
        | Function(_,_) -> 
            sprintf "(%s) -> %s" (printType t1) (printType t2)
        | _ ->
            sprintf "%s -> %s" (printType t1) (printType t2)
    | List(t) ->
        sprintf "[%s]" (printType t)
    | Type.Tuple (types) ->
        sprintf "(%s)" (printTuple types)
    | Type.Record (pairs) ->
        sprintf "{%s}" (printRecord pairs)

let rec printResultList result =
    match result with
    | ResCons (head, ResNil) -> printResult head
    | ResCons (head, tail) -> printResult head + ", " + printResultList tail
    | t -> sprintf "Result %A is not list to be printed" t

and printResultString result =
    match result with
    | ResCons (ResC head, ResNil) -> string head
    | ResCons (ResC head, tail) -> string head + printResultString tail
    | t -> sprintf "Result %A is not list to be printed" t

and printResult result =
    match result with
    | ResB true -> "true"
    | ResB false -> "false"
    | ResC c -> string c
    | ResI i -> string i
    | ResRaise -> "raise"
    | ResNil -> "[]"
    | ResCons (ResC head, tail) -> "\"" + printResultString result + "\""
    | ResCons (head, tail) -> "[" + printResultList result + "]"
    | ResTuple v -> 
        "(" + 
        (List.fold (fun acc v -> acc + ", " + printResult v) 
        (printResult v.Head) v.Tail) 
        + ")"
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
    | ResFn (BuiltIn b, env) ->
        sprintf "Builtin function %A" b
    | ResPartial (b, _) -> 
        sprintf "Partial application of builtin function %A" b