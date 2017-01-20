module Printer

open Definition

let printTrait trt =
    match trt with
    | Orderable -> "Orderable"
    | Equatable -> "Equatable"

let rec printTraits traits =
    match traits with
    | [] -> ""
    | trt :: [] -> printTrait trt
    | trt :: rest -> printTrait trt + ", " + printTraits rest

let rec printType typ =
    match typ with
    | VarType(s, traits) -> 
        s + " (" + printTraits traits + ")"
    | Int -> "Int"
    | Bool -> "Bool"
    | Char -> "Char"
    | List Char -> "String"
    | Unit -> "Unit"
    | Function(t1, t2) ->  
        match t1 with
        | Function(_,_) -> 
            sprintf "(%s) -> %s" (printType t1) (printType t2)
        | _ ->
            sprintf "%s -> %s" (printType t1) (printType t2)
    | List(t) ->
        sprintf "[%s]" (printType t)

let rec private stringify term lvl =
    let tabs = String.replicate(lvl) "\t"
    match term with
    | B true -> 
        tabs + "true"
    | B false -> 
        tabs + "false"
    | I(i) -> 
        tabs + (string i)
    | C c ->
        tabs + (string c)
    | OP(t1, Application, t2) ->
        let t1' = (stringify t1 0)
        if t1'.EndsWith("\n") then
            sprintf "%s%s%s" tabs t1' (stringify t2 0)
        else
            sprintf "%s%s %s" tabs t1' (stringify t2 0)
    | OP(t1, Cons, t2) ->
        match t1 with
        | OP(_, cons, _) ->
            sprintf "%s(%s)::%s" tabs (stringify t1 0) (stringify t2 0)
        | _ ->
            sprintf "%s%s::%s" tabs (stringify t1 0) (stringify t2 0)
    | OP(n1, op, n2) ->
        let opString = match op with
                        | Add -> "+"
                        | Subtract -> "-"
                        | Multiply -> "*"
                        | Divide -> "/"
                        | LessThan -> "<"
                        | LessOrEqual -> "<="
                        | Equal -> "="
                        | Different -> "!="
                        | GreaterOrEqual -> ">="
                        | GreaterThan -> ">"
                        | _ -> "nao sei o que é"
        sprintf "%s(%s %s %s)" tabs (stringify n1 0) opString (stringify n2 0)
    | Cond(t1, t2, t3) ->
        sprintf "%sif %s then\n%s\n%selse\n%s" 
            tabs (stringify t1 0) (stringify t2 (lvl+1)) tabs (stringify t3 (lvl+1))
    | X(id) -> 
        tabs + id
    | Fn(id, Some typ, t) -> 
        let term = (stringify t (lvl+1))
        if term.EndsWith("\n") then
            sprintf "%sfn(%s: %s) {\n%s%s}\n" 
                tabs id (printType typ) (stringify t (lvl+1)) tabs
        else
            sprintf "%sfn(%s: %s) {\n%s\n%s}" 
                tabs id (printType typ) (stringify t (lvl+1)) tabs
    | Fn(id, None, t) -> 
        let term = (stringify t (lvl+1))
        if term.EndsWith("\n") then
            sprintf "%sfn(%s) {\n%s%s}\n" 
                tabs id (stringify t (lvl+1)) tabs
        else
            sprintf "%sfn(%s) {\n%s\n%s}" 
                tabs id (stringify t (lvl+1)) tabs
    | Let(id, Some typ, t1, t2) ->
        sprintf "%slet %s: %s = %s;\n%s" 
            tabs id (printType typ) (stringify t1 0) (stringify t2 lvl)
    | Let(id, None, t1, t2) ->
        sprintf "%slet %s = %s;\n%s" 
            tabs id (stringify t1 0) (stringify t2 lvl)
    | Nil -> 
        sprintf "%snil" tabs
    | IsEmpty(t) ->
        sprintf "%sempty? %s" tabs (stringify t 0)
    | Head(t) ->
        sprintf "%shead %s" tabs (stringify t 0)
    | Tail(t) ->
        sprintf "%stail %s" tabs (stringify t 0)
    | Raise ->
        tabs + "raise"
    | Try(t1, t2) ->
        sprintf "%stry\n%s\nexcept\n%s" 
            tabs (stringify t1 (lvl+1)) (stringify t2 (lvl+1))
    | _ as t -> sprintf "Could not print term %A" t

let print term = stringify term 0

let rec printResultList result =
    match result with
    | ResCons (head, ResNil) -> printResult head
    | ResCons (head, tail) -> printResult head + ", " + printResultList tail
    | t -> sprintf "Result %A is not list to be printed" t

and printResult result =
    match result with
    | ResB true -> "true"
    | ResB false -> "false"
    | ResSkip -> "skip"
    | ResC c -> string c
    | ResI i -> string i
    | ResRaise -> "raise"
    | ResNil -> "[]"
    | ResCons (head, tail) -> "[" + printResultList result + "]"
    | ResTuple v -> 
        "(" + 
        (List.fold (fun acc v -> acc + ", " + printResult v) 
        (printResult v.Head) v.Tail) 
        + ")"
    | ResRecord v -> 
        let headName, headV = v.Head
        "(" + 
        (List.fold (fun acc (name, v) -> acc + ", " + name + ":" + printResult v) 
        (headName + ":" + printResult headV) v.Tail) 
        + ")"
    | ResClosure (id, t, env) -> sprintf "Function with parameter %A" id
    | ResRecClosure (id, id2, t, env) -> 
        sprintf "Recursive function with name %A and parameter %A" id id2

type term with
    member public this.DisplayValue = stringify this 0