module REPL

open Definition
open Parser
open Translation
open Evaluation
open TypeInference
open Printer
open System.Runtime.InteropServices

let getBindings lib = 
    let identPairs = List.collect (fun decl -> match decl with Term(pat, _) -> Translation.getIdents pat | Data _ -> []) lib.terms
                        |> List.map (fun id -> (id, lib.translationEnv.getOriginalIdent id))
    let tuple = List.fold (fun  acc (id, _) -> App(acc, X id)) 
                          (Constructor <| Tuple identPairs.Length) 
                          identPairs
    let term = List.foldBack (fun decl acc -> Let(decl, acc)) lib.terms tuple;
    let types =
        match typeInfer term with
        | ConstType (ConstructorType.Tuple _, types) -> types
        | _ -> raise <| ParseException "There was an error getting the bindings in the REPL"
    let results =
        match evaluate term with
        | ResConstructor (Tuple _, results) -> results 
        | _ -> raise <| ParseException "There was an error getting the bindings in the REPL"
    List.zip3 (List.map snd identPairs) types results

let makeIdList existingIds newIds =
    List.fold (fun ids (id, typ, result) -> Map.add id (typ, result) ids) 
                             existingIds newIds

let printBinding (id, (typ, res)) =
    match typ with
    | Function _ -> id + ": " + (printType typ) // Do not try to print value if it is a function.
    | _ -> id + ": " + (printType typ) + " = " + printResult res

type Env =
    {currentCommand: string option
     commands: string list
     ids: Map<Ident, (Type * result)>
     allIds: Map<Ident, (Type * result)>
     browseIndex: int option
     currentLib: Library
     fromStdLib: bool
    }

    member this.clearLib () =
        let newLib = if this.fromStdLib then parseStdlib () else emptyLib
        { this with currentLib = newLib
                    ids = Map.empty
                    allIds = newLib |> getBindings |> makeIdList Map.empty}

    member this.append command =
        let oldCommands = this.commands 
        { this with commands = oldCommands @ [command]; currentCommand = None }

    member this.appendIds newIds = 
        let ids' = makeIdList this.ids newIds
        let allIds' = makeIdList this.allIds newIds
        { this with ids = ids'; allIds = allIds' }

let stdlibEnv = 
    {currentCommand = None
     commands = []
     ids = Map.empty
     allIds = parseStdlib () |> getBindings |> makeIdList Map.empty
     browseIndex = None
     currentLib = parseStdlib ()
     fromStdLib = true}

let emptyEnv = 
    {currentCommand = None
     commands = []
     ids = Map.empty
     allIds = Map.empty
     browseIndex = None
     currentLib = emptyLib
     fromStdLib = false}

type options =
    | ShowType
    | Clear
    | ListIds
    | ListAllIds // List also Ids bound in std library and by user
    | History

type parseResult =
    | Expression of string
    | Error of exn
    | Addition of (Ident * Type * result) list
    | Partial
    | Cleared

let processTerm line (env: Env) =
    let current = 
        match env.currentCommand with
        | None -> line
        | Some prev -> prev + "\n" + line

    let actualText, option =
        if current.StartsWith "<type>" then
            current.Substring 6, Some ShowType
        elif current = "<clear>" then
            "Nil", Some Clear
        elif current = "<list>" then
            "Nil", Some ListIds
        elif current = "<list-all>" then
            "Nil", Some ListAllIds
        elif current = "<history>" then
            "Nil", Some History
        else
            current, None
    let parsed = parseWith env.currentLib actualText
    let term = translate parsed env.currentLib.translationEnv

    let env' = if option.IsNone then env.append current else env

    try 
        match option with
        | Some ShowType ->
            let res = term |> typeInfer |> printType
            res |> Expression, env'
        | Some Clear ->
            Cleared, env'.clearLib ()
        | Some ListIds ->
            let s = Map.toList env'.ids 
                    |> List.map printBinding
                    |> String.concat "\n"
            s |> Expression, env'
        | Some ListAllIds ->
            let s = Map.toList env'.allIds
                    |> List.map printBinding
                    |> String.concat "\n"
            s |> Expression, env'
        | Some History ->
            String.concat "\n" env'.commands |> Expression, env'
        | None ->    
            term |> typeInfer |> ignore
            let evaluated = evaluate term
            let res = evaluated |> printResult 
            res |> Expression, env'
    with
    | e ->
        Error e, env'

let processLib line (env: Env) =
    let current = 
        match env.currentCommand with
        | None -> line
        | Some prev -> prev + "\n" + line
    
    try
        let newLib = parseLibWith current env.currentLib
        let f = fun (OpSpec (_, s)) -> List.forall (fun (OpSpec (_, name)) -> name <> s) newLib.operators
        let oldOps' = List.filter f env.currentLib.operators
    
        let newOps = newLib.operators @ oldOps'
        let newTerms = env.currentLib.terms @ newLib.terms
        let newEnv = newLib.translationEnv
        let lib' = {terms = newTerms; operators = newOps; translationEnv = newEnv}
        ignore <| typeInferLib lib'

        let additions = getBindings newLib
        Addition additions, ({env with currentLib = lib' }.append current).appendIds additions
    with
    | ParseException _ as e ->
        Partial, {env with currentCommand = Some current}
    | TypeException _ as e ->
        Error e, env.append current

let rec parseLine line (env: Env)  =
    try
        processTerm line env
    with
    | ParseException e as exc -> 
        if e.Contains "The error occurred at the end of the input stream" then
            processLib line env
        else
            Error exc, {env with currentCommand = None}