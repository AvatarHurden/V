module REPL

open Definition
open Parser
open Translation
open Evaluation
open TypeInference
open Printer
open System.Runtime.InteropServices

type Env =
    {currentCommand: string option
     commands: string list
     ids: Map<Ident, (Type * result)>
     browseIndex: int option
     currentLib: Library
     fromStdLib: bool
    }

    member this.clearLib () =
        { this with currentLib = if this.fromStdLib then parseStdlib () else emptyLib }

    member this.append command =
        let oldCommands = this.commands 
        { this with commands = oldCommands @ [command]; currentCommand = None }

let stdlibEnv = 
    {currentCommand = None
     commands = []; ids = Map.empty
     browseIndex = None
     currentLib = parseStdlib ()
     fromStdLib = true}

let emptyEnv = 
    {currentCommand = None
     commands = []
     ids = Map.empty
     browseIndex = None
     currentLib = emptyLib
     fromStdLib = false}

type options =
    | ShowType
    | Clear

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
        | Some prev -> prev + line

    let actualText, option =
        if current.StartsWith "<type>" then
            current.Substring 6, Some ShowType
        elif current = "<clear>" then
            "Nil", Some Clear
        else
            current, None
    let parsed = parseWith env.currentLib actualText
    let term = translate parsed env.currentLib.translationEnv

    let env' = env.append current

    try 
        match option with
        | Some ShowType ->
            let res = term |> typeInfer |> printType
            res |> Expression, env'
        | Some Clear ->
            Cleared, env'.clearLib ()
        | _ ->    
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
        | Some prev -> prev + line
    
    try
        let newLib = parseLibWith current env.currentLib
        let f = fun (OpSpec (_, s)) -> List.forall (fun (OpSpec (_, name)) -> name <> s) newLib.operators
        let oldOps' = List.filter f env.currentLib.operators
    
        let newOps = newLib.operators @ oldOps'
        let newTerms = env.currentLib.terms @ newLib.terms
        let newEnv = newLib.translationEnv
        let lib' = {terms = newTerms; operators = newOps; translationEnv = newEnv}
        ignore <| typeInferLib lib'

        let additions =
            List.collect (fst >> Translation.getIdents) newLib.terms
              |> List.map (fun id -> (id, lib'.translationEnv.getOriginalIdent id))
              |> List.map (fun (id, origId) -> 
                    let term = List.foldBack (fun (p, t) acc -> Let(p, t, acc)) newLib.terms (X id);
                    (origId, typeInfer term, evaluate term))

        let newIds = List.fold (fun ids (id, typ, result) -> Map.add id (typ, result) ids) env.ids additions
        Addition additions, {env with currentLib = lib'; ids = newIds}.append current
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