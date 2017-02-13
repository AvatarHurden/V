// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open System
open System.IO
open Definition
open StringConversion
open Parser
open Printer
open Evaluation
open TypeInference
open Compiler
open Argu
open System.Runtime.Serialization

type Compile =
    | [<MainCommand; Mandatory>] Path of path: string
    | Pure
    | Lib
    | Output of path: string
with
    interface IArgParserTemplate with
        member this.Usage =
            match this with
            | Path _ -> "The path of the file"
            | Pure -> "Do not load the stdlib"
            | Lib -> "Compile as library."
            | Output _ -> "Set the output path."
        
and Run =
    | [<MainCommand; Mandatory>] Path of path: string
    | Pure
    | ShowTime
with
    interface IArgParserTemplate with
        member this.Usage =
            match this with
            | Path _ -> "The path of the file"
            | Pure -> "Do not load the stdlib"
            | ShowTime -> "Show the time for parsing, inferring type and evaluating in milliseconds"

and Interactive =
    | Pure
with
    interface IArgParserTemplate with
        member this.Usage =
            match this with
            | Pure -> "Do not load the stdlib"

and Argument =
    | [<CliPrefix(CliPrefix.None)>] Interactive of ParseResults<Interactive>
    | [<CliPrefix(CliPrefix.None)>] Compile of ParseResults<Compile>
    | [<CliPrefix(CliPrefix.None)>] Run of ParseResults<Run>
with
    interface IArgParserTemplate with
        member s.Usage =
            match s with
            | Interactive _ -> "Open in interactive mode."
            | Compile _ -> "Compile Files."
            | Run _ -> "Run the specified file."

let parser = ArgumentParser.Create<Argument>(programName = "Interpretador_L1.exe")

let runCompile (results: ParseResults<Compile>) =
    let parser = parser.GetSubCommandParser <@ Compile @>
    
    if results.IsUsageRequested then
        Console.WriteLine (parser.PrintUsage())
    elif not <| results.Contains <@ Compile.Path @> then
        Console.WriteLine (parser.PrintUsage("Missing argument <path>"))
    else
        let path = results.GetResult <@ Compile.Path @>
        let isPure = results.Contains <@ Compile.Pure @>
        let isLib = results.Contains <@ Lib @>
        
        if not <| IO.File.Exists(path) then
            printfn "No file \"%s\" found" path
            exit(0)

        let outputName =
            results.GetResult (<@ Output @>, IO.Path.ChangeExtension(path, if isLib then "l1b" else "l1c"))
        
        let text = path |> IO.File.ReadAllText
           
        compileText (if isLib || isPure then parsePure else parse) text isLib outputName

let runRun (results: ParseResults<Run>) =
    let parser = parser.GetSubCommandParser <@ Run @>

    if results.IsUsageRequested then
        Console.WriteLine (parser.PrintUsage())
    elif not <| results.Contains <@ Run.Path @> then
        Console.WriteLine (parser.PrintUsage("Missing argument <path>"))
    else
        let path = results.GetResult <@ Run.Path @>
        let isPure = results.Contains <@ Run.Pure @>
        let showTime = results.Contains <@ Run.ShowTime @>

        if not <| IO.File.Exists(path) then
            printfn "No file \"%s\" found" path
            exit(0)
            
        try
            let evaluated = evaluate <| loadTerm path
            evaluated |> printResult |> printfn "%O"
        with
        | :? SerializationException ->
            
            let text = path |> IO.File.ReadAllText
            
            Parser.baseFolder <- path |> Path.GetFullPath |> Path.GetDirectoryName

            try
                let stopWatch = System.Diagnostics.Stopwatch.StartNew()
                let term = if isPure then parsePure text else parse text
                let parseTime = stopWatch.Elapsed.TotalMilliseconds

                stopWatch.Restart()
                ignore <| typeInfer term
                let inferTime = stopWatch.Elapsed.TotalMilliseconds
        
                stopWatch.Restart()
                let evaluated = evaluate term
                let evalTime = stopWatch.Elapsed.TotalMilliseconds

                evaluated |> printResult |> printfn "%O"
                printfn "Time to parse = %f" parseTime
                printfn "Time to infer type = %f" inferTime
                printfn "Time to evaluate = %f" evalTime
            with
            | EvalException e -> 
                printfn "Evaluation error:"
                Console.WriteLine e
            | ParseException e -> 
                printfn "Parsing error:"
                Console.WriteLine e
            | TypeException e ->
                printfn "Type system error:"
                Console.WriteLine e

let runInteractive (results: ParseResults<Interactive>) =
    let parser = parser.GetSubCommandParser <@ Interactive @>

    if results.IsUsageRequested then
        Console.WriteLine (parser.PrintUsage())
    else
        let isPure = results.Contains <@ Pure @>
        
        Console.WriteLine isPure

[<EntryPoint>]
let main argv = 

    let results = parser.Parse(raiseOnUsage = false)

    if results.IsUsageRequested then
        Console.WriteLine (parser.PrintUsage())
    else
        if results.Contains <@ Compile @> then
            runCompile <| results.GetResult <@ Compile @>
        elif results.Contains <@ Run @> then
            runRun <| results.GetResult <@ Run @>
        elif results.Contains <@ Interactive @> then
            runInteractive <| results.GetResult <@ Interactive @>
        else
            Console.WriteLine (parser.PrintUsage())  
        
    0

    