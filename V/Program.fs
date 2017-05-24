// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open System
open System.IO
open Definition
open Translation
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
    | ShowTime
with
    interface IArgParserTemplate with
        member this.Usage =
            match this with
            | Path _ -> "The path of the file"
            | Pure -> "Do not load the stdlib"
            | Lib -> "Compile as library."
            | Output _ -> "Set the output path."
            | ShowTime -> "Show the time for each operation in milliseconds"
        
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
            | ShowTime -> "Show the time for each operation in milliseconds"

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
    | [<HiddenAttribute>] CompileStdLib
    | [<HiddenAttribute>] WriteTests
with
    interface IArgParserTemplate with
        member s.Usage =
            match s with
            | Interactive _ -> "Open in interactive mode."
            | Compile _ -> "Compile Files."
            | Run _ -> "Run the specified file."
            | CompileStdLib -> ""
            | WriteTests -> ""

let parser = ArgumentParser.Create<Argument>(programName = "V.exe")

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
        
        let showTime = results.Contains <@ Compile.ShowTime @>
        let mutable times = []

        if not <| IO.File.Exists(path) then
            printfn "No file \"%s\" found" path
            exit(0)

        let outputName =
            results.GetResult (<@ Output @>, IO.Path.ChangeExtension(path, if isLib then "vl" else "vo"))
        
        let stopWatch = System.Diagnostics.Stopwatch.StartNew()
        let text = path |> IO.File.ReadAllText
        times <- times @ ["read file", stopWatch.Elapsed.TotalMilliseconds]
        
        try
            if isLib then
                stopWatch.Restart()
                let lib = parseLib text
                times <- times @ ["parse", stopWatch.Elapsed.TotalMilliseconds]
                
                stopWatch.Restart()
                ignore <| typeInferLib lib
                times <- times @ ["infer type", stopWatch.Elapsed.TotalMilliseconds]

                stopWatch.Restart()
                saveLib lib outputName
                times <- times @ ["save ", stopWatch.Elapsed.TotalMilliseconds]
            else
                stopWatch.Restart()
                let exTerm = (if isPure then parsePure else parse) text
                times <- times @ ["parse", stopWatch.Elapsed.TotalMilliseconds]
                
                stopWatch.Restart()
                let term = translate exTerm
                times <- times @ ["translate", stopWatch.Elapsed.TotalMilliseconds]

                stopWatch.Restart()
                ignore <| typeInfer term
                times <- times @ ["infer type", stopWatch.Elapsed.TotalMilliseconds]

                stopWatch.Restart()
                saveTerm term outputName
                times <- times @ ["save ", stopWatch.Elapsed.TotalMilliseconds]
        with
        | ParseException e -> 
            printfn "Parsing error:"
            Console.WriteLine e
        | TypeException e ->
            printfn "Type system error:"
            Console.WriteLine e
             
        if showTime then
            Console.WriteLine (List.fold (fun acc (x, t) -> acc + sprintf "\nTime to %s = %f" x t) "" times)
            printfn "\nTotal time = %f" <| List.fold (fun acc (x, t) -> acc + t) 0.0 times   

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
        let mutable times = []

        if not <| IO.File.Exists(path) then
            printfn "No file \"%s\" found" path
            exit(0)
            
        try
            let stopWatch = System.Diagnostics.Stopwatch.StartNew()
            let term = loadTerm path
            times <- times @ ["read file", stopWatch.Elapsed.TotalMilliseconds]
            
            stopWatch.Restart()
            let evaluated = evaluate term
            times <- times @ ["evaluate", stopWatch.Elapsed.TotalMilliseconds]

            evaluated |> printResult |> printfn "%O"
            if showTime then
                Console.WriteLine (List.fold (fun acc (x, t) -> acc + sprintf "\nTime to %s = %f" x t) "" times)
                printfn "\nTotal time = %f" <| List.fold (fun acc (x, t) -> acc + t) 0.0 times
        with
        | :? SerializationException ->
            
            let stopWatch = System.Diagnostics.Stopwatch.StartNew()
            let text = path |> IO.File.ReadAllText
            times <- times @ ["read file", stopWatch.Elapsed.TotalMilliseconds]
            
            Compiler.baseFolder <- path |> Path.GetFullPath |> Path.GetDirectoryName

            try
                stopWatch.Restart()
                let exTerm = (if isPure then parsePure else parse) text
                times <- times @ ["parse", stopWatch.Elapsed.TotalMilliseconds]
                
                stopWatch.Restart()
                let term = translate exTerm
                times <- times @ ["translate", stopWatch.Elapsed.TotalMilliseconds]

                stopWatch.Restart()
                ignore <| typeInfer term
                times <- times @ ["infer type", stopWatch.Elapsed.TotalMilliseconds]
        
                stopWatch.Restart()
                let evaluated = evaluate term
                times <- times @ ["evaluate", stopWatch.Elapsed.TotalMilliseconds]

                evaluated |> printResult |> printfn "%O"
                if showTime then
                    Console.WriteLine (List.fold (fun acc (x, t) -> acc + sprintf "\nTime to %s = %f" x t) "" times)
                    printfn "\nTotal time = %f" <| List.fold (fun acc (x, t) -> acc + t) 0.0 times
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

type options =
    | ShowType
    | Clear

let rec parseItem lib previous first =
    
    if first then 
        printf "> "

    let line = previous + Console.ReadLine()
    try
        let actualText, options =
            if line.StartsWith "<type>" then
                line.Substring 6, Some ShowType
            elif line = "<clear>" then
                "nil", Some Clear
            else
                line, None
        let parsed = parseWith lib actualText
        Choice2Of3 (translate parsed, lib), options
    with
    | ParseException e -> 
        if e.Contains "The error occurred at the end of the input stream" then
            try
                let newLib = parseLib line
                let f = fun (OpSpec (_, s)) -> List.forall (fun (OpSpec (_, name)) -> name <> s) newLib.operators
                let oldOps' = List.filter f lib.operators
        
                let newOps = newLib.operators @ oldOps'
                let newTerms = lib.terms @ newLib.terms
                let lib' = {terms = newTerms; operators = newOps}
                Choice1Of3 lib', None
            with
            | ParseException e ->
                parseItem lib line false
        else
            Console.WriteLine e
            Choice3Of3 lib, None

let rec interactive (parsed, option) =
    match parsed with
    | Choice1Of3 (newLib: Library) ->
        interactive <| parseItem newLib "" true
    | Choice2Of3 (term, lib) ->
        try 
            match option with
            | Some ShowType ->
                term |> typeInfer |> printType |> printfn "%O"
            | Some Clear ->
                ()
            | _ ->    
            term |> typeInfer |> ignore
            let evaluated = evaluate term
            evaluated |> printResult |> printfn "%O"
        with
        | TypeException e ->
            printfn "Type system error:"
            Console.WriteLine e
        | EvalException e -> 
            printfn "Evaluation error:"
            Console.WriteLine e
        match option with
        | Some Clear ->
            interactive <| parseItem emptyLib "" true
        | _ ->
            interactive <| parseItem lib "" true
    | Choice3Of3 lib ->
        interactive <| parseItem lib "" true

let runInteractive (results: ParseResults<Interactive>) =
    let parser = parser.GetSubCommandParser <@ Interactive @>

    if results.IsUsageRequested then
        Console.WriteLine (parser.PrintUsage())
    else
        let isPure = results.Contains <@ Pure @>

        if isPure then
            interactive <| parseItem emptyLib "" true
        else
            interactive <| parseItem (stdlib.loadCompiled ()) "" true

let compileStdlib x =
    
    let lib = parseLib stdlib.content
    
    ignore <| typeInferLib lib

    let ar = saveLibArray lib
        
    let text = "module compiledStdlib"
    let text = text + "\n\nlet compiled: byte[] = [|"

    let f (index, text) (byte: byte) =
        let hex = String.Format("0x{0:X2}uy;", byte)
        if index = 16 then
            0 , text + "\n    " + hex
        else
            index + 1, text + " " + hex

    let (_, text) = Array.fold f (16, text) ar

    let text = text.Substring (0, text.Length - 1) + "\n|]\n\n"

    File.WriteAllText("compiledStdlib.fs", text)

let rec getTermText x =
    let text = Console.ReadLine ()
    if text.Length = 0 then
        text
    else
        text + "\n" + getTermText ()

let rec writeTests x =
    Console.WriteLine "Select what to test:"
    Console.WriteLine "1 - Type"
    Console.WriteLine "2 - Result"
    //Console.WriteLine "3 - Type and Result"
    Console.WriteLine "4 - Exit"

    let option = Console.ReadLine()
    match option with
    | "4" -> ()
    | "1" | "2" -> 

        Console.WriteLine "Insert the name of the test: "

        let name = Console.ReadLine ()
        
        Console.WriteLine "Insert the expression (empty line finishes):"

        let termText = getTermText ()
        
        Console.WriteLine termText
        try
            let term = translate <| parse termText
            
            Console.WriteLine ()
            Console.WriteLine "What should the correct result be?"
            Console.WriteLine "0 - A result"
            Console.WriteLine "1 - An error"

            let text =
                match Console.ReadLine () with
                | "0" ->
                    let result = 
                        if option = "1" then
                            sprintf "%A" <| typeInfer term
                        else
                            sprintf "%A" <| evaluate term
                    Console.WriteLine "The provided result is: "
                    Console.WriteLine (sprintf "%AO" result)
                    sprintf "
        [<Test>]
        member that.%O() =
            compare (%A, %O)\n" name (termText.TrimEnd()) result
                | "1" -> 
                    sprintf "
        [<Test>]
        member that.%O() =
            shouldFail %A\n" name termText
                | _ -> ""
  
            File.AppendAllText("tests.txt", text)
            writeTests ()
            with
            | ParseException e ->
                printfn "Parse error:"
                Console.WriteLine e
        
    | _ ->
        Console.WriteLine "Wrong Key"
        writeTests ()

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
        elif results.Contains <@ CompileStdLib @> then
            compileStdlib ()
        elif results.Contains <@ WriteTests @> then
            writeTests ()
        else
            Console.WriteLine (parser.PrintUsage())  
    
    0

    