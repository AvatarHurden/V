﻿// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open System
open Definition
open StringConversion
open Parser
open Printer
open Evaluation
open TypeInference
open System.Text.RegularExpressions

let private splitSpaces term =
    term |> Seq.skipWhile Char.IsWhiteSpace |> String.Concat

[<EntryPoint>]
let main argv = 

    let t = "
    let t = [(3,4,6)];
    f (3,4,4,5)::t"

    let t' = parsePure t
    
    let f = Let ("f", None, Fn ("x", None, ProjectIndex (2, (X "x"))), t') 

    let typ, uni = typeInfer f
    printConstraints uni.constraints
    let t = evaluate f

    // Para permitir debug (não permite espaços entre parâmetros)
    let argv = 
        if argv.Length = 0 then
            System.Console.ReadLine().Split ' '
        else
            argv
            
    let file = 
        if argv.Length = 0 then
            printfn "Missing argument"
            exit(0)
        else
            argv.[0]

    let text = 
        if IO.File.Exists(file) then
            file |> IO.File.ReadAllText
        else
            printfn "Provided path is invalid"
            exit(0)

    try
        let stopWatch = System.Diagnostics.Stopwatch.StartNew()

        let term = parse text

        stopWatch.Stop()
        printfn "Time to parse = %f" stopWatch.Elapsed.TotalMilliseconds
        
        
        //printfn "%O" <| toString term
        
        stopWatch.Restart()

        typeInfer term |> printfn "Your program is of type:\n\n%A\n\n"
        
        stopWatch.Stop()
        printfn "Time to infer type = %f" stopWatch.Elapsed.TotalMilliseconds
            

        stopWatch.Restart()

        term |> evaluate |> printResult |> printfn "Your program resulted in:\n\n%O\n"
        
        stopWatch.Stop()
        printfn "Time to evaluate = %f" stopWatch.Elapsed.TotalMilliseconds
    with
    | WrongExpression e -> Console.WriteLine e
    | InvalidEntryText t -> Console.WriteLine t
    | InvalidType e ->
        printfn "Your program has invalid type information"
        Console.WriteLine e

    ignore <| System.Console.ReadLine()
    0 // return an integer exit code

    