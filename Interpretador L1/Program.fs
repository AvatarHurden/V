// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open System
open Definition
open Sugar
open Evaluation

[<EntryPoint>]
let main argv = 

    let file = 
        if argv.Length = 0 then
            let mutable cur = System.Console.ReadLine()
            let mutable acc = cur
            while cur.Length > 0 do
                cur <- System.Console.ReadLine()
                if cur.Length > 0 then
                    acc <- acc + "\n" + cur
            acc
        else
            argv.[0]

    let text = 
        if IO.File.Exists(file) then
            file |> IO.File.ReadAllText
        else
            file

    try
        let term = parseTerm text
            
        term |> print |> printfn "Your input was interpreted as:\n\n%O"
        Console.WriteLine()
        Console.WriteLine()
        term |> eval |> print |> printfn "Your program resulted in:\n\n%O"
    with
    | InvalidEntryText t -> Console.WriteLine t
    | WrongExpression t -> Console.WriteLine t

    let t2 = System.Console.ReadLine()
    0 // return an integer exit code

    