module LibParser

open System.Runtime.Serialization.Formatters.Binary
open System.IO
open Parser
open TypeInference
open System

let saveLib libPath =
    try
        let libText = File.ReadAllText libPath

        // Parse the library as a function
        let lib = parsePure <| "\x -> " + libText + " x"

        // Check to see if library is correct
        ignore <| typeInfer lib

        let binFormatter = new BinaryFormatter()

        use stream = new FileStream (Path.ChangeExtension (libPath, "l1b"), FileMode.Create)
        binFormatter.Serialize(stream, lib)
        stream.Flush()
    with
    | InvalidType e ->
        Console.WriteLine "Compiling the library resulted in the following type error: "
        Console.WriteLine e
    | InvalidEntryText e -> 
        Console.WriteLine "Compiling the library resulted in the following syntax error: "
        Console.WriteLine e


