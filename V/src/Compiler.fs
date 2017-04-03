module Compiler

open System.Runtime.Serialization
open System.Runtime.Serialization.Formatters.Binary
open System.IO
open Definition
open TypeInference
open System

let mutable baseFolder = AppDomain.CurrentDomain.SetupInformation.ApplicationBase
let makeRelative fileName = Path.Combine(baseFolder, fileName)

let private save value path =
    let binFormatter = new BinaryFormatter()

    use stream = new FileStream(path, FileMode.Create)
    binFormatter.Serialize(stream, value)
    stream.Flush()

let saveTerm (term: term) path = save term path
let saveLib (lib: Library) path = save lib path

let private saveArray term  =
    let binFormatter = new BinaryFormatter()

    use stream = new MemoryStream()
    binFormatter.Serialize(stream, term)
    stream.ToArray()

let saveLibArray (lib: Library) = saveArray lib

let private load<'T> path =
    let binFormatter = new BinaryFormatter()

    use stream = new FileStream(path, FileMode.Open)
    binFormatter.Deserialize(stream) :?> 'T

let loadTerm = load<Definition.term>
let loadLib path = 

    let relative = makeRelative path

    let pathName = 
        if not <| Path.HasExtension relative then
            if Path.ChangeExtension(relative, "vl") |> File.Exists then
                Path.ChangeExtension(relative, "vl")
            elif Path.ChangeExtension(relative, "v") |> File.Exists then
               Path.ChangeExtension(relative, "v")
            else
                raise (LibNotFound <| sprintf "Could not find library file at %A" path)
        else
            if relative |> File.Exists then
                relative     
            else
                raise (LibNotFound <| sprintf "Could not find library file at %A" path)
    try
        load<Definition.Library> pathName
    with
    | :? SerializationException ->
        raise <| UncompiledLib (File.ReadAllText pathName)
    
let loadCompiledLib (arr: byte[]) =
    let binFormatter = new BinaryFormatter()

    use stream = new MemoryStream(arr)
    binFormatter.Deserialize(stream) :?> Definition.Library

let loadArray (arr: byte[]) =
    let binFormatter = new BinaryFormatter()

    use stream = new MemoryStream(arr)
    binFormatter.Deserialize(stream) :?> Definition.term

