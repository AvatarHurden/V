module Compiler

open System.Runtime.Serialization
open System.Runtime.Serialization.Formatters.Binary
open System.IO
open Definition
open TypeInference
open System

let saveTerm term path =
    let binFormatter = new BinaryFormatter()

    use stream = new FileStream(path, FileMode.Create)
    binFormatter.Serialize(stream, term)
    stream.Flush()

let loadTerm path =
    let binFormatter = new BinaryFormatter()

    use stream = new FileStream(path, FileMode.Open)
    binFormatter.Deserialize(stream) :?> Definition.term
    
let isValidLib term = 
    let rec iter t =
        match t with
        | Let (x, typ, inside, X "x") ->
            true
        | Let (x, typ, inside, (Let _ as newLet)) ->
            iter newLet
        | _ -> false
    match term with
    | Fn ("x", None, t) -> iter t
    | _ -> false

let replaceXLib lib term = 
    let rec iter t =
        match t with
        | Let (x, typ, inside, X "x") ->
            Let (x, typ, inside, term)
        | Let (x, typ, inside, (Let _ as newLet)) ->
            Let (x, typ, inside, iter newLet)
        | _ ->
            raise <| ParseException "Not a library"
    match lib with
    | Fn ("x", None, t) -> iter t
    | _ -> raise <| ParseException "Not a library"
    
let loadStdlib (arr: byte[]) nextTerm =
    let binFormatter = new BinaryFormatter()

    use stream = new MemoryStream(arr)
    let lib = binFormatter.Deserialize(stream) :?> Definition.term
    
    replaceXLib lib nextTerm

let loadLib path nextTerm =
    let lib = loadTerm path

    if isValidLib lib then
        replaceXLib lib nextTerm
    else
        raise <| ParseException ("The file at " + path + " is not a library")


