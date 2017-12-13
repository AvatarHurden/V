module TestHelpers

open NUnit.Framework
open System
open FsUnit
open Parser
open Definition

let ExInt = ExConstType (Definition.Int, [])
let ExBool = ExConstType (Definition.Bool, [])
let ExChar = ExConstType (Definition.Char, [])
let ExList x = ExConstType (Definition.List, [x])

let Int' = ConstType (Definition.Int, [])
let Bool = ConstType (Definition.Bool, [])
let Char = ConstType (Definition.Char, [])
let List x = ConstType (Definition.List, [x])

let tupled (values: term list) =
    let constructor = Constructor <| Tuple (values.Length)
    Seq.fold (fun acc x -> App (acc, x)) constructor values