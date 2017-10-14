module TestHelpers

open NUnit.Framework
open FsUnit
open Parser
open Definition

let ExInt = ExConstType (Definition.Int, [])
let ExBool = ExConstType (Definition.Bool, [])
let ExChar = ExConstType (Definition.Char, [])
let ExList x = ExConstType (Definition.List, [x])

let Int = ConstType (Definition.Int, [])
let Bool = ConstType (Definition.Bool, [])
let Char = ConstType (Definition.Char, [])
let List x = ConstType (Definition.List, [x])