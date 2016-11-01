module InternalParserTests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation
open Parser2


[<TestFixture>]
type TestIdentParsing() =

    [<Test>]
    member that.emptyIdentifier() =
        (fun () -> parseIdent "" |> ignore) |> 
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.reservedIdentifier() =
        (fun () -> parseIdent "empty? t" |> ignore) |> 
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.spacedIdentifier() =
        parseIdent "  x   = t+3" |> should equal ("   = t+3", "x")

    [<Test>]
    member that.gluedIdentifier() =
        parseIdent "banana=t+3" |> should equal ("=t+3", "banana")

[<TestFixture>]
type TestTypeParsing() =

    [<Test>]
    member that.emptyType() =
        (fun () -> parseType "" [""] |> ignore) |>   
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.unclosedType() =
        (fun () -> parseType "[Int" [""] |> ignore) |> 
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.invalidType() =
        (fun () -> parseType "Inta" [")"] |> ignore) |> 
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.complexType() =
        parseType "([Int]->[Bool])->Int  =  3;" ["="] |> 
            should equal ("=  3;", Function(Function(List Int, List Bool), Int))

    [<Test>]
    member that.spacedType() =
        parseType "  Int   ->   String  ) 4" [")"] |> 
            should equal (") 4", Function(Int, List Char))

    [<Test>]
    member that.emptyClosing() =
        parseType "  Int   ->   String  ) 4" [""] |> 
            should equal ("->   String  ) 4", Int)

    [<Test>]
    member that.emptyClosingParenthesis() =
        parseType " ( Int   ->   String  ) 4" [""] |> 
            should equal ("4", Function(Int, List Char))


[<TestFixture>]
type TestIdentTypeParsing() =

    [<Test>]
    member that.emptyString() =
        (fun () -> parseIdentTypePair "" [] |> ignore) |>   
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.wrongSeparator() =
        (fun () -> parseIdentTypePair "x;" ["="] |> ignore) |> 
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.invalidType() =
        (fun () -> parseIdentTypePair "x:Doble, " [","] |> ignore) |> 
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.noType() =
        parseIdentTypePair "x = 3" ["="] |> 
            should equal ("= 3", ("x", (None: Type option)))

    [<Test>]
    member that.simpleType() =
        parseIdentTypePair "x:Int = 3" ["="] |> 
            should equal ("= 3", ("x", Some Int))


[<TestFixture>]
type TestParameterParsing() =

    [<Test>]
    member that.emptyString() =
        (fun () -> parseParameters "" [] |> ignore) |>   
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.noTypes() =
        parseParameters "x,y,z => x+y+z" ["=>"] |> 
            should equal ("=> x+y+z", ["x", (None: Type option); 
                "y", (None: Type option); "z", (None: Type option)])

    [<Test>]
    member that.simpleTypes() =
        parseParameters "x:Int,y:Bool,z:String => x+y+z" ["=>"] |> 
            should equal ("=> x+y+z", ["x", Some Int; 
                "y", Some Bool; "z", Some <| List Char])

    [<Test>]
    member that.complexTypes() =
        parseParameters "x:[[Int]],y:(Bool->Int),z:String => x+y+z" ["=>"] |> 
            should equal ("=> x+y+z", ["x", List Int |> List |> Some; 
                "y", Some <| Function (Bool, Int); "z", Some <| List Char])
