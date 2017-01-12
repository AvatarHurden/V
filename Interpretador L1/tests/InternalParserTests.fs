module InternalParserTests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation
open Parser


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
        (fun () -> parseType "" (true, [""]) |> ignore) |>   
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.unclosedType() =
        (fun () -> parseType "[Int" (true, [""]) |> ignore) |> 
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.invalidType() =
        (fun () -> parseType "Inta" (true, [")"]) |> ignore) |> 
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.complexType() =
        parseType "([Int]->[Bool])->Int  =  3;" (true, ["="]) |> 
            should equal ("  3;", Function(Function(List Int, List Bool), Int))

    [<Test>]
    member that.spacedType() =
        parseType "  Int   ->   String  ) 4" (true, [")"]) |> 
            should equal (" 4", Function(Int, List Char))

    [<Test>]
    member that.emptyClosing() =
        parseType "  Int   ->   String  ) 4" (true, [""]) |> 
            should equal ("->   String  ) 4", Int)

    [<Test>]
    member that.emptyClosingParenthesis() =
        parseType " ( Int   ->   String  ) 4" (true, [""]) |> 
            should equal ("4", Function(Int, List Char))


[<TestFixture>]
type TestIdentTypeParsing() =

    [<Test>]
    member that.emptyString() =
        (fun () -> parseIdentTypePair "" (true, []) |> ignore) |>   
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.wrongSeparator() =
        (fun () -> parseIdentTypePair "x;" (true, ["="]) |> ignore) |> 
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.invalidType() =
        (fun () -> parseIdentTypePair "x:Doble, " (true, [","]) |> ignore) |> 
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.noType() =
        parseIdentTypePair "x = 3" (true, ["="]) |> 
            should equal (" 3", ("x", (None: Type option)))

    [<Test>]
    member that.simpleType() =
        parseIdentTypePair "x:Int = 3" (true, ["="]) |> 
            should equal (" 3", ("x", Some Int))

    [<Test>]
    member that.complexType() =
        parseIdentTypePair "x:[[Int]->[(Bool->String)]] = 3" (true, ["="]) |> 
            should equal (" 3", ("x", Some <| 
                List (Function (List Int, List (Function (Bool, List Char))))))


[<TestFixture>]
type TestParameterParsing() =

    [<Test>]
    member that.emptyString() =
        (fun () -> parseParameters "" (true, []) |> ignore) |>   
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.noTypes() =
        parseParameters "x,y,z => x+y+z" (true, ["=>"]) |> 
            should equal (" x+y+z", ["x", (None: Type option); 
                "y", (None: Type option); "z", (None: Type option)])

    [<Test>]
    member that.simpleTypes() =
        parseParameters "x:Int,y:Bool,z:String => x+y+z" (true, ["=>"]) |> 
            should equal (" x+y+z", ["x", Some Int; 
                "y", Some Bool; "z", Some <| List Char])

    [<Test>]
    member that.complexTypes() =
        parseParameters "x:[[Int]],y:(Bool->Int),z:String => x+y+z" (true, ["=>"]) |> 
            should equal (" x+y+z", ["x", List Int |> List |> Some; 
                "y", Some <| Function (Bool, Int); "z", Some <| List Char])


[<TestFixture>]
type TestStringLiteralParsing() =

    [<Test>]
    member that.emptyString() =
        (fun () -> parseStringLiteral "" '"' |> ignore) |>   
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.simple() =
        parseStringLiteral "hello governor\" said mary" '"' |> 
            should equal ("\" said mary", "hello governor")

    [<Test>]
    member that.escapedClosing() =
        parseStringLiteral "hello \\\"governor\\\"\" said mary" '"' |> 
            should equal ("\" said mary", "hello \"governor\"")

    [<Test>]
    member that.noClosing() =
        (fun () -> parseStringLiteral "hello governor' said mary" '"' |> ignore) |>   
            should throw typeof<InvalidEntryText> 


[<TestFixture>]
type TestCharParsing() =

    [<Test>]
    member that.emptyChar() =
        (fun () -> parseChar "'" |> ignore) |> 
            should throw typeof<InvalidEntryText> 
            
    [<Test>]
    member that.longChar() =
        (fun () -> parseChar "sd'" |> ignore) |> 
            should throw typeof<InvalidEntryText> 

    [<Test>]
    member that.unclosedChar() =
        (fun () -> parseChar "a" |> ignore) |> 
            should throw typeof<InvalidEntryText> 
            
    [<Test>]
    member that.simpleChar() =
        parseChar "a'; let..." |> should equal ("; let...", C 'a') 
            
    [<Test>]
    member that.escapedChar() =
        parseChar "\\\'' :: \\\"hello\\\"" |> 
            should equal (" :: \\\"hello\\\"", C '\'') 

[<TestFixture>]
type TestStringParsing() =

    [<Test>]
    member that.emptyString() =
        parseString "\" @ \\\"test\\\"" |> 
            should equal (" @ \\\"test\\\"", Nil)
            
    [<Test>]
    member that.unclosedString() =
        (fun () -> parseString "aafte" |> ignore) |> 
            should throw typeof<InvalidEntryText> 
            
    [<Test>]
    member that.longString() =
        parseString "thx\" @ \\\"test\\\"" |> should equal 
            (" @ \\\"test\\\"", OP(C 't', Cons, OP(C 'h', Cons, OP(C 'x', Cons, Nil))))

    [<Test>]
    member that.escapedString() =
        parseString "\\\"h\\\"\" @ \\\"hello\\\"" |> should equal 
            (" @ \\\"hello\\\"", OP(C '"', Cons, OP(C 'h', Cons, OP(C '"', Cons, Nil))))

[<TestFixture>]
type TestComponentParsing() =

    [<Test>]
    member that.noComponent() =
        let t = parseMultipleComponents "  )" (true, [")"])
        let s: string * (string option * term) list = "", []
        t |> should equal s 

    [<Test>]
    member that.singleComponent() =
        parseMultipleComponents " 3 )" (true, [")"]) |> 
            should equal ("", [((None: string option), I 3)])

    [<Test>]
    member that.doubleComponent() =
        parseMultipleComponents " 3, 'c' )" (true, [")"]) |> 
            should equal ("", [((None: string option), I 3); (None, C 'c')])
    
    [<Test>]
    member that.namedSingleComponent() =
        parseMultipleComponents " a : x )" (true, [")"]) |> 
            should equal ("", [(Some "a", X "x")])

    [<Test>]
    member that.namedDoubleComponent() =
        parseMultipleComponents " a : x, b: 3 )" (true, [")"]) |> 
            should equal ("", [(Some "a", X "x"); (Some "b", I 3)])

    [<Test>]
    member that.consComponent() =
        let t = parseMultipleComponents " a :: x )" (true, [")"])
        let s = ("", [((None: string option), OP (X "a", Cons, X "x"))])
        t |> should equal s        