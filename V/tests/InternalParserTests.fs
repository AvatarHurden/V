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
            should throw typeof<ParseException> 

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
        (fun () -> parseType "" (true, [S ""]) |> ignore) |>   
            should throw typeof<ParseException> 

    [<Test>]
    member that.unclosedType() =
        (fun () -> parseType "[Int" (true, [S ""]) |> ignore) |> 
            should throw typeof<ParseException> 

    [<Test>]
    member that.invalidType() =
        (fun () -> parseType "Inta" (true, [S ")"]) |> ignore) |> 
            should throw typeof<ParseException> 

    [<Test>]
    member that.complexType() =
        parseType "([Int]->[Bool])->Int  =  3;" (true, [S "="]) |> 
            should equal ("  3;", Function(Function(List Int, List Bool), Int))

    [<Test>]
    member that.spacedType() =
        parseType "  Int   ->   String  ) 4" (true, [S ")"]) |> 
            should equal (" 4", Function(Int, List Char))

    [<Test>]
    member that.emptyClosing() =
        parseType "  Int   ->   String  ) 4" (true, [S ""]) |> 
            should equal ("->   String  ) 4", Int)

    [<Test>]
    member that.emptyClosingParenthesis() =
        parseType " ( Int   ->   String  ) 4" (true, [S ""]) |> 
            should equal ("4", Function(Int, List Char))

    [<Test>]
    member that.tupleType() =
        parseType " ( Int, Bool  ) 4" (true, [S ""]) |> 
            should equal ("4", Type.Tuple [Int; Bool])
            
    [<Test>]
    member that.tupleUnitType() =
        (fun () -> parseType " (   ) 4" (true, [S ""]) |> ignore) |> 
            should throw typeof<ParseException> 

    [<Test>]
    member that.recordType() =
        parseType " {a: Bool , b: (Int, Char)} 4" (true, [S ""]) |> 
            should equal ("4", 
                Type.Record ["a", Bool; "b", Type.Tuple [Int; Char]])
                
    [<Test>]
    member that.recordUnitType() =
        (fun () -> parseType " { } 4" (true, [S ""]) |> ignore) |> 
            should throw typeof<ParseException> 

[<TestFixture>]
type TestIdentTypeParsing() =

    [<Test>]
    member that.emptyString() =
        (fun () -> parseIdentTypePair "" (true, []) |> ignore) |>   
            should throw typeof<ParseException> 

    [<Test>]
    member that.wrongSeparator() =
        (fun () -> parseIdentTypePair "x;" (true, [S "="]) |> ignore) |> 
            should throw typeof<ParseException> 

    [<Test>]
    member that.invalidType() =
        (fun () -> parseIdentTypePair "x:Doble, " (true, [S ","]) |> ignore) |> 
            should throw typeof<ParseException> 

    [<Test>]
    member that.noType() =
        parseIdentTypePair "x = 3" (true, [S "="]) |> 
            should equal (" 3", ("x", (None: Type option)))

    [<Test>]
    member that.simpleType() =
        parseIdentTypePair "x:Int = 3" (true, [S "="]) |> 
            should equal (" 3", ("x", Some Int))

    [<Test>]
    member that.complexType() =
        parseIdentTypePair "x:[[Int]->[(Bool->String)]] = 3" (true, [S "="]) |> 
            should equal 
                (" 3", ("x", 
                    Some <| 
                    List (Function (List Int, List (Function (Bool, List Char))))))


[<TestFixture>]
type TestParameterParsing() =

    [<Test>]
    member that.emptyString() =
        (fun () -> parseParameters "" (true, []) |> ignore) |>   
            should throw typeof<ParseException> 

    [<Test>]
    member that.noTypes() =
        parseParameters "x y z => x+y+z" (true, [S "=>"]) |> 
            should equal 
                (" x+y+z", [Pat(XPat "x", (None: Type option)); 
                    Pat(XPat "y", (None: Type option)); Pat(XPat "z", (None: Type option))])

    [<Test>]
    member that.simpleTypes() =
        parseParameters "(x:Int) (y:Bool) (z:String) => x+y+z" (true, [S "=>"]) |> 
            should equal (" x+y+z", [Pat(XPat "x", Some Int); 
                Pat(XPat "y", Some Bool); Pat(XPat "z", Some <| List Char)])

    [<Test>]
    member that.complexTypes() =
        parseParameters "(x:[[Int]]) (y:(Bool->Int)) (z:String) => x+y+z" (true, [S "=>"]) |> 
            should equal (" x+y+z", [Pat(XPat "x", List Int |> List |> Some); 
                Pat(XPat "y", Some <| Function (Bool, Int)); Pat(XPat "z", Some <| List Char)])

    [<Test>]
    member that.recordPatterns() =
        parseParameters "{a: x, b: y: Int} => x + y" (true, [S "=>"]) |>
            should equal (" x + y", [Pat(RecordPat 
                ["a", Pat(XPat "x", None);
                 "b", Pat(XPat "y", Some Int)], None)])

    [<Test>]
    member that.consPattern() =
        parseParameters "((x :: y): [Int]) z => x + y + z" (true, [S "=>"]) |>
            should equal (" x + y + z", [Pat(ConsPat (
                Pat(XPat "x", None),
                Pat(XPat "y", None)), Some (List Int));
                Pat(XPat "z", None)])
        
    [<Test>]
    member that.consPatternFailed() =
        (fun () -> parseParameters "x :: y => x + y" (true, [S "=>"]) |> ignore) |>   
            should throw typeof<ParseException> 

[<TestFixture>]
type TestStringLiteralParsing() =

    [<Test>]
    member that.emptyString() =
        (fun () -> parseStringLiteral "" '"' |> ignore) |>   
            should throw typeof<ParseException> 

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
            should throw typeof<ParseException> 


[<TestFixture>]
type TestCharParsing() =

    [<Test>]
    member that.emptyChar() =
        (fun () -> parseChar "'" |> ignore) |> 
            should throw typeof<ParseException> 
            
    [<Test>]
    member that.longChar() =
        (fun () -> parseChar "sd'" |> ignore) |> 
            should throw typeof<ParseException> 

    [<Test>]
    member that.unclosedChar() =
        (fun () -> parseChar "a" |> ignore) |> 
            should throw typeof<ParseException> 
            
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
            should throw typeof<ParseException> 
            
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
        let t = parseMultipleComponents parseTerm "  )" (true, [S ")"])
        let s: string * term list = "", []
        t |> should equal s 

    [<Test>]
    member that.singleComponent() =
        parseMultipleComponents parseTerm " 3 )" (true, [S ")"]) |> 
            should equal ("", [I 3])

    [<Test>]
    member that.doubleComponent() =
        parseMultipleComponents parseTerm " 3, 'c' )" (true, [S ")"]) |> 
            should equal ("", [I 3; C 'c'])
    
    [<Test>]
    member that.namedSingleComponent() =
        parseMultipleComponents parseRecordComponent " a : x }" (true, [S "}"]) |> 
            should equal ("", [("a", X "x")])

    [<Test>]
    member that.namedDoubleComponent() =
        parseMultipleComponents parseRecordComponent " a : x, b: 3 }" (true, [S "}"]) |> 
            should equal ("", [("a", X "x"); ("b", I 3)])

    [<Test>]
    member that.consComponent() =
        let t = parseMultipleComponents parseTerm " a :: x )" (true, [S ")"])
        let s = ("", [OP (X "a", Cons, X "x")])
        t |> should equal s   
       
    [<Test>]
    member that.consComponentRecord() =
        let t = parseMultipleComponents parseRecordComponent "b : a :: x }" (true, [S "}"])
        let s = ("", ["b", OP (X "a", Cons, X "x")])
        t |> should equal s

    [<Test>]
    member that.consComponentRecordUnnamed() =
        (fun () -> parseMultipleComponents parseRecordComponent "a :: x }" (true, [S "}"]) |> ignore) |> 
            should throw typeof<ParseException> 
         
         