﻿module TranslationTests

open NUnit.Framework
open FsUnit
open Parser
open Definition
open Translation

let shouldFail text =
    (fun () -> text |> parsePure |> flip translate emptyTransEnv |> ignore) |> should throw typeof<ParseException> 
   
[<TestFixture>]
type PatternTranslationTests() =

    [<Test>]
    member this.invalidatesRepeats() =
        let pat = ExListPat [ExXPat "x", None; ExXPat "x", None]
        (fun () -> translatePattern (pat, None) emptyTransEnv |> ignore) 
            |> should throw typeof<ParseException>
    
    [<Test>]
    member this.invalidatesRepeatsInMultiple() =
        let pat1 = ExXPat "x", None
        let pat2 = ExXPat "x", None
        (fun () -> translatePatterns [pat1; pat2] emptyTransEnv |> ignore) 
            |> should throw typeof<ParseException>
     
    [<Test>]
    member this.addsIdentifier() =
        let pat = ExXPat "x", None
        let pat', env' = translatePattern pat emptyTransEnv
        env'.idents |> should equal (Map.empty.Add ("x", "generated0"))
        env'.nextSuffix |> should equal 1
        pat' |> should equal (Pat (XPat "generated0", None))
    
    [<Test>]
    member this.overridesIdentifier() =
        let pat = ExXPat "x", None
        let env = {emptyTransEnv with idents = Map.empty.Add ("x", "banana") }
        let pat', env' = translatePattern pat env
        env'.idents |> should equal (Map.empty.Add ("x", "generated0"))
        env'.nextSuffix |> should equal 1
        pat' |> should equal (Pat (XPat "generated0", None))

    [<Test>]
    member this.addsNestedIdentifiers() =
        let pat = ExListPat [ExXPat "x", None; ExXPat "y", None]
        let pat', env' = translatePattern (pat, None) emptyTransEnv
        env'.idents |> should equal (["x", "generated1"; "y", "generated0"] |> Map.ofList)
        env'.nextSuffix |> should equal 2
        let expectedPat' =
            Pat (ConstructorPat (Cons, [Pat (XPat "generated1", None); 
                Pat (ConstructorPat (Cons, [Pat (XPat "generated0", None); 
                    Pat (ConstructorPat (Nil, []), None)]), None)]), None)
        pat' |> should equal expectedPat'
    

[<TestFixture>]
type FunctionTranslationTests() =

    [<Test>]
    member this.simpleMatchForSingleArgument() =
        let fn = ExLambda ([ExXPat "x", None], ExX "x")   
        let fn' = translateFn fn emptyTransEnv
        fn' |> should equal (Fn <| Lambda ("generated1", Match (X "generated1", [Pat (XPat "generated0", None), None, X "generated0"])))

    [<Test>]
    member this.tupledMatchForMultipleArguments() =
        let fn = ExLambda ([ExXPat "x", None; ExXPat "y", None], ExX "x")   
        let fn' = translateFn fn emptyTransEnv

        let expected = 
            Fn <| Lambda ("generated3",
                Fn <| Lambda ("generated2",
                    Match (App (App (Constructor (Tuple 2), X "generated3"), X "generated2"),
                        [Pat (ConstructorPat (Tuple 2, [Pat (XPat "generated1", None); Pat (XPat "generated0", None)]), None),
                         None,
                         X "generated1"])))

        fn' |> should equal expected

    
    [<Test>]
    member this.dissallowsUndeclaredIdentifiers() =
        let fn = ExLambda ([ExXPat "x", None], ExX "generated1")   
        (fun () -> translateFn fn emptyTransEnv |> ignore)
            |> should throw typeof<ParseException>