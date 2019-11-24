module TranslationTests

open NUnit.Framework
open FsUnit
open TestHelpers
open Parser
open Definition
open Translation

let shouldFail text =
    (fun () -> text |> parsePure |> flip translate emptyTransEnv |> ignore) |> should throw typeof<ParseException> 
   
[<TestFixture>]
 type TypeTranslationTests() =

    [<Test>]
    member this.usesEnvironment() =
        let t = ExTypeAlias ("a")
        let env = emptyTransEnv.addTypeAlias "a" (ConstType (Int, []))
        translateType t env |> should equal (ConstType (Int, []))

    [<Test>]
    member this.failsWithUnkown() =
        let t = ExTypeAlias ("a")
        (fun () -> translateType t emptyTransEnv |> ignore) 
            |> should throw typeof<ParseException>
            
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
        fn' |> should equal (Fn <| Lambda ("generated0", X "generated0"))

    [<Test>]
    member this.typedMatchForSingleArgument() =
        let fn = ExLambda ([ExXPat "x", Some (ExConstType (Int, []))], ExX "x")   
        let fn' = translateFn fn emptyTransEnv
        fn' |> should equal 
            (Fn <| Lambda ("generated1", 
                Match (X "generated1", 
                    [Pat (XPat "generated0", Some (ConstType (Int, []))), None, X "generated0"])))

    [<Test>]
    member this.simpleMatchForMultipleArguments() =
        let fn = ExLambda ([ExXPat "x", None; ExXPat "y", None], ExX "x")   
        let fn' = translateFn fn emptyTransEnv

        let expected = 
            Fn <| Lambda ("generated1", Fn <| Lambda ("generated0", X "generated1"))

        fn' |> should equal expected

    [<Test>]
    member this.tupledMatchForMultipleArguments() =
        let fn = ExLambda ([ExXPat "x", None; ExIgnorePat, None], ExX "x")   
        let fn' = translateFn fn emptyTransEnv

        let expected = 
            Fn <| Lambda ("generated2",
                Fn <| Lambda ("generated1",
                    Match (App (App (Constructor (Tuple 2), X "generated2"), X "generated1"),
                        [Pat (ConstructorPat (Tuple 2, [Pat (XPat "generated0", None); Pat (IgnorePat, None)]), None),
                         None,
                         X "generated0"])))

        fn' |> should equal expected

    
    [<Test>]
    member this.dissallowsUndeclaredIdentifiers() =
        let fn = ExLambda ([ExXPat "x", None], ExX "generated1")   
        (fun () -> translateFn fn emptyTransEnv |> ignore)
            |> should throw typeof<ParseException>

    [<Test>]
    member this.returnTypeForMultipleRecursive() =
        let fn = ExRecursive ("f", [ExXPat "x", Some ExInt; ExIgnorePat, Some ExInt], Some ExInt, ExX "x")   
        let translated = translateFn fn emptyTransEnv
        
        let expected = 
            Fn <| Recursive ("generated1", Some <| Function (Int', Int'), "generated3",
                Fn <| Lambda ("generated2",
                    Match (tupled [X "generated3"; X "generated2"],
                        [Pat (ConstructorPat (Tuple 2, [Pat (XPat "generated0", Some Int'); Pat (IgnorePat, Some Int')]), None),
                         None,
                         X "generated0"])))
        
        translated |> should equal expected
    
    [<Test>]
    member this.completesParameterTypes() =
        let fn = ExRecursive ("f", [ExXPat "x", None; ExIgnorePat, Some ExInt], Some ExInt, ExX "x")   
        let translated = translateFn fn emptyTransEnv
        
        let varTyp = VarType ("type0", [])
        let expected = 
            Fn <| Recursive ("generated1", Some <| Function (Int', Int'), "generated3",
                Fn <| Lambda ("generated2",
                    Match (tupled [X "generated3"; X "generated2"],
                        [Pat (ConstructorPat (Tuple 2, [Pat (XPat "generated0", Some varTyp); Pat (IgnorePat, Some Int')]), None),
                         None,
                         X "generated0"])))
        
        translated |> should equal expected
       
[<TestFixture>]
type DeclarationTranslationTests() =

    [<Test>]
    member this.generatesSubstitutions() =
        let term = DeclConst ((ExXPat "x", None), ExConstructor (I 3))
        let assocs, env' = translateDecl term emptyTransEnv

        assocs |> should equal [Term (Pat (XPat "generated0", None), Constructor (I 3))]
        env'.idents |> should equal (Map.empty.Add ("x", "generated0"))
    
    [<Test>]
    member this.recursiveFunctions() =
        let term = DeclFunc (true, "f", [ExXPat "x", Some (ExConstType (Int, []))], None, ExX "f")
        let assocs, env' = translateDecl term emptyTransEnv

        let generatedFn = Fn (Recursive <|
            ("generated2", None, "generated3", Match (X "generated3", [Pat (XPat "generated1", Some (ConstType (Int, []))), None, X "generated2"])))
        assocs.Head |> should equal (Term (Pat (XPat "generated0", None), generatedFn))
        env'.idents |> should equal (Map.empty.Add ("f", "generated0"))
   
    [<Test>]
    member this.partialTypedFunctions() =
        let term = DeclFunc (false, "f", [ExXPat "x", None], Some ExInt, ExX "x")
        let assocs, env' = translateDecl term emptyTransEnv

        let varType = VarType ("type0", [])

        let generatedFn = 
            Fn <| Lambda ("generated2", 
                    Match (X "generated2",
                        [Pat (XPat "generated1", Some (VarType ("type0", []))),
                         None,
                         X "generated1"]))
        assocs.Head |> should equal (Term (Pat (XPat "generated0", Some (Function (varType, Int'))), generatedFn))
        env'.idents |> should equal (Map.empty.Add ("f", "generated0"))
        
    [<Test>]
    member this.partialTypedMultiParameterFunctions() =
        let term = DeclFunc (false, "f", [ExXPat "x", None; ExIgnorePat, Some ExInt], Some ExInt, ExX "x")
        let assocs, env' = translateDecl term emptyTransEnv

        let varType = VarType ("type0", [])

        let generatedFn = 
            Fn <| Lambda ("generated3", 
                Fn <| Lambda ("generated2", 
                        Match (tupled [X "generated3"; X "generated2"],
                            [Pat (ConstructorPat (Tuple 2, [Pat (XPat "generated1", Some (VarType ("type0", []))); Pat (IgnorePat, Some Int')]), None),
                             None,
                             X "generated1"])))
        assocs.Head |> should equal (Term (Pat (XPat "generated0", Some (Function (varType, Function (Int', Int')))), generatedFn))
        env'.idents |> should equal (Map.empty.Add ("f", "generated0"))
        
    [<Test>]
    member this.partialTypedMultiParameterRecursiveFunctions() =
        let term = DeclFunc (true, "f", [ExXPat "x", None; ExIgnorePat, Some ExInt], Some ExInt, ExX "x")
        let assocs, env' = translateDecl term emptyTransEnv

        let varType = VarType ("type0", [])

        let generatedFn = 
            Fn <| Recursive ("generated2", Some <| Function (Int', Int'), "generated4", 
                Fn <| Lambda ("generated3", 
                        Match (tupled [X "generated4"; X "generated3"],
                            [Pat (ConstructorPat (Tuple 2, [Pat (XPat "generated1", Some (VarType ("type0", []))); Pat (IgnorePat, Some Int')]), None),
                             None,
                             X "generated1"])))
        assocs.Head |> should equal (Term (Pat (XPat "generated0", Some (Function (varType, Function (Int', Int')))), generatedFn))
        env'.idents |> should equal (Map.empty.Add ("f", "generated0"))

    [<Test>]
    member this.recursiveTypedFunctions() =
        let term = DeclFunc (true, "f", [ExXPat "x", Some ExInt], Some ExInt, ExX "x")
        let assocs, env' = translateDecl term emptyTransEnv

        let generatedFn = 
            Fn <| Recursive ("generated2", Some Int', "generated3", 
                Match (X "generated3", [Pat (XPat "generated1", Some Int'), None, X "generated1"]))
        assocs.Head |> should equal (Term (Pat (XPat "generated0", Some (Function (Int', Int'))), generatedFn))
        env'.idents |> should equal (Map.empty.Add ("f", "generated0"))

    [<Test>]
    member this.typedFunctions() =
        let term = DeclFunc (false, "f", [ExXPat "x", Some ExInt], Some ExInt, ExX "x")
        let assocs, env' = translateDecl term emptyTransEnv

        let generatedFn = 
            Fn <| Lambda ("generated2", 
                Match (X "generated2", [Pat (XPat "generated1", Some Int'), None, X "generated1"]))
        assocs.Head |> should equal (Term (Pat (XPat "generated0", Some (Function (Int', Int'))), generatedFn))
        env'.idents |> should equal (Map.empty.Add ("f", "generated0"))

    [<Test>]
    member this.addsAliases() =
       let term = DeclAlias ("a", ExConstType (Int, []))
       let assocs, env' = translateDecl term emptyTransEnv
       assocs |> should equal []
       env'.typeAliases |> should equal (Map.empty.Add("a", ConstType (Int, [])))


      
    