module TypeDeclarationTests

open NUnit.Framework
open FsUnit
open TestHelpers
open Parser
open Definition
open Evaluation
open TypeInference
open Translation

let throwsWrongType text =
    let parsed = text |> parsePure |> flip translate stdlib.stdEnv
    (fun () -> typeInfer parsed |> ignore) |> should throw typeof<TypeException>

let throwsParseException text =
    (fun () -> text |> parsePure |> flip translate stdlib.stdEnv |> ignore) 
        |> should throw typeof<ParseException>
   
let hasType text typ =
    let parsed = text |> parsePure |> flip translate stdlib.stdEnv
    let typ' = typeInfer <| parsed
    typ' |> should equal typ

let equals text term =
    let parsed = text |> parsePure |> flip translate stdlib.stdEnv
    let typ = typeInfer <| parsed
    let evaluated = evaluate <| parsed
    evaluated |> should equal term

let equalsParsed text text' =
    let parsed = text |> parsePure |> flip translate stdlib.stdEnv
    let parsed' = text' |> parsePure |> flip translate stdlib.stdEnv
    let typ = typeInfer <| parsed
    let typ' = typeInfer <| parsed'
    let evaluated = evaluate <| parsed
    let evaluated' = evaluate <| parsed'
    evaluated |> should equal evaluated'

[<TestFixture>]
 type SimpleEnumDeclaration() =

    [<Test>]
    member this.allowsSimpleDeclaration() =
        equals "type Data = One; One" <| ResConstructor (Custom "One", [])

    [<Test>]
    member this.constructorHasCorrectType() =
        hasType "type Data = One; One" <| ConstType (CustomType "Data", [])

    [<Test>]
    member this.recognizesExplicitType() =
        equals "type Data = One;
                 let x: Data = One;
                 x" <| ResConstructor (Custom "One", [])

    [<Test>]
    member this.mismatchedTypeErrors() =
        throwsWrongType "type Data = One; let x: Data = 1; x"
    
    [<Test>]
    member this.requiresUpperCaseName() =
        throwsParseException "type data = One; 4"

    [<Test>]
    member this.requiresUpperCaseConstructor() =
        throwsParseException "type Data = one; 4"

    [<Test>]
    member this.requiresDeclaration() =
        throwsWrongType "type Data = One; Two"

    [<Test>]
    member this.repeatedConstructorCausesError() =
        throwsParseException "type Data = One | One; One"

    [<Test>]
    member this.repeatedConstructorShadows() =
        hasType "type Data = One | Two; type Data2 = One | Three; One"
            <| ConstType (CustomType "Data2", [])

    [<Test>]
    member this.typeIsStoredForVariable() =
        hasType "type Data = One | Two; let x = One; type Data2 = One | Three; x"
            <| ConstType (CustomType "Data", [])
    
    [<Test>]
    member this.allowsDeclarationWithMultipleValues() =
        equals "type Data = One | Two | Three; One" <| ResConstructor (Custom "One", [])

    [<Test>]
    member this.allowsOptionalLeadingPipe() =
        equals "type Data = 
                    | One 
                    | Two 
                    | Three; 
                One" <| ResConstructor (Custom "One", [])

    [<Test>]
    member this.matchExpressionWorksForSimpleDeclaration() =
        equals "type Data = One | Two | Three;
                let x = Two;
                match x with
                    | One -> 1
                    | Two -> 2
                    | Three -> 3" <| ResConstructor (I 2, [])

    [<Test>]
    member this.matchExpressionRequiresRightType() =
        throwsWrongType 
               "type Data = One | Two | Three;
                type Data2 = Banana;
                let x = Two;
                match x with
                    | One -> 1
                    | Two -> 2
                    | Banana -> 3"
    
    [<Test>]
    member this.matchExpressionFailsWithShadowing() =
        throwsWrongType 
               "type Data = One | Two | Three;
                let x = Two;
                type Data2 = One;
                match x with
                    | One -> 1
                    | Two -> 2
                    | Three -> 3"