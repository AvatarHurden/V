module TranslationTests

open NUnit.Framework
open FsUnit
open Definition
open Translation
open TestHelpers

[<TestFixture>]
type TestGeneratedMatches() =

    let baseText = "generated"

    [<Test>]
    member this.substitutesTypedVars() =
        let generated = baseText + "0"
        let source = ExFn (ExLambda([ExXPat "x", Some ExInt], ExX "x"))
        let expected = Fn(Lambda(generated, Match (X generated, [Pat (XPat "x", Some Int), None, X "x"])))

        let result = translate source emptyTransEnv

        result |> should equal expected

    [<Test>]
    member this.substitutesMultiple() =
        let generated1 = baseText + "0"
        let generated0 = baseText + "1"
        let source = ExFn (ExLambda([ExXPat "x", Some ExInt; ExXPat "y", None], ExX "x"))

        let tupled = App (App (Constructor (Tuple 2), X generated0), X generated1)
        let tupledPat = Pat (ConstructorPat (Tuple 2, [Pat (XPat "x", Some Int); Pat (XPat "y", None)]), None)
        let inner = Fn(Lambda(generated1, Match (tupled, [tupledPat, None, X "x"])))
        let expected = Fn (Lambda(generated0, inner))

        let result = translate source emptyTransEnv

        result |> should equal expected

    [<Test>]
    member this.keepsUntypedVars() =
        let source = ExFn (ExLambda([ExXPat "x", None], ExX "x"))
        let expected = Fn(Lambda("x", X "x"))

        let result = translate source emptyTransEnv

        result |> should equal expected

    [<Test>]
    member this.keepsMultipleUntyped() =
        let source = ExFn (ExLambda([ExXPat "x", None; ExXPat "y", None], ExX "x"))
        
        let inner = Fn(Lambda("y", X "x"))
        let expected = Fn (Lambda("x", inner))

        let result = translate source emptyTransEnv

        result |> should equal expected