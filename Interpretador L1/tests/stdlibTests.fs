module stdlibTests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation
open TypeInference
open Parser

let compare (text, term) =
    let parsed = parseTerm text (List.empty)
    let typ = typeInfer <| parsed
    let evaluated = evaluate <| parsed
    evaluated |> should equal term

[<TestFixture>]
type Teststdlib() =

    [<Test>]
    member that.existsTrue() =
        compare ("exists [5] [[1],[2],[],[5]]", True)

    [<Test>]
    member that.existsFalse() =
        compare ("exists false [true, true, true]", False)

    [<Test>]
    member that.existsWrong() =
        (fun () -> compare ("exists (\x => x) []", True) |> ignore)
             |> should throw typeof<InvalidType>

    [<Test>]
    member that.indexOfPositive() =
        compare ("indexOf [5] [[1],[2],[],[5]]", I 3)

    [<Test>]
    member that.indexOfNegative() =
        compare ("indexOf false [true, true, true]", I -1)

    [<Test>]
    member that.indexOfWrong() =
        (fun () -> compare ("indexOf 4 [true]", Bool) |> ignore)
             |> should throw typeof<InvalidType>