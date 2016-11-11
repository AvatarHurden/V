module stdlibTests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation
open TypeInference
open Parser

let compare (text, term) =
    let parsed = parse text
    let typ = typeInfer <| parsed
    let evaluated = evaluate <| parsed
    evaluated |> should equal term

[<TestFixture>]
type Teststdlib() =

    [<Test>]
    member that.existsTrue() =
        compare ("exists [5] [[1],[2],[],[5]]", ResTrue)

    [<Test>]
    member that.existsFalse() =
        compare ("exists false [true, true, true]", ResFalse)

    [<Test>]
    member that.existsWrong() =
        (fun () -> compare ("exists (\x => x) []", True) |> ignore)
             |> should throw typeof<InvalidType>

    [<Test>]
    member that.indexOfPositive() =
        compare ("indexOf [5] [[1],[2],[],[5]]", ResI 3)

    [<Test>]
    member that.indexOfNegative() =
        compare ("indexOf false [true, true, true]", ResI -1)

    [<Test>]
    member that.indexOfWrong() =
        (fun () -> compare ("indexOf 4 [true]", Bool) |> ignore)
             |> should throw typeof<InvalidType>
             
    [<Test>]
    member that.maximumAndminimum() =
        compare ("minimum [[1],[2,4],[5]]", OP (I 1, Cons, Nil))
        compare ("maximum []", Raise)
        compare ("minimum [5, -3, 2, -56, 0, 10]", I -56)

    [<Test>]
    member that.sort() =
        compare ("sort [[1],[2,4],[],[5]]", evaluate <| parse "[[], [1], [2,4], [5]]")
        compare ("sort [5, -3, 2, -56, 0, 10]", evaluate <| parse "[-56,-3,0,2,5,10]")