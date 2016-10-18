module TypeInferenceTests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation
open Parser
open TypeInference


let compare (text, typ) =
    let evaluated = typeInfer <| parseTerm text (List.empty)
    evaluated |> should equal typ


[<TestFixture>]
type TestTypeInfer() =

    [<Test>]
    member that.letAndCond () =
        compare ("let x: Int = 3;
        let y: Int = 4;
        let b: Bool = false;
        if b then
	        (x + y)
        else
	        (x - y)", Int)

    [<Test>]
    member that.IntList() =
         compare ("[(let x = 3; x*2), 8, (\x => x+1) 4]", List Int)

    [<Test>]
    member that.IntMap() =
        compare ("let rec map(f: Int -> Int, ls: [Int]): [Int] {
    if empty? ls then
        nil
    else
        (f (head ls))::(map f (tail ls))
};
map (\x => x + 1) [1,2,3,4]", List Int)