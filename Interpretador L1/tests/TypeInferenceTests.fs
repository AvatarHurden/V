module TypeInferenceTests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation
open Parser
open TypeInference


let compare (text, typ) =
    let evaluated = typeInfer <| parse text
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
         compare ("[(let x = 3; x*2), 8, (\x -> x+1) 4]", List Int)

    [<Test>]
    member that.IntMap() =
        compare ("let rec map (f: Int -> Int) (ls: [Int]): [Int] =
    if empty? ls then
        nil
    else
        (f (head ls))::(map f (tail ls))
;
map (\x -> x + 1) [1,2,3,4]", List Int)

    [<Test>]
    member that.polymorphicIdentity() =
        compare ("let f x = if x = x then x else x;
                if (f true) then
                    f 1
                else
                    f 4", Int)

    [<Test>]
    member that.polymorphicRec() =
        compare ("let rec count ls = if empty? ls then 0 else 1 + count (tail ls);
                count [1,2,3] + count [true,false]", Int)

    [<Test>]
    member that.wrongPolymorphism() =
        (fun () -> compare ("let f x = head x;
                if (f [true]) then
                    f 1
                else
                    f 4", Int) |> ignore) |> should throw typeof<InvalidType>

    [<Test>]
    member that.polymorphicHead() =
        compare ("let f x = head x;
                if (f [true]) then
                    f [1]
                else
                    f [4]", Int)

    [<Test>]
    member that.multipleFolds() =
        compare ("if (fold (\\acc x -> if x then acc else false) true [true,true,false]) then
	fold (\\acc x -> acc + x) 0 [1,2,3]
else
	fold (\\acc x -> if x then acc+1 else acc) 0 [true,false,true]", Int)

    [<Test>]
    member that.wrongReduces() =
        (fun () -> 
            compare (
                "if (reduce (\\acc x -> x && acc) [true,true,false]) then
	        reduce (\\acc x -> acc + x) [1,2,3]
        else
	        reduce (\\acc x -> x || acc) [true,false,true]", Int) |> ignore) |> 
        should throw typeof<InvalidType>