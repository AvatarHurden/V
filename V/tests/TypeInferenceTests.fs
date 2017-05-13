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

let shouldFail text =
    (fun () -> text |> parse |> typeInfer |> ignore) |> should throw typeof<TypeException> 
   
let compareDirect term typ =
    let evaluated = typeInfer term
    evaluated |> should equal typ

let shouldFailDirect term =
    (fun () -> term |> typeInfer |> ignore) |> should throw typeof<TypeException> 
    
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
                    f 4", Int) |> ignore) |> should throw typeof<TypeException>

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
        should throw typeof<TypeException>

    [<Test>]
    member that.extendedPatFunction() =
        compare ("let f {age: x, ...} = x + 1; f", 
            Function (VarType ("X529",[RecordLabel ("age",Int)]),Int))

    [<Test>]
    member that.simplePatFunction() =
        compare ("let f {age: x} = x + 1; f", 
            Function (Type.Record [("age", Int)],Int))

    [<Test>]
    member that.extendedPatMatch() =
        compare ("match {name: \"arthur\", age: 21, male: true} with
                    | {age: x, ...} when x > 50 -> 0
                    | {male: true, age: x, ...} when x < 30 -> 1
                    | _ -> 2", Int)

    [<Test>]
    member that.extendedPatMatchFunction() =
        compare ("let f x =
                    match x with
                    | {age: x, ...} when x > 50 -> 0
                    | {male: true, age: x, ...} when x < 30 -> 1
                    | _ -> 2
                    ; f", 
            Function (VarType ("X535",[RecordLabel ("male",Bool); RecordLabel ("age",Int)]),Int))

    [<Test>]
    member that.simplePatMatchFunction() =
        compare ("let f x =
                    match x with
                    | {age: x, ...} when x > 50 -> 0
                    | {male: true, age: x} when x < 30 -> 1
                    | _ -> 2
                    ; f", Function (Type.Record [("age", Int); ("male", Bool)],Int))


[<TestFixture>]
type TestMatchInfer() =

    [<Test>]
    member that.simpleUntyped() =
        compare ("let x = 3; x", Int)

    [<Test>]
    member that.simpleTyped() =
        compare ("let x: Int = 3; x", Int)

    [<Test>]
    member that.simpleTypedWrong() =
        shouldFail "let x: Char = 3; x"
            
    [<Test>]
    member that.simpleTuple() =
        compare ("let (x, y) = (3,4); x + y", Int)
           
    [<Test>]
    member that.simpleTupleInternalType() =
        compare ("let (x: [Int], y) = ([], 4); x", List Int)

    [<Test>]
    member that.simpleTupleExternalType() =
        compare ("let (x, y): (Int, Int) = (3,4); x", Int)
        
    [<Test>]
    member that.wrongTuple() =
        shouldFail "let (x, y) = (3,4, 5); x" 
               
    [<Test>]
    member that.simpleRecord() =
        compare ("let {a: x, b: y} = {a: 4, b: 5}; x + y", Int)

    [<Test>]
    member that.simpleRecordTyped() =
        compare ("let {a: x: Int, b: y} = {a: 4, b: 'c'}; x", Int)
        
    [<Test>]
    member that.wrongRecord() =
        shouldFail "let {a: x, b: y} = {a: 4, d: 'c'}; x"

    [<Test>]
    member that.wrongRecord2() =
        shouldFail "let {a: x, b: y} = {a: 4, b: 4, d: 'c'}; x"
        
    [<Test>]
    member that.wrongRecord3() =
        shouldFail "let {a: x, b: y} = {a: 4}; x"

    [<Test>]
    member that.listHead() =
        compare ("let x :: y = [3,4]; x", Int)

    [<Test>]
    member that.lisTail() =
        compare ("let x :: y = [3,4]; y", List Int)

    [<Test>]
    member that.listTyped() =
        compare ("let (x: Int) :: (y: [Int]) = [3,4]; y", List Int)

    [<Test>]
    member that.listTotalTyped() =
        compare ("let  ((x: Int) :: (y: [Int])): [Int] = [3,4]; y", List Int)

    [<Test>]
    member that.FnParamaterTuple() =
        compare ("\(x: Int,y: Char) -> (y,x)",
            (Function(Type.Tuple [Int; Char], Type.Tuple [Char;Int])))

    [<Test>]
    member that.FnParamater2Tuple() =
        compare ("\(x: Int,y: Char) -> x",
            (Function(Type.Tuple [Int; Char], Int)))

    [<Test>]
    member that.FnParamaterList() =
        compare ("\((x :: y): [Int]) -> (y,x)",
            (Function(List Int, Type.Tuple [List Int;Int])))

    [<Test>]
    member that.FnParamaterListPassingFailingParameter() =
        compare ("(\((x :: y): [Int]) -> (y, x)) []",
            (Type.Tuple [List Int;Int]))
    
    [<Test>]
    member that.differentTypesMatch() =
        shouldFail "let empty2 x =
	match x with
	| [] -> true
	| x :: xs when x = 'c' -> true
	| x :: xs when x < 3 -> false
;
empty2 [1,2,3]
"

    [<Test>]
    member that.emptyFunction() =
        compare ("let empty2 x =
	match x with
	| [] -> true
	| x :: xs -> false
;
empty2 []
", Bool)