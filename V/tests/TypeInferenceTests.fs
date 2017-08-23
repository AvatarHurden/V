module TypeInferenceTests

open NUnit.Framework
open FsUnit
open Definition
open Translation
open Evaluation
open Parser
open TypeInference


let compare (text, typ) =
    let evaluated = text |> parsePure |> flip translate emptyTransEnv|> typeInfer
    evaluated |> should equal typ

let shouldFail text =
    (fun () -> text |> parsePure |> flip translate emptyTransEnv |> typeInfer |> ignore) |> should throw typeof<TypeException> 
   
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
	        (x - y)", ConstType (Int, []))

    [<Test>]
    member that.IntList() =
         compare ("[(let x = 3; x*2), 8, (\x -> x+1) 4]", ConstType (List, [ConstType (Int, [])]))

    [<Test>]
    member that.IntMap() =
        compare ("let rec map (f: Int -> Int) (ls: [Int]): [Int] =
    match ls with
    | [] -> []
    | x :: xs -> f x :: map f xs
;
map (\x -> x + 1) [1,2,3,4]", ConstType (List, [ConstType (Int, [])]))

    [<Test>]
    member that.polymorphicIdentity() =
        compare ("let f x = if x = x then x else x;
                if (f true) then
                    f 1
                else
                    f 4", (ConstType (Int, [])))

    [<Test>]
    member that.polymorphicRec() =
        compare ("let rec count ls = 
            match ls with
            | [] -> 0
            | x :: xs -> 1 + count xs
            ;
                count [1,2,3] + count [true,false]", (ConstType (Int, [])))

    [<Test>]
    member that.wrongPolymorphism() =
        (fun () -> compare ("let f x = head x;
                if (f [true]) then
                    f 1
                else
                    f 4", (ConstType (Int, []))) |> ignore) |> should throw typeof<TypeException>

    [<Test>]
    member that.polymorphicHead() =
        compare ("let head (x :: xs) = x;
                let f x = head x;
                if (f [true]) then
                    f [1]
                else
                    f [4]", (ConstType (Int, [])))

    [<Test>]
    member that.multipleFolds() =
        compare ("
let rec fold f acc ls =
    match ls with
    | [] -> acc
    | x :: xs -> fold f (f acc x) xs
;
if (fold (\\acc x -> if x then acc else false) true [true,true,false]) then
	fold (\\acc x -> acc + x) 0 [1,2,3]
else
	fold (\\acc x -> if x then acc+1 else acc) 0 [true,false,true]", (ConstType (Int, [])))

    [<Test>]
    member that.wrongReduces() =
        (fun () -> 
            compare (
                "if (reduce (\\acc x -> x && acc) [true,true,false]) then
	        reduce (\\acc x -> acc + x) [1,2,3]
        else
	        reduce (\\acc x -> x || acc) [true,false,true]", (ConstType (Int, []))) |> ignore) |> 
        should throw typeof<TypeException>

    [<Test>]
    member that.extendedPatFunction() =
        compare ("let f {age: x, ...} = x + 1; f", 
            Function (VarType ("X26791",[RecordLabel ("age",(ConstType (Int, [])))]),(ConstType (Int, []))))

    [<Test>]
    member that.simplePatFunction() =
        compare ("let f {age: x} = x + 1; f", 
            Function (Type.Record [("age", (ConstType (Int, [])))],(ConstType (Int, []))))

    [<Test>]
    member that.extendedPatMatch() =
        compare ("match {name: \"arthur\", age: 21, male: true} with
                    | {age: x, ...} when x > 50 -> 0
                    | {male: true, age: x, ...} when x < 30 -> 1
                    | _ -> 2", (ConstType (Int, [])))

    [<Test>]
    member that.extendedPatMatchFunction() =
        compare ("let f x =
                    match x with
                    | {age: x, ...} when x > 50 -> 0
                    | {male: true, age: x, ...} when x < 30 -> 1
                    | _ -> 2
                    ; f", 
            Function (VarType ("X28262",[RecordLabel ("male",(ConstType (Bool, []))); RecordLabel ("age",(ConstType (Int, [])))]),(ConstType (Int, []))))

    [<Test>]
    member that.simplePatMatchFunction() =
        compare ("let f x =
                    match x with
                    | {age: x, ...} when x > 50 -> 0
                    | {male: true, age: x} when x < 30 -> 1
                    | _ -> 2
                    ; f", Function (Type.Record [("age", ConstType (Int, [])); ("male", (ConstType (Bool, [])))],ConstType (Int, [])))


[<TestFixture>]
type TestMatchInfer() =

    [<Test>]
    member that.simpleUntyped() =
        compare ("let x = 3; x", ConstType (Int, []))

    [<Test>]
    member that.simpleTyped() =
        compare ("let x: Int = 3; x", ConstType (Int, []))

    [<Test>]
    member that.simpleTypedWrong() =
        shouldFail "let x: Char = 3; x"
            
    [<Test>]
    member that.simpleTuple() =
        compare ("let (x, y) = (3,4); x + y", ConstType (Int, []))
           
    [<Test>]
    member that.simpleTupleInternalType() =
        compare ("let (x: [Int], y) = ([], 4); x", ConstType (List, [ConstType (Int, [])]))

    [<Test>]
    member that.simpleTupleExternalType() =
        compare ("let (x, y): (Int, Int) = (3,4); x", ConstType (Int, []))
        
    [<Test>]
    member that.wrongTuple() =
        shouldFail "let (x, y) = (3,4, 5); x" 
               
    [<Test>]
    member that.simpleRecord() =
        compare ("let {a: x, b: y} = {a: 4, b: 5}; x + y", ConstType (Int, []))

    [<Test>]
    member that.simpleRecordTyped() =
        compare ("let {a: x: Int, b: y} = {a: 4, b: 'c'}; x", ConstType (Int, []))
        
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
        compare ("let x :: y = [3,4]; x", ConstType (Int, []))

    [<Test>]
    member that.lisTail() =
        compare ("let x :: y = [3,4]; y", ConstType (List, [ConstType (Int, [])]))

    [<Test>]
    member that.listTyped() =
        compare ("let (x: Int) :: (y: [Int]) = [3,4]; y", ConstType (List, [ConstType (Int, [])]))

    [<Test>]
    member that.listTotalTyped() =
        compare ("let  ((x: Int) :: (y: [Int])): [Int] = [3,4]; y", ConstType (List, [ConstType (Int, [])]))

    [<Test>]
    member that.FnParamaterTuple() =
        compare ("\(x: Int,y: Char) -> (y,x)",
            (Function(Type.Tuple [ConstType (Int, []); (ConstType (Char, []))], Type.Tuple [(ConstType (Char, []));ConstType (Int, [])])))

    [<Test>]
    member that.FnParamater2Tuple() =
        compare ("\(x: Int,y: Char) -> x",
            (Function(Type.Tuple [ConstType (Int, []); (ConstType (Char, []))], ConstType (Int, []))))

    [<Test>]
    member that.FnParamaterList() =
        compare ("\((x :: y): [Int]) -> (y,x)",
            (Function(ConstType (List, [ConstType (Int, [])]), Type.Tuple [ConstType (List, [ConstType (Int, [])]);ConstType (Int, [])])))

    [<Test>]
    member that.FnParamaterListPassingFailingParameter() =
        compare ("(\((x :: y): [Int]) -> (y, x)) []",
            (Type.Tuple [ConstType (List, [ConstType (Int, [])]);ConstType (Int, [])]))
    
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
empty2 []", (ConstType (Bool, [])))