module TypeInferenceTests

open NUnit.Framework
open FsUnit
open Definition
open Parser
open TypeInference


let compare (text, typ) =
    let evaluated, _ = typeInfer <| parse text
    evaluated |> should equal typ

let compareDirect term typ =
    let typ, (u: Unified) = typ
    let typ', u' = typeInfer term
    typ |> should equal typ'
    u |> should equal u'

let throwsInvalidType term =
    (fun () -> typeInfer term |> ignore) |> should throw typeof<InvalidType>


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

    [<Test>]
    member that.polymorphicIdentity() =
        compare ("let f(x) { if x = x then x else x };
                if (f true) then
                    f 1
                else
                    f 4", Int)

    [<Test>]
    member that.polymorphicRec() =
        compare ("let rec count(ls) { if empty? ls then 0 else 1 + count (tail ls) };
                count [1,2,3] + count [true,false]", Int)

    [<Test>]
    member that.wrongPolymorphism() =
        (fun () -> compare ("let f(x) { head x };
                if (f [true]) then
                    f 1
                else
                    f 4", Int) |> ignore) |> should throw typeof<InvalidType>

    [<Test>]
    member that.polymorphicHead() =
        compare ("let f(x) { head x };
                if (f [true]) then
                    f [1]
                else
                    f [4]", Int)

    [<Test>]
    member that.multipleFolds() =
        compare ("if (fold (\\acc, x => if x then acc else false) true [true,true,false]) then
	fold (\\acc, x => acc + x) 0 [1,2,3]
else
	fold (\\acc, x => if x then acc+1 else acc) 0 [true,false,true]", Int)

    [<Test>]
    member that.wrongReduces() =
        (fun () -> compare (
        "if (reduce (\\acc, x => x && acc) [true,true,false]) then
	reduce (\\acc, x => acc + x) [1,2,3]
else
	reduce (\\acc, x => x || acc) [true,false,true]", Int) |> ignore) |> 
        should throw typeof<InvalidType>

[<TestFixture>]
type TestTupleType() =

    [<Test>]
    member that.singleton() =
        throwsInvalidType <| Tuple [I 3]

    [<Test>]
    member that.singletonRecord() =
        throwsInvalidType <| Record (["h", I 3])

    [<Test>]
    member that.twoTuple() =
        compareDirect (Tuple [I 3; True]) <|
             (Type.Tuple [Int; Bool], Unified([]))

    [<Test>]
    member that.twoTupleNames() =
        compareDirect (Record ["a", I 3; "b", True]) <|
             (Type.Record ["a", Int; "b", Bool], Unified([]))

    [<Test>]
    member that.repeatedNames() =
        throwsInvalidType <| Record ["a", I 3; "a", True]

    [<Test>]
    member that.accessIndex() =
        let x0 = VarType <| Var ("VarType0")
        compareDirect (ProjectIndex (1, Record ["a", I 3; "b", True])) <|
            (x0, Unified([Subtype (Bool, x0)]))
    
    [<Test>]
    member that.accessIndexOutOfRange() =
        throwsInvalidType <|
            ProjectIndex (2, Record ["a", I 3; "b", True])
            
    [<Test>]
    member that.accessName() =
        let x0 = VarType <| Var ("VarType0")
        compareDirect
            (ProjectName ("a", Record ["a", I 3; "b", True]))
            (x0, Unified([Subtype (Int, x0)]))
    
    [<Test>]
    member that.accessNameOutOfRange() =
        throwsInvalidType <|
            (ProjectName ("c", Record ["a", I 3; "b", True]))
             
    [<Test>]
    member that.accessNameUnnamed() =
        throwsInvalidType <|
            ProjectName ("c", Tuple [I 3; True])