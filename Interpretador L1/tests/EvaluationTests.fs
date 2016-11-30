module EvaluationTests

open NUnit.Framework
open FsUnit
open Parser
open Definition
open Evaluation
open TypeInference

let facList =
    Let("faclist", Some <| Function(Int, List Int), 
        RecFn("faclist", Some <| List Int, "x", Some Int, 
            Let ("fac", Some <| Function(Int, Int),
                RecFn("fac", Some Int, "y", Some Int, 
            Cond(
                OP(X("y"), Equal, I(0)),
                 I(1),
                        OP(X("y"), Multiply, OP(X("fac"), Application, OP(X("y"), Subtract, I(1)))))),
            Cond(
                OP(X("x"), Equal, I(0)),
                     Nil,
                     OP(OP(X("fac"), Application, X("x")), 
                        Cons, 
                            OP(X("faclist"), Application, OP(X("x"), Subtract, I(1))))))),
            OP(X("faclist"), Application, I(5)))

let compare (text, term) =
    let evaluated = evaluate <| parse text
    evaluated |> should equal term

let compareDirect term result =
    let typ = typeInfer term
    let evaluated = evaluate term
    evaluated |> should equal result

let throwsWrongExpression term =
    (fun () -> evaluate term |> ignore) |> should throw typeof<WrongExpression>


[<TestFixture>]
type TestEval() =

    [<Test>]
    member that.``factorial``() =
        let fatMult = OP(X("x"), Multiply, OP(X("fat"), Application, OP(X("x"), Subtract, I(1))))
        let fnTerm =  Cond(OP(X("x"), Equal, I(0)), I(1), fatMult)
        let fat = Let("fat", Some <| Function (Int, Int), 
            RecFn("fat", Some Int, "x", Some Int, fnTerm), OP(X("fat"), Application, I(5)))

        evaluate fat |> should equal (ResI(120))

    [<Test>]
    member that.faclist() =
        evaluate facList |> should equal <|
            ResCons(ResI 120, ResCons(ResI 24, ResCons(ResI 6, ResCons(ResI 2, ResCons(ResI 1, ResNil)))))
           

    [<Test>]
    member that.LCM() =
        "let modulo(x:Int): Int -> Int {
    let rec d(y:Int): Int {
        if x = 0 then  
            raise
        else if y<x then
            y
        else
            d(y-x)
    };
    (\y:Int => d y)
};
let rec gcd(x:Int): Int -> Int {
    let f(y: Int): Int {
        try
            gcd y (modulo y x) 
        except
            x    
    };
    (\y: Int => f y)
};
let lcm(x:Int): Int -> Int {
    (\y: Int => x*y/(gcd x y))
};
lcm 121 11*15" |> parse |> evaluate |> should equal <| ResI 1815

    [<Test>]
    member that.orderLists() =
        compare ("[1,2,3] <= [3,4,5]", ResTrue)
        compare ("[1,2,3] > [1,2]", ResTrue)
        compare ("[5,2,3] < [3,4,5]", ResFalse)
        compare ("[] <= [3,4,5]", ResTrue)

    [<Test>]
    member that.equateLists() =
        compare ("[1,2,3] = [3,4,5]", ResFalse)
        compare ("[1,2,3] != [1,2]", ResTrue)
        compare ("[1,2,3] = [1]", ResFalse)
        compare ("[3,4,5] = [3,4,5]", ResTrue)
        compare ("[true, false, true] = [true, false, true]", ResTrue)

    [<Test>]
    member that.shortCircuit() =
        compare ("true || raise", ResTrue)
        compare ("false && true", ResFalse)
        compare ("false && raise", ResFalse)
        compare ("let t = []; (empty? t) || (head t) = 0", ResTrue)


[<TestFixture>]
type TestRecordEval() =

    [<Test>]
    member that.singleton() =
        throwsWrongExpression <| Record (None, [I 3])

    [<Test>]
    member that.singletonRecord() =
        throwsWrongExpression <| Record (Some <| seq(["h"]), [I 3])

    [<Test>]
    member that.unmatchingLists() =
        throwsWrongExpression <| Record (Some <| seq(["h"]), [I 3; True])

    [<Test>]
    member that.twoTuple() =
        compareDirect (Record(None, [I 3; True])) <|
             ResRecord(None, [ResI 3; ResTrue])

    [<Test>]
    member that.twoTupleNames() =
        compareDirect (Record(Some <| seq(["a";"b"]), [I 3; True])) <|
             ResRecord(Some <| seq(["a";"b"]), [ResI 3; ResTrue])
             
    [<Test>]
    member that.repeatedNames() =
        throwsWrongExpression <| Record(Some <| seq(["a";"a"]), [I 3; Raise])

    [<Test>]
    member that.invalidMember() =
        compareDirect (Record(Some <| seq(["a";"b"]), [I 3; Raise])) <|
             ResRaise

    [<Test>]
    member that.accessIndex() =
        compareDirect 
            (OP (I 3, Add, 
                Project (IntProjection 1, Record(Some <| seq(["a";"b"]), [I 3; True]))))
            ResTrue
    
    [<Test>]
    member that.accessIndexOutOfRange() =
        throwsWrongExpression <|
            (Project (IntProjection 2, Record(Some <| seq(["a";"b"]), [I 3; True])))
            
    [<Test>]
    member that.accessName() =
        compareDirect
            (Project (StringProjection "a", Record(Some <| seq(["a";"b"]), [I 3; True])))
            (ResI 3)
    
    [<Test>]
    member that.accessNameOutOfRange() =
        throwsWrongExpression <|
            (Project (StringProjection "c", Record(Some <| seq(["a";"b"]), [I 3; True])))
             
    [<Test>]
    member that.accessNameUnnamed() =
        throwsWrongExpression <|
            (Project (StringProjection "c", Record(None, [I 3; True])))
             
