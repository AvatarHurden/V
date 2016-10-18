module EvaluationTests

open NUnit.Framework
open FsUnit
open Parser
open Definition
open Evaluation

let facList =
    LetRec("faclist", Some Int, List(Int) |> Some, "x", 
        LetRec("fac", Some Int, Some Int, "y", 
            Cond(
                OP(X("y"), Equal, I(0)),
                 I(1),
                 OP(X("y"), Multiply, OP(X("fac"), Application, OP(X("y"), Subtract, I(1))))),
            Cond(
                OP(X("x"), Equal, I(0)),
                     Nil,
                     OP(OP(X("fac"), Application, X("x")), 
                        Cons, 
                        OP(X("faclist"), Application, OP(X("x"), Subtract, I(1)))))),
            OP(X("faclist"), Application, I(5)))

[<TestFixture>]
type TestEval() =

    [<Test>]
    member that.``factorial``() =
        let fatMult = OP(X("x"), Multiply, OP(X("fat"), Application, OP(X("x"), Subtract, I(1))))
        let fnTerm =  Cond(OP(X("x"), Equal, I(0)), I(1), fatMult)
        let fat = LetRec("fat", Some Int, Some Int, "x", fnTerm, OP(X("fat"), Application, I(5))) in

        evaluate fat |> should equal (I(120))

    [<Test>]
    member that.faclist() =
        evaluate facList |> should equal 
            (OP(I(120), Cons, OP(I(24), Cons, OP(I(6), Cons, OP(I(2), Cons, OP(I(1), Cons, Nil))))))

    [<Test>]
    member that.LCM() =
        ("let modulo(x:Int): Int -> Int {
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
lcm 121 11*15" |> parseTermPure <| List.empty) |> evaluate |> should equal (I(1815))
