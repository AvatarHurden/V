module Tests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation

[<TestFixture>]
type TestReplace() = 

    [<Test>]
    member that.``replace let``() =
        let app = App(Fn("x", Int, OP(X("x"), Add, I(1))), OP(X("x"), Add, X("y")))
        let defy = Let("y", Int, I(40), app)
        let defx = Let("x", Int, OP(I(10), Add, X("y")), defy)

        let shouldBe = Let("x", Int, OP(I(10), Add, I(4)), defy) in
        (replace "y" (I(4)) defx) |> should equal shouldBe


[<TestFixture>]
type TestEval() =

    [<Test>]
    member that.``eval factorial``() =
        let fatMult = OP(X("x"), Multiply, App(X("fat"), OP(X("x"), Subtract, I(1))))
        let fnTerm =  Cond(OP(X("x"), Equal, I(0)), I(1), fatMult)
        let fat = LetRec("fat", Int, Int, "x", fnTerm, App(X("fat"), I(5))) in

        eval fat |> should equal (I(120))