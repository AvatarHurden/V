module Tests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation

[<TestFixture>]
type TestReplace() = 

    [<Test>]
    member that.``replace let``() =
        let app = App(Fn(Ident.X("x"), Int, OP(X(Ident.X("x")), Add, I(1))), OP(X(Ident.X("x")), Add, X(Ident.X("y")))) in
        let defy = Let(Ident.X("y"), Int, I(40), app) in
        let defx = Let(Ident.X("x"), Int, OP(I(10), Add, X(Ident.X("y"))), defy) in

        let shouldBe = Let(Ident.X("x"), Int, OP(I(10), Add, I(4)), defy) in
        (replace (Ident.X("y")) (I(4)) defx) |> should equal shouldBe


[<TestFixture>]
type TestEval() =

    [<Test>]
    member that.``eval factorial``() =
        let fatName = Ident.X("fat")
        let xName = Ident.X("x")
        let fatMult = OP(X(xName), Multiply, App(X(fatName), OP(X(xName), Subtract, I(1))))
        let fnTerm =  Cond(OP(X(xName), Equal, I(0)), I(1), fatMult)
        let fat = LetRec(fatName, Int, Int, xName, fnTerm, App(X(fatName), I(5))) in

        eval fat |> should equal (I(120))