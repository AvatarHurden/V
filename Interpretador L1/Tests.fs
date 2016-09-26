module Tests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation

[<TestFixture>]
type TestReplace() = 

    [<Test>]
    member that.``replace let``() =
        let app = App(Fn(Ident.X("x"), Int, OP(X(Ident.X("x")), Add, V(I(1)))), OP(X(Ident.X("x")), Add, X(Ident.X("y")))) in
        let defy = Let(Ident.X("y"), Int, V(I(40)), app) in
        let defx = Let(Ident.X("x"), Int, OP(V(I(10)), Add, X(Ident.X("y"))), defy) in

        let shouldBe = Let(Ident.X("x"), Int, OP(V(I(10)), Add, V(I(4))), defy) in
        (replace (Ident.X("y")) (V(I(4))) defx) |> should equal shouldBe


[<TestFixture>]
type TestEval() =

    [<Test>]
    member that.``eval factorial``() =
        let fatName = Ident.X("fat")
        let xName = Ident.X("x")
        let fatMult = OP(X(xName), Multiply, App(X(fatName), OP(X(xName), Subtract, V(I(1)))))
        let fnTerm =  Cond(OP(X(xName), Equal, V(I(0))), V(I(1)), fatMult)
        let fat = LetRec(fatName, Int, Int, xName, fnTerm, App(X(fatName), V(I(5)))) in

        eval fat |> should equal (V(I(120)))