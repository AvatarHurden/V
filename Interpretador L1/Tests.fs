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