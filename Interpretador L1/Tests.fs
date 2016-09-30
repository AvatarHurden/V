module Tests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation

[<TestFixture>]
type TestReplace() = 

    [<Test>]
    [<Category("Let")>]
    [<Category("Fn")>]
    [<Category("OP")>]
    [<Category("Value")>]
    [<Category("X")>]
    member that.``let``() =
        let app = OP(Fn("x", Int, OP(X("x"), Add, I(1))), Application, OP(X("x"), Add, X("y")))
        let defy = Let("y", Int, I(40), app)
        let defx = Let("x", Int, OP(I(10), Add, X("y")), defy)

        let shouldBe = Let("x", Int, OP(I(10), Add, I(4)), defy) in
        (replace "y" (I(4)) defx) |> should equal shouldBe


let facList =
    LetRec("faclist", Int, List(Int), "x", 
        LetRec("fac", Int, Int, "y", 
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
    [<Category("LetRec")>]
    [<Category("Cond")>]
    [<Category("OP")>]
    [<Category("Value")>]
    [<Category("X")>]
    member that.``factorial``() =
        let fatMult = OP(X("x"), Multiply, OP(X("fat"), Application, OP(X("x"), Subtract, I(1))))
        let fnTerm =  Cond(OP(X("x"), Equal, I(0)), I(1), fatMult)
        let fat = LetRec("fat", Int, Int, "x", fnTerm, OP(X("fat"), Application, I(5))) in

        eval fat |> should equal (I(120))

    [<Test>]
    [<Category("LetRec")>]
    [<Category("Raise")>]
    [<Category("Cond")>]
    [<Category("OP")>]
    [<Category("Type")>]
    [<Category("Value")>]
    [<Category("X")>]
    member that.faclist() =
        eval facList |> should equal 
            (OP(I(120), Cons, OP(I(24), Cons, OP(I(6), Cons, OP(I(2), Cons, OP(I(1), Cons, Nil))))))