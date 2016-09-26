module SugarTests

open NUnit.Framework
open FsUnit
open Definition
open Sugar

let simpleLetAndCond = (

    ("let x: Int = 3 in
let y: Int = 4 in
let b: Bool = false in
if b then
	(x + y)
else
	(x - y)".Replace("\r", "")), 

    Let("x", Int, I(3), 
        Let("y", Int, I(4), 
            Let("b", Bool, False, 
                Cond(X("b"), 
                    OP(X("x"), Add, X("y")), 
                    OP(X("x"), Subtract, X("y"))))))

)


[<TestFixture>]
type TestStringify() =

    [<Test>]
    [<Category("Let")>]
    [<Category("Cond")>]
    [<Category("OP")>]
    [<Category("Value")>]
    [<Category("Type")>]
    [<Category("X")>]
    member that.``simple let and cond``() =
        stringify (snd simpleLetAndCond) |> should equal (fst simpleLetAndCond)


[<TestFixture>]
type TestParse() =

    [<Test>]
    [<Category("Let")>]
    [<Category("Cond")>]
    [<Category("OP")>]
    [<Category("Value")>]
    [<Category("Type")>]
    [<Category("X")>]
    member that.``simple let and cond``() =
        parse (fst simpleLetAndCond) |> should equal (snd simpleLetAndCond)