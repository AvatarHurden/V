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

let opRight = (
    "(1 + (2 + 3))",
    
    OP(I(1), Add, OP(I(2), Add, I(3)))
)

let opLeft = (
    "((1 + 2) + 3)",
    
    OP(OP(I(1), Add, I(2)), Add, I(3))
)

let opCenter = (
    "((1 + 2) + (3 + 4))",
    
    OP(OP(I(1), Add, I(2)), Add, OP(I(3), Add, I(4)))
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
        
    [<Test>]
    [<Category("OP")>]
    [<Category("Value")>]
    member that.opRight() =
        stringify (snd opRight) |> should equal (fst opRight)
        
    [<Test>]
    [<Category("OP")>]
    [<Category("Value")>]
    member that.opLeft() =
        stringify (snd opLeft) |> should equal (fst opLeft)
        
    [<Test>]
    [<Category("OP")>]
    [<Category("Value")>]
     member that.opCenter() =
        stringify (snd opCenter) |> should equal (fst opCenter)

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

    [<Test>]
    [<Category("OP")>]
    [<Category("Value")>]
    member that.opRight() =
        parseTerm (fst opRight) |> should equal (snd opRight)
        
    [<Test>]
    [<Category("OP")>]
    [<Category("Value")>]
    member that.opLeft() =
        parseTerm (fst opLeft) |> should equal (snd opLeft)
        
    [<Test>]
    [<Category("OP")>]
    [<Category("Value")>]
     member that.opCenter() =
        parseTerm (fst opCenter) |> should equal (snd opCenter)