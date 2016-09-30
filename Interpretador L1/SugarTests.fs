module SugarTests

open NUnit.Framework
open FsUnit
open Definition
open Sugar

let simpleLetAndCond = (

    "let x: Int = 3;
let y: Int = 4;
let b: Bool = false;
if b then
	(x + y)
else
	(x - y)".Replace("\r", "").Replace("    ", "\t"), 

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

let nestedIf = (
    "if true then
    if false then
        1
    else
        2
else
    3".Replace("\r", "").Replace("    ", "\t"),
        
    Cond(True, Cond(False, I(1), I(2)), I(3))
)

let nestedFn = (
    "fn(x: Int) {
    fn(y: Int) {
        (x + y)
    }
}
"       .Replace("\r", "").Replace("    ", "\t"),
     
     Fn("x", Int, Fn("y", Int, OP(X("x"), Add, X("y"))))
)

let app3 = (
    "let app3: (Int -> Int) -> Int = fn(f: Int -> Int) {
    f 3
}
;
app3 fn(x: Int) {
    (x + 1)
}
".Replace("\r", "").Replace("    ", "\t"),
    
    Let("app3", Function(Function(Int, Int), Int), 
        Fn("f", Function(Int, Int), OP(X("f"), Application, I(3))),
            OP(X("app3"), Application, Fn("x", Int, OP(X("x"), Add, I(1)))))
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
        print (snd simpleLetAndCond) |> should equal (fst simpleLetAndCond)
        
    [<Test>]
    [<Category("OP")>]
    [<Category("Value")>]
    member that.opRight() =
        print (snd opRight) |> should equal (fst opRight)
        
    [<Test>]
    [<Category("OP")>]
    [<Category("Value")>]
    member that.opLeft() =
        print (snd opLeft) |> should equal (fst opLeft)
        
    [<Test>]
    [<Category("OP")>]
    [<Category("Value")>]
     member that.opCenter() =
        print (snd opCenter) |> should equal (fst opCenter)

    [<Test>]
    [<Category("Cond")>]
    [<Category("Value")>]
     member that.nestedIf() =
        print (snd nestedIf) |> should equal (fst nestedIf)

    [<Test>]
    [<Category("Fn")>]
    [<Category("OP")>]
    [<Category("X")>]
    [<Category("Value")>]
     member that.nestedFn() =
        print (snd nestedFn) |> should equal (fst nestedFn)

    [<Test>]
    [<Category("Let")>]
    [<Category("Fn")>]
    [<Category("App")>]
    [<Category("OP")>]
    [<Category("X")>]
    [<Category("Type")>]
    [<Category("Value")>]
     member that.app3() =
        print (snd app3) |> should equal (fst app3)

let compare text term =
    parseTerm text |> should equal term

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
        compare (fst simpleLetAndCond) (snd simpleLetAndCond)

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

    [<Test>]
    [<Category("Cond")>]
    [<Category("Value")>]
     member that.nestedIf() =
        parseTerm (fst nestedIf) |> should equal (snd nestedIf)

    [<Test>]
    [<Category("Fn")>]
    [<Category("OP")>]
    [<Category("X")>]
    [<Category("Value")>]
     member that.nestedFn() =
        parseTerm (fst nestedFn) |> should equal (snd nestedFn)

    [<Test>]
    [<Category("Let")>]
    [<Category("Fn")>]
    [<Category("App")>]
    [<Category("OP")>]
    [<Category("X")>]
    [<Category("Type")>]
    [<Category("Value")>]
     member that.app3() =
        parseTerm (fst app3) |> should equal (snd app3)