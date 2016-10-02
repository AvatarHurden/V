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

    Let("x", Some Int, I(3), 
        Let("y", Some Int, I(4), 
            Let("b", Some Bool, False, 
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
}".Replace("\r", "").Replace("    ", "\t"),
     
     Fn("x", Some Int, Fn("y", Some Int, OP(X("x"), Add, X("y"))))
)

let app3 = (
    "let app3: (Int -> Int) -> Int = fn(f: Int -> Int) {
    f 3
};
app3 fn(x: Int) {
    (x + 1)
}".Replace("\r", "").Replace("    ", "\t"),
    
    Let("app3", Function(Function(Int, Int), Int) |> Some, 
        Fn("f", Function(Int, Int) |> Some, OP(X("f"), Application, I(3))),
            OP(X("app3"), Application, Fn("x", Some Int, OP(X("x"), Add, I(1)))))
)

let nestedLet = (
    "let banana  :  (   Bool  ->  Int  )->Int   =let x:Int=4;x+4;
    let x: Int = 2*2;
    let y:Int=6-(1+1+1);
    x+banana+y    
    ",
    
    Let("banana", Function(Function(Bool, Int), Int) |> Some,
        Let("x", Some Int, I(4), OP(X("x"), Add, I(4))),
        Let("x", Some Int, OP(I(2), Multiply, I(2)),
            Let("y", Some Int, OP(I(6), Subtract, OP(OP(I(1), Add, I(1)), Add, I(1))),
                OP(OP(X("x"), Add, X("banana")), Add, X("y")))))
)

let factorial = (
    "let rec fat(x: Int): Int {
        if x = 0 then 1 else x*(fat (x-1))
     };
     fat 5",
    
    LetRec("fat", Some Int, Some Int, "x", 
        Cond(OP(X("x"), Equal, I(0)), I(1), 
            OP(X("x"), Multiply, OP(X("fat"), Application, OP(X("x"), Subtract, I(1))))), 
        OP(X("fat"), Application, I(5)))
)

let simpleTry = (
    "try
        if true then raise else 1
     except
        fn(x: Int) { x+3 } 4",
        
     Try(
        Cond(True, Raise, I(1)),
        OP(Fn("x", Some Int, OP(X("x"), Add, I(3))), Application, I(4))
        )
)

let letRecList = (
    "let rec sum(x: [Int]): Int {
        if empty? x then 0 else (head x)+(sum(tail x))
    };
    sum(4::3::2::1::nil)", 
    
    LetRec("sum", List(Int) |> Some, Some Int, "x",
        Cond(IsEmpty(X("x")), 
            I(0), 
            OP(Head(X("x")), Add, OP(X("sum"), Application, Tail(X("x"))))),
            
            OP(X("sum"), Application, 
                OP(I(4), Cons, OP(I(3), Cons, OP(I(2), Cons, OP(I(1), Cons, Nil))))))
)

let facList = (
    "let rec faclist(x: Int): [Int] {
    let rec fac(y: Int): Int {
        if y = 0 then 1 else y*(fac (y-1))
    };
    if x = 0 then
        nil
    else
        (fac x) :: (faclist (x-1))
};
faclist 5",

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
    [<Category("Type")>]
    [<Category("X")>]
    [<Category("Value")>]
     member that.nestedFn() =
        parseTerm (fst nestedFn) |> should equal (snd nestedFn)

    [<Test>]
    [<Category("Let")>]
    [<Category("OP")>]
    [<Category("Type")>]
    [<Category("X")>]
    [<Category("Value")>]
     member that.nestedLet() =
        parseTerm (fst nestedLet) |> should equal (snd nestedLet)

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

    [<Test>]
    [<Category("LetRec")>]
    [<Category("Cond")>]
    [<Category("OP")>]
    [<Category("Type")>]
    [<Category("Value")>]
    [<Category("X")>]
     member that.factorial() =
        parseTerm (fst factorial) |> should equal (snd factorial)

    [<Test>]
    [<Category("Try")>]
    [<Category("Raise")>]
    [<Category("Fn")>]
    [<Category("Cond")>]
    [<Category("OP")>]
    [<Category("Type")>]
    [<Category("Value")>]
    [<Category("X")>]
     member that.simpleTry() =
        parseTerm (fst simpleTry) |> should equal (snd simpleTry)

    [<Test>]
    [<Category("LetRec")>]
    [<Category("Raise")>]
    [<Category("IsEmpty")>]
    [<Category("Head")>]
    [<Category("Tail")>]
    [<Category("Cond")>]
    [<Category("OP")>]
    [<Category("Type")>]
    [<Category("Value")>]
    [<Category("X")>]
     member that.list() =
        parseTerm (fst letRecList) |> should equal (snd letRecList)
        
    [<Test>]
    [<Category("LetRec")>]
    [<Category("Raise")>]
    [<Category("Cond")>]
    [<Category("OP")>]
    [<Category("Type")>]
    [<Category("Value")>]
    [<Category("X")>]
     member that.facList() =
        parseTerm (fst facList) |> should equal (snd facList)

[<TestFixture>]
type TestParsePrint() =

    [<Test>]
    member that.``wrong type let``() =
        (fun () -> parseTerm "let x: = 3; x+3" |> ignore) |> should throw typeof<InvalidEntryText>

    [<Test>]
    member that.``wrong type named function``() =
        (fun () -> parseTerm "let x(y:Int) { y+2} ; x 3" |> ignore) |> should throw typeof<InvalidEntryText>

    [<Test>]
    member that.``named function``() =
        parseTerm "let x(y:Int): Int { y+2} ; x 3" |> print |> 
            should equal ("let x: Int -> Int = fn(y: Int) {
\t(y + 2)
};
x 3".Replace("\r", ""))

    [<Test>]
    member that.``let``() =
        parseTerm "let x = 4; x+4" |> print|> should equal
            ("let x = 4;
(x + 4)".Replace("\r", ""))

    [<Test>]
    member that.map() =
    parseTerm  "let t2 = 1::2::3::nil;
                let f = fn(x) {
                    (x * 2)
                };
                let rec map(l) {
                    if empty? l then
                        nil
                    else
                        (f head l)::map tail l
                };
                map t2" 
    |> print |> should equal
        ("let t2 = 1::2::3::nil;
let f = fn(x) {
    (x * 2)
};
let rec map(l) {
    if empty? l then
        nil
    else
        (f head l)::map tail l
};
map t2".Replace("\r", "").Replace("    ", "\t"))
