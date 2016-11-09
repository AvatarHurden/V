module ParserTests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation
open Parser

let simpleLetAndCond = (

    "let x: Int = 3;
let y: Int = 4;
let b: Bool = false;
if b then
	(x + y)
else
	(x - y)", 

    (ResI -1)

)

let opRight = (
    "(1 * (2 + 3))",
    
    (ResI 5)
)

let opLeft = (
    "((1 + 2) * 3)",
    
    (ResI 9)
)

let opCenter = (
    "((1 + 2) * (3 + 4))",
    
    (ResI 21)
)

let nestedIf = (
    "if true then
    if false then
        1
    else
        2
else
    3",
        
    (ResI 2)
)

let nestedFn = (
    "fn(x: Int) {
    fn(y: Int) {
        (x + y)
    }
} 3 4",
     
    (ResI 7)
)

let app3 = (
    "let app3: (Int -> Int) -> Int = fn(f: Int -> Int) {
    f 3
};
app3 fn(x: Int) {
    (x + 1)
}",
    
    (ResI 4)
)

let nestedLet = (
    "let banana  :  (   Bool  ->  Int  )->Int   =let x:Int=4;x+4;
    let x: Int = 2*2;
    let y:Int=6-(1+1+1);
    x+banana+y    
    ",
    
    (ResI 15)
)

let factorial = (
    "let rec fat(x: Int): Int {
        if x = 0 then 1 else x*(fat (x-1))
     };
     fat 5",
    
    (ResI 120)
)

let simpleTry = (
    "try
        if true then raise else 1
     except
        fn(x: Int) { x+3 } 4",
        
     (ResI 7)
)

let letRecList = (
    "let rec sum(x: [Int]): Int {
        if empty? x then 0 else (head x)+(sum(tail x))
    };
    sum(4::3::2::1::nil)", 
    
    (ResI 10)
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
reverse <| faclist 5",

    ResCons(ResI 1, ResCons(ResI 2, ResCons(ResI 6, ResCons(ResI 24, ResCons(ResI 120, ResNil)))))
    
)

let compare (text, term) =
    let evaluated = evaluate <| parseTerm text (List.empty)
    evaluated |> should equal term


type TestParse() =

    [<Test>]
    member that.``simple let and cond``() =
        compare simpleLetAndCond

    [<Test>]
    member that.opRight() =
        compare opRight
        
    [<Test>]
    member that.opLeft() =
        compare opLeft
        
    [<Test>]
     member that.opCenter() =
        compare opCenter

    [<Test>]
     member that.nestedIf() =
        compare nestedIf

    [<Test>]
     member that.nestedFn() =
        compare nestedFn

    [<Test>]
     member that.nestedLet() =
        compare nestedLet

    [<Test>]
     member that.app3() =
        compare app3
    
    [<Test>]
     member that.factorial() =
        compare factorial  

    [<Test>]
     member that.simpleTry() =
        compare simpleTry

    [<Test>]
     member that.list() =
        compare letRecList
        
    [<Test>]
     member that.facList() =
        compare facList

[<TestFixture>]
type TestParsePrint() =

    [<Test>]
    member that.``wrong type let``() =
        (fun () -> parseTermPure "let x: = 3; x+3" (List.empty) |> ignore) |> should throw typeof<InvalidEntryText>

    [<Test>]
    member that.``wrong type named function``() =
        (fun () -> parseTermPure "let x(y:Int) { y+2} ; x 3" (List.empty) |> ignore) |> should throw typeof<InvalidEntryText>

    [<Test>]
    member that.``named function``() =
        compare ("let x(y:Int): Int { y+2} ; x 3", ResI 5)

    [<Test>]
    member that.``let``() =
        compare ("let x = 4; x+4", ResI 8)

    [<Test>]
    member that.map() =
        compare ("let t2 = 1::2::3::nil;
                    let f = fn(x) {
                        (x * 2)
                    };
                    map f t2",
            ResCons(ResI 2, ResCons(ResI 4, ResCons(ResI 6, ResNil))))

    [<Test>]
    member that.comprehension() =
        compare ("[x*2 for x in [1,2,3]]",
            ResCons(ResI 2, ResCons(ResI 4, ResCons(ResI 6, ResNil))))

    [<Test>]
    member that.recComprehension() =
        compare ("[[x*2 for x in [1,2,3]], [1,2,3], [x for x in [y for y in [1,2,3]]]]",
            evaluate (OP( OP(I 2, Cons, OP(I 4, Cons, OP(I 6, Cons, Nil))),
                Cons,
                OP( OP(I 1, Cons, OP(I 2, Cons, OP(I 3, Cons, Nil))),
                    Cons,
                    OP( OP(I 1, Cons, OP(I 2, Cons, OP(I 3, Cons, Nil))),
                        Cons,
                        Nil)))))

    [<Test>]
    member that.listValues() =
        compare ("[true,false,nil,0,1]",
            ResCons(ResTrue, ResCons(ResFalse, ResCons(ResNil, ResCons(ResI 0, ResCons(ResI 1, ResNil))))))

    [<Test>]
    member that.simpleRange() =
        compare ("[1..10]", (evaluate (parseTermPure "[1,2,3,4,5,6,7,8,9,10]" <| List.empty)))

    [<Test>]
    member that.range() =
        compare ("[1..3..10]", (evaluate (parseTermPure "[1,3,5,7,9]" <| List.empty)))

    [<Test>]
    member that.negativeRange() =
        compare ("[-30..-20..20]", (evaluate (parseTerm "[-30,-20,-10,0,10,20]" <| List.empty)))
        
    [<Test>]
    member that.subtractiveRange() =
        compare ("[5..4..0]", (evaluate (parseTermPure "[5,4,3,2,1,0]" <| List.empty)))