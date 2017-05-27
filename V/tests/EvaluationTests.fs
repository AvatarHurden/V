module EvaluationTests

open NUnit.Framework
open FsUnit
open Parser
open Definition
open Translation
open Evaluation

let compareDirect term result =
    let evaluated = evaluate term
    evaluated |> should equal result
    
let shouldFailDirect term =
    (fun () -> term |> evaluate |> ignore) |> should throw typeof<EvalException> 

let compare (text, term) =
    let evaluated = text |> parse |> flip translate stdlib.stdEnv |> evaluate
    evaluated |> should equal term

let shouldFail text =
    (fun () -> parse text |> flip translate stdlib.stdEnv |> evaluate |> ignore) |> should throw typeof<EvalException> 

[<TestFixture>]
type TestEval() =

    [<Test>]
    member that.``factorial``() =
        let fatMult = OP(X("x"), Multiply, OP(X("fat"), Application, OP(X("x"), Subtract, I(1))))
        let fnTerm = Cond(OP(X("x"), Equal, I(0)), I(1), fatMult)
        let fat = 
            Let(Pat(XPat "fat", Some <| Function (Int, Int)), 
                RecFn("fat", Some Int, Pat(XPat "x", Some Int), fnTerm), OP(X("fat"), Application, I(5)))

        evaluate fat |> should equal (ResI(120))

    [<Test>]
    member that.LCM() =
        compare ("
let rec gcd (x:Int) (y:Int) =
    match y with
    | 0 -> x
    | y -> gcd y (y % x)
;
let lcm (x:Int) (y:Int) =
    x*y/(gcd x y)
;
lcm 121 11*15", ResI 1815)

    [<Test>]
    member that.orderLists() =
        compare ("[1,2,3] <= [3,4,5]", ResB true)
        compare ("[1,2,3] > [1,2]", ResB true)
        compare ("[5,2,3] < [3,4,5]", ResB false)
        compare ("[] <= [3,4,5]", ResB true)

    [<Test>]
    member that.shortCircuit() =
        compare ("true || raise", ResB true)
        compare ("false && true", ResB false)
        compare ("false && raise", ResB false)
        compare ("let t = []; (empty? t) || (head t) = 0", ResB true)

[<TestFixture>]
type TestEquality() =

    [<Test>]
    member that.tuples() =
        compare ("(1,2,3) = (1,2,4)", ResB false)
        compare ("(1,2,3) = (1,2,3)", ResB true)
        shouldFail "(1,2,'c') = (1,2,4)"

    [<Test>]
    member that.records() =
        compare ("{a:1,b:2} = {b:2,a:1}", ResB true)
        compare ("{a:1,b:2,c:3} = {a:1,b:2,c:4}", ResB false)
        shouldFail "{a:1,b:2} = {b:2,a:1,c:4}"

    [<Test>]
    member that.lists() =
        compare ("[1,2,3] = [3,4,5]", ResB false)
        compare ("[1,2,3] != [1,2]", ResB true)
        compare ("[1,2,3] = [1]", ResB false)
        compare ("[3,4,5] = [3,4,5]", ResB true)
        compare ("[true, false, true] = [true, false, true]", ResB true)
        
[<TestFixture>]
type TestMatchEval() =

    [<Test>]
    member that.simpleVar() =
        compare ("let x = 3; x", ResI 3)
    
    [<Test>]
    member that.simpleBool() =
        compare ("let x = true;
            let true = true; x", ResB true)
       
    [<Test>]
    member that.wrongBool() =
        compare ("let x = true;
            let false = true; x", ResRaise)
            
    [<Test>]
    member that.matchWrongNumber() =
        compare ("let x = 2;
            let (3,y) = (x,3);
            y
            ", ResRaise)
    [<Test>]
    member that.simpleTuple() =
        compare ("let (x, y) = (3, 4); x", ResI 3)

    [<Test>]
    member that.longList() =
        compare ("let x :: y :: [] = [3,4]; x + y", ResI 7)
        
    [<Test>]
    member that.longListInvalid() =
        compare ("let x :: y :: [] = [3,4,6]; x + y", ResRaise)

    [<Test>]
    member that.longListTail() =
        compare ("let x :: y :: z = [3,4,6]; z", (ResCons (ResI 6, ResNil)))
        
    [<Test>]
    member that.FnParamater() =
        compare ("(\(x,y) -> (y,x)) (3,4)", (ResTuple [ResI 4; ResI 3]))
        
    [<Test>]
    member that.FnParamaterRecord() =
        compare ("(\{a: x, b: y} -> (y,x)) {a: 3, b: 4}", (ResTuple [ResI 4; ResI 3]))

    [<Test>]
    member that.FnParamaterFail() =
        shouldFail "(\(x, y) -> (y,x)) (3,4,4)"
       
    [<Test>]
    member that.FnParamaterListPassingFailingParameter() =
        compare ("(\(x :: y) -> (y,x)) []", ResRaise)

    [<Test>]
    member that.RecFnParameter() =
        compare ("(rec count (x :: y) -> if empty? y then 1 else 1 + count y) [3,4,7]", ResI 3)

    [<Test>]
    member that.RecFnParameterFail() =
        compare ("(rec count (x :: y) -> if empty? y then 1 else 1 + count y) []", ResRaise)

[<TestFixture>]
type NonStrictness() =
        [<Test>]
        member that.basic() =
            compare ("let f x = 3; f raise", ResI 3)

        [<Test>]
        member that.strict() =
            compare ("let f x y =
	    match x with
	    | 0 -> 0
	    | x -> x + y
    ;
    f 0 raise", ResI 0)

        [<Test>]
        member that.strict2() =
            compare ("let f x y =
	    match x with
	    | 0 -> 0
	    | x -> x + y
    ;
    f 1 raise
    ", ResRaise)

        [<Test>]
        member that.indexing() =
            compare ("[raise, raise, raise, 3] !! 3", ResI 3)
