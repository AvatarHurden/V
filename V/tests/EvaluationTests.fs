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
lcm 121 11*15", ResConstructor (I 1815, []))

    [<Test>]
    member that.orderLists() =
        compare ("[1,2,3] <= [3,4,5]", ResConstructor (B true, []))
        compare ("[1,2,3] > [1,2]", ResConstructor (B true, []))
        compare ("[5,2,3] < [3,4,5]", ResConstructor (B false, []))
        compare ("[] <= [3,4,5]", ResConstructor (B true, []))

    [<Test>]
    member that.shortCircuit() =
        compare ("true || raise", ResConstructor (B true, []))
        compare ("false && true", ResConstructor (B false, []))
        compare ("false && raise", ResConstructor (B false, []))
        compare ("let t = []; (empty? t) || (head t) = 0", ResConstructor (B true, []))

[<TestFixture>]
type TestEquality() =

    [<Test>]
    member that.tuples() =
        compare ("(1,2,3) = (1,2,4)", ResConstructor (B false, []))
        compare ("(1,2,3) = (1,2,3)", ResConstructor (B true, []))
        shouldFail "(1,2,'c') = (1,2,4)"

    [<Test>]
    member that.records() =
        compare ("{a:1,b:2} = {b:2,a:1}", ResConstructor (B true, []))
        compare ("{a:1,b:2,c:3} = {a:1,b:2,c:4}", ResConstructor (B false, []))
        shouldFail "{a:1,b:2} = {b:2,a:1,c:4}"

    [<Test>]
    member that.lists() =
        compare ("[1,2,3] = [3,4,5]", ResConstructor (B false, []))
        compare ("[1,2,3] != [1,2]", ResConstructor (B true, []))
        compare ("[1,2,3] = [1]", ResConstructor (B false, []))
        compare ("[3,4,5] = [3,4,5]", ResConstructor (B true, []))
        compare ("[true, false, true] = [true, false, true]", ResConstructor (B true, []))
        
[<TestFixture>]
type TestMatchEval() =

    [<Test>]
    member that.simpleVar() =
        compare ("let x = 3; x", ResConstructor (I 3, []))
    
    [<Test>]
    member that.simpleBool() =
        compare ("let x = true;
            let true = true; x", ResConstructor (B true, []))
       
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
        compare ("let (x, y) = (3, 4); x", ResConstructor (I 7, []))

    [<Test>]
    member that.longList() =
        compare ("let x :: y :: [] = [3,4]; x + y", ResConstructor (I 7, []))
        
    [<Test>]
    member that.longListInvalid() =
        compare ("let x :: y :: [] = [3,4,6]; x + y", ResRaise)

    [<Test>]
    member that.longListTail() =
        compare ("let x :: y :: z = [3,4,6]; z", (ResConstructor (Cons, [ResConstructor (I 6, []); ResConstructor (Nil, [])])))
        
    [<Test>]
    member that.FnParamater() =
        compare ("(\(x,y) -> (y,x)) (3,4)", (ResTuple [ResConstructor (I 4, []); ResConstructor (I 3, [])]))
        
    [<Test>]
    member that.FnParamaterRecord() =
        compare ("(\{a: x, b: y} -> (y,x)) {a: 3, b: 4}", (ResTuple [ResConstructor (I 4, []); ResConstructor (I 3, [])]))

    [<Test>]
    member that.FnParamaterFail() =
        shouldFail "(\(x, y) -> (y,x)) (3,4,4)"
       
    [<Test>]
    member that.FnParamaterListPassingFailingParameter() =
        compare ("(\(x :: y) -> (y,x)) []", ResRaise)

    [<Test>]
    member that.RecFnParameter() =
        compare ("(rec count (x :: y) -> if empty? y then 1 else 1 + count y) [3,4,7]", ResConstructor (I 3, []))

    [<Test>]
    member that.RecFnParameterFail() =
        compare ("(rec count (x :: y) -> if empty? y then 1 else 1 + count y) []", ResRaise)

[<TestFixture>]
type Strictness() =
        [<Test>]
        member that.basic() =
            compare ("let f x = 3; f raise", ResRaise)

        [<Test>]
        member that.strict() =
            compare ("let f x y =
	    match x with
	    | 0 -> 0
	    | x -> x + y
    ;
    f 0 raise", ResRaise)

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
            compare ("[raise, raise, raise, 3] !! 3", ResRaise)
