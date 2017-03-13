module LazyEvaluationTests


open NUnit.Framework
open FsUnit
open Parser
open Definition
open LazyEvaluation

let compareDirect term result =
    let evaluated = lazyEvaluate term
    evaluated |> should equal result
    
let shouldFailDirect term =
    (fun () -> term |> lazyEvaluate |> ignore) |> should throw typeof<EvalException> 

let compare (text, term) =
    let evaluated = lazyEvaluate <| parse text
    evaluated |> should equal term

let shouldFail text =
    (fun () -> parse text |> lazyEvaluate |> ignore) |> should throw typeof<EvalException> 

[<TestFixture>]
type TestEval() =

    [<Test>]
    member that.``factorial``() =
        let fatMult = OP(X("x"), Multiply, OP(X("fat"), Application, OP(X("x"), Subtract, I(1))))
        let fnTerm = Cond(OP(X("x"), Equal, I(0)), I(1), fatMult)
        let fat = 
            Let(Var(XPattern "fat", Some <| Function (Int, Int)), 
                RecFn("fat", Some Int, Var(XPattern "x", Some Int), fnTerm), OP(X("fat"), Application, I(5)))

        lazyEvaluate fat |> should equal (ResI(120))

    [<Test>]
    member that.LCM() =
        compare (
        "let modulo x y = y - x*(y/x);
         let rec gcd x y =
            if y = 0 then
                x
            else
                gcd y (modulo y x)
         ;
         let lcm x y = x * y / gcd x y;
         lcm 121 (11*15)", ResI 1815)

    [<Test>]
    member that.orderLists() =
        compare ("[1,2,3] <= [3,4,5]", ResB true)
        compare ("[1,2,3] > [1,2]", ResB true)
        compare ("[1,2,3] > [1,2, raise]", ResRaise)
        compare ("[5,2,3] < [3,4,5]", ResB false)
        compare ("[5,raise, 2,3] < [3,4,5, raise]", ResB false)
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
        compare ("let x :: y :: z = [3,4,6]; z", 
            (ResCons (ResI 6, ResNil)))
        
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
