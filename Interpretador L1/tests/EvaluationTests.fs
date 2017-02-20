module EvaluationTests

open NUnit.Framework
open FsUnit
open Parser
open Definition
open Evaluation

let facList =
    Let("faclist", Some <| Function(Int, List Int), 
        RecFn("faclist", Some <| List Int, "x", Some Int, 
            Let ("fac", Some <| Function(Int, Int),
                RecFn("fac", Some Int, "y", Some Int, 
                    Cond(
                        OP(X("y"), Equal, I(0)),
                         I(1),
                                OP(X("y"), Multiply, OP(X("fac"), Application, OP(X("y"), Subtract, I(1)))))),
                    Cond(
                        OP(X("x"), Equal, I(0)),
                             Nil,
                             OP(OP(X("fac"), Application, X("x")), 
                                Cons, 
                                    OP(X("faclist"), Application, OP(X("x"), Subtract, I(1))))))),
                    OP(X("faclist"), Application, I(5)))

let compareDirect term result =
    let evaluated = evaluate term
    evaluated |> should equal result
    
let shouldFailDirect term =
    (fun () -> term |> evaluate |> ignore) |> should throw typeof<EvalException> 

let compare (text, term) =
    let evaluated = evaluate <| parse text
    evaluated |> should equal term

let shouldFail text =
    (fun () -> parse text |> evaluate |> ignore) |> should throw typeof<EvalException> 

[<TestFixture>]
type TestEval() =

    [<Test>]
    member that.``factorial``() =
        let fatMult = OP(X("x"), Multiply, OP(X("fat"), Application, OP(X("x"), Subtract, I(1))))
        let fnTerm = Cond(OP(X("x"), Equal, I(0)), I(1), fatMult)
        let fat = 
            Let("fat", Some <| Function (Int, Int), 
                RecFn("fat", Some Int, "x", Some Int, fnTerm), OP(X("fat"), Application, I(5)))

        evaluate fat |> should equal (ResI(120))

    [<Test>]
    member that.faclist() =
        evaluate facList |> should equal <|
            ResCons(ResI 120, ResCons(ResI 24, ResCons(ResI 6, ResCons(ResI 2, ResCons(ResI 1, ResNil)))))
           

    [<Test>]
    member that.LCM() =
        "let modulo (x:Int): Int -> Int =
    let rec d (y:Int): Int =
        if x = 0 then  
            raise
        else if y<x then
            y
        else
            d (y-x)
    ;
    (\(y:Int) -> d y)
;
let rec gcd (x:Int): Int -> Int =
    let f (y: Int): Int =
        try
            gcd y (modulo y x) 
        except
            x
    ;
    (\(y: Int) -> f y)
;
let lcm (x:Int): Int -> Int =
    (\(y: Int) -> x*y/(gcd x y))
;
lcm 121 11*15" |> parse |> evaluate |> should equal <| ResI 1815

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
        compareDirect
            (Let2 (Var(XPattern "x", None), I 3, X "x"))
            (ResI 3)

    [<Test>]
    member that.simpleTuple() =
        let pattern = Var( TuplePattern(
            [Var(XPattern "x", None); Var(XPattern "y", None)]), None)
        compareDirect
            (Let2 (pattern, Tuple([I 3; I 4]), OP(X "x", Add, X "y")))
            (ResI 7)

    [<Test>]
    member that.longList() =
        let pattern = Var( ConsPattern(
            Var(XPattern "x", None), Var( ConsPattern(
                Var(XPattern "y", None), Var (NilPattern, None)), None)), None)
        compareDirect
            (Let2 (pattern, OP(I 3, Cons, OP (I 4, Cons, Nil)), OP(X "x", Add, X "y")))
            (ResI 7)

    [<Test>]
    member that.longListInvalid() =
        let pattern = Var( ConsPattern(
            Var(XPattern "x", None), Var( ConsPattern(
                Var(XPattern "y", None), Var (NilPattern, None)), None)), None)
        compareDirect
            (Let2 (pattern, OP(I 3, Cons, OP (I 4, Cons, OP(I 6, Cons, Nil))), OP(X "x", Add, X "y")))
            (ResRaise)

    [<Test>]
    member that.longListTail() =
        let pattern = Var( ConsPattern(
            Var(XPattern "x", None), Var( ConsPattern(
                Var(XPattern "y", None), Var (XPattern "z", None)), None)), None)
        compareDirect
            (Let2 (pattern, OP(I 3, Cons, OP (I 4, Cons, OP(I 6, Cons, Nil))), X "z"))
            (ResCons (ResI 6, ResNil))

    [<Test>]
    member that.FnParamater() =
        let pattern = Var( TuplePattern(
            [Var(XPattern "x", None); Var(XPattern "y", None)]), None)
        compareDirect
            (OP (Fn2 (pattern, Tuple [X "y"; X "x"]), Application, Tuple [I 3; I 4]))
            (ResTuple [ResI 4; ResI 3])

    [<Test>]
    member that.FnParamaterRecord() =
        let pattern = Var( RecordPattern(
            ["a", Var(XPattern "x", None); "b", Var(XPattern "y", None)]), None)
        compareDirect
            (OP (Fn2 (pattern, Tuple [X "y"; X "x"]), 
                Application, 
                Record ["a", I 3; "b", I 4]))
            (ResTuple [ResI 4; ResI 3])

    [<Test>]
    member that.FnParamaterFail() =
        let pattern = Var( TuplePattern(
            [Var(XPattern "x", None); Var(XPattern "y", None)]), None)
        shouldFailDirect
            (OP (Fn2 (pattern, Tuple [X "y"; X "x"]), Application, Tuple [I 3; I 4; I 4]))

    [<Test>]
    member that.FnParamaterListPassingFailingParameter() =
        let pattern = Var( ConsPattern(
            Var(XPattern "x", None), Var(XPattern "y", None)), Some <| List Int)
        compareDirect
            (OP (Fn2 (pattern, Tuple [X "y"; X "x"]), Application, Nil))
            (ResRaise)

    [<Test>]
    member that.RecFnParameter() =
        let pattern = Var( ConsPattern(
            Var(XPattern "x", None), Var(XPattern "y", None)), None)
        compareDirect
            (OP (RecFn2 ("count", None, pattern, 
                Cond(IsEmpty (X "y"), 
                    I 1, 
                    OP(I 1, Add, OP (X "count", Application, X "y")))),
                Application,
                OP (I 3, Cons, OP (I 4, Cons, OP (I 7, Cons, Nil)))))
            (ResI 3)

    [<Test>]
    member that.RecFnParameterFail() =
        let pattern = Var( ConsPattern(
            Var(XPattern "x", None), Var(XPattern "y", None)), None)
        compareDirect
            (OP (RecFn2 ("count", None, pattern, 
                Cond(IsEmpty (X "y"), 
                    I 1, 
                    OP(I 1, Add, OP (X "count", Application, X "y")))),
                Application,
                Nil))
            (ResRaise)