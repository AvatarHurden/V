module TypeInferenceTests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation
open Parser
open TypeInference


let compare (text, typ) =
    let evaluated = typeInfer <| parse text
    evaluated |> should equal typ

let compareDirect term typ =
    let evaluated = typeInfer term
    evaluated |> should equal typ

let shouldFailDirect term =
    (fun () -> term |> typeInfer |> ignore) |> should throw typeof<TypeException> 
    
[<TestFixture>]
type TestTypeInfer() =

    [<Test>]
    member that.letAndCond () =
        compare ("let x: Int = 3;
        let y: Int = 4;
        let b: Bool = false;
        if b then
	        (x + y)
        else
	        (x - y)", Int)

    [<Test>]
    member that.IntList() =
         compare ("[(let x = 3; x*2), 8, (\x -> x+1) 4]", List Int)

    [<Test>]
    member that.IntMap() =
        compare ("let rec map (f: Int -> Int) (ls: [Int]): [Int] =
    if empty? ls then
        nil
    else
        (f (head ls))::(map f (tail ls))
;
map (\x -> x + 1) [1,2,3,4]", List Int)

    [<Test>]
    member that.polymorphicIdentity() =
        compare ("let f x = if x = x then x else x;
                if (f true) then
                    f 1
                else
                    f 4", Int)

    [<Test>]
    member that.polymorphicRec() =
        compare ("let rec count ls = if empty? ls then 0 else 1 + count (tail ls);
                count [1,2,3] + count [true,false]", Int)

    [<Test>]
    member that.wrongPolymorphism() =
        (fun () -> compare ("let f x = head x;
                if (f [true]) then
                    f 1
                else
                    f 4", Int) |> ignore) |> should throw typeof<TypeException>

    [<Test>]
    member that.polymorphicHead() =
        compare ("let f x = head x;
                if (f [true]) then
                    f [1]
                else
                    f [4]", Int)

    [<Test>]
    member that.multipleFolds() =
        compare ("if (fold (\\acc x -> if x then acc else false) true [true,true,false]) then
	fold (\\acc x -> acc + x) 0 [1,2,3]
else
	fold (\\acc x -> if x then acc+1 else acc) 0 [true,false,true]", Int)

    [<Test>]
    member that.wrongReduces() =
        (fun () -> 
            compare (
                "if (reduce (\\acc x -> x && acc) [true,true,false]) then
	        reduce (\\acc x -> acc + x) [1,2,3]
        else
	        reduce (\\acc x -> x || acc) [true,false,true]", Int) |> ignore) |> 
        should throw typeof<TypeException>


[<TestFixture>]
type TestMatchInfer() =

    [<Test>]
    member that.simpleUntyped() =
        compareDirect
            (Let (Var(XPattern "x", None), I 3, X "x"))
            Int

    [<Test>]
    member that.simpleTyped() =
        compareDirect
            (Let (Var(XPattern "x", Some Int), I 3, X "x"))
            Int

    [<Test>]
    member that.simpleTypedWrong() =
        shouldFailDirect
            (Let (Var(XPattern "x", Some Char), I 3, X "x"))
            
    [<Test>]
    member that.simpleTuple() =
        let pattern = Var( TuplePattern(
            [Var(XPattern "x", None); Var(XPattern "y", None)]), None)
        compareDirect
            (Let (pattern, Tuple([I 3; I 4]), OP(X "x", Add, X "y")))
            (Int)
           
    [<Test>]
    member that.simpleTupleList() =
        let pattern = Var( TuplePattern(
            [Var(XPattern "x", None); Var(XPattern "y", None)]), None)
        compareDirect
            (Let (pattern, Tuple([Nil; I 4]), X "x"))
            (List (VarType ("X0", [])))
            
    [<Test>]
    member that.simpleTupleInternalType() =
        let pattern = Var( TuplePattern(
            [Var(XPattern "x", Some (List Int)); Var(XPattern "y", None)]), None)
        compareDirect
            (Let (pattern, Tuple([Nil; I 4]), X "x"))
            (List Int)

    [<Test>]
    member that.simpleTupleExternalType() =
        let pattern = Var( TuplePattern(
            [Var(XPattern "x", None); Var(XPattern "y", None)]), Some <| Type.Tuple [Int; Int])
        compareDirect
            (Let (pattern, Tuple([I 3; I 4]), X "x"))
            (Int)
        
    [<Test>]
    member that.duplicateVars() =
        let pattern = Var( TuplePattern(
            [Var(XPattern "x", None); Var(XPattern "x", None)]), None)
        shouldFailDirect
            (Let (pattern, Tuple([I 3; I 4]), OP(X "x", Add, X "y")))

    [<Test>]
    member that.listHead() =
        let pattern = Var( ConsPattern(
            Var(XPattern "x", None), Var(XPattern "y", None)), None)
        compareDirect
            (Let (pattern, OP(I 3, Cons, OP (I 4, Cons, Nil)), X "x"))
            (Int)

    [<Test>]
    member that.lisTail() =
        let pattern = Var( ConsPattern(
            Var(XPattern "x", None), Var(XPattern "y", None)), None)
        compareDirect
            (Let (pattern, OP(I 3, Cons, OP (I 4, Cons, Nil)), X "y"))
            (List Int)

    [<Test>]
    member that.listTyped() =
        let pattern = Var( ConsPattern(
            Var(XPattern "x", Some Int), Var(XPattern "y", Some <| List Int)), None)
        compareDirect
            (Let (pattern, OP(I 3, Cons, OP (I 4, Cons, Nil)), X "y"))
            (List Int)

    [<Test>]
    member that.listTotalTyped() =
        let pattern = Var( ConsPattern(
            Var(XPattern "x", Some Int), Var(XPattern "y", Some <| List Int)), Some <| List Int)
        compareDirect
            (Let (pattern, OP(I 3, Cons, OP (I 4, Cons, Nil)), X "y"))
            (List Int)

    [<Test>]
    member that.FnParamaterTuple() =
        let pattern = Var( TuplePattern(
            [Var(XPattern "x", Some Int); Var(XPattern "y", Some Char)]), None)
        compareDirect
            (Fn (pattern, Tuple [X "y"; X "x"]))
            (Function(Type.Tuple [Int; Char], Type.Tuple [Char;Int]))

    [<Test>]
    member that.FnParamater2Tuple() =
        let pattern = Var( TuplePattern(
            [Var(XPattern "x", Some Int); Var(XPattern "y", Some Char)]), None)
        compareDirect
            (Fn (pattern, X "x"))
            (Function(Type.Tuple [Int; Char], Int))

    [<Test>]
    member that.FnParamaterList() =
        let pattern = Var( ConsPattern(
            Var(XPattern "x", None), Var(XPattern "y", None)), Some <| List Int)
        compareDirect
            (Fn (pattern, Tuple [X "y"; X "x"]))
            (Function(List Int, Type.Tuple [List Int;Int]))

    [<Test>]
    member that.FnParamaterListPassingFailingParameter() =
        let pattern = Var( ConsPattern(
            Var(XPattern "x", None), Var(XPattern "y", None)), Some <| List Int)
        compareDirect
            (OP (Fn (pattern, Tuple [X "y"; X "x"]), Application, Nil))
            (Type.Tuple [List Int;Int])