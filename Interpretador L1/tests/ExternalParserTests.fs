module ExternalParserTests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation
open Parser


let compare text term =
    let evaluated = evaluate <| parse text
    evaluated |> should equal term
    
let shouldFail text =
    (fun () -> parse text |> ignore) |> should throw typeof<InvalidEntryText> 

[<TestFixture>]
type TestInfixParsing() =
    
    [<Test>]
    member that.leftAssociation() =
        compare "1 * 2 + 3" <| I 5
        
    [<Test>]
    member that.rightAssociation() =
        compare "1 + 2 * 3" <| I 7
        
    [<Test>]
    member that.parenthesisPriority() =
        compare "(1 + 2) * 3" <| I 9

    [<Test>]
    member that.centerAssociation() =
        compare "(1 + 2) * (3 + 4)" <| I 21
        
    [<Test>]
    member that.infixFollowedByPrefix() =
        compare "'a' != head \"hello\"" True
        
    [<Test>]
    member that.infixPrecededByPrefix() =
        shouldFail "'a' head !=  \"hello\""

    [<Test>]
    member that.infixFollowedByInfix() =
        shouldFail "3 != + 3"

[<TestFixture>]
type TestLetParsing() =
    
    [<Test>]
    member that.simpleLetDeclaration() =
        compare "   let   t   = 4 +3; t" <| I 7
        
    [<Test>]
    member that.nestedLetDeclaration() =
        compare "   let   t   = let x = 3;x+4; t" <| I 7
        
    [<Test>]
    member that.typedLetDeclaration() =
        compare "   let   t:Int   = let x: Int = 3;x+4; t" <| I 7
        
    [<Test>]
    member that.maltypedLetDeclaration() =
        shouldFail "   let   t: = (let x: Int = 3;x+4); t"
        
    [<Test>]
    member that.incompleteLetDeclaration() =
        shouldFail "   let   t = 5"
        
    [<Test>]
    member that.incompleteLetDeclaration2() =
        shouldFail "   let   t = 5;"


    [<Test>]
    member that.simpleLetRec() =
        compare "   let  rec  t (x) { x*x }; t 4" <| I 16
        
    [<Test>]
    member that.multiParameterLetRec() =
        compare "let rec f(x:Int,y:Int):Int { x+y}; f 3 4" <| I 7

    [<Test>]
    member that.nestedLetRec() =
        compare "   let  rec t (x) { let rec f(y) { x-y }; f x }; t 5" <| I 0
        
    [<Test>]
    member that.typedLetRec() =
        compare "   let  rec  t (x: Int): Int { x*x }; t 4" <| I 16
        
    [<Test>]
    member that.maltypedLetRec() =
        shouldFail "   let  rec t(f): Int = (let x: Int = 3;x+4); t"
        
    [<Test>]
    member that.incompleteLetRec() =
        shouldFail "   let  rec t: Int { 3+4 }; t"


    [<Test>]
    member that.simpleLetFunction() =
        compare "   let t (x) { x*x }; t 4" <| I 16
        
    [<Test>]
    member that.multiParameterLetFunction() =
        compare "let f(x:Int,y:Int, z: Int):Int { x-y-z}; f 10 2 4" <| I 4

    [<Test>]
    member that.nestedLetFunction() =
        compare "   let  t (x) { let f(y) { x-y }; f x }; t 5" <| I 0
          
    [<Test>]
    member that.sequentialLetFunction() =
        compare "   let  t (x) { x*2 }; let f(x, y) { x-y }; f 5 (t 2)" <| I 1
        
    [<Test>]
    member that.typedLetFunction() =
        compare "   let  t (x: Char): String { 'a'::\"hi\" }; t 'a'" <|
            OP (C 'a', Cons, OP (C 'h', Cons, OP (C 'i', Cons, Nil)))
        
    [<Test>]
    member that.maltypedLetFunction() =
        shouldFail "   let t(f: Int) = (let x: Int = 3;x+4); t"
        
    [<Test>]
    member that.incompleteLetFunction() =
        shouldFail "   let  t(x) { 3+4 };"
        
[<TestFixture>]
type TestFunctionParsing() =

    [<Test>]
    member that.simpleFn() =
        compare " fn (x) { x*x } 4" <| I 16
        
    [<Test>]
    member that.multiParameterFn() =
        compare "fn(x:Int,y:Int) { x-y} 3 4" <| I -1

    [<Test>]
    member that.nestedFn() =
        compare "   fn(x) { fn(y) { x-y } }  5 4" <| I 1
       
    [<Test>]
    member that.typedFn() =
        compare "   fn   (x: Int) { x*x } 4" <| I 16
        
    [<Test>]
    member that.maltypedFn() =
        shouldFail "   fn(f): Int { f + 2} 3"
        

    [<Test>]
    member that.simpleLambda() =
        compare " (\x => x*x) 4" <| I 16
        
    [<Test>]
    member that.multiParameterLambda() =
        compare "(\x:Int, y:Int => x - y) 3 4" <| I -1

    [<Test>]
    member that.nestedLambda() =
        compare "   (\x => (\y => x - y))  5 4" <| I 1
       
    [<Test>]
    member that.typedLambda() =
        compare "  (\x:Int => x*x) 4" <| I 16
        
    [<Test>]
    member that.maltypedLambda() =
        shouldFail "   (\x: => x) 3"
        

[<TestFixture>]
type TestCondAndTry() =

    [<Test>]
    member that.simpleCond() =
        compare " if 0 = 0 then 16 else 0" <| I 16
        
    [<Test>]
    member that.nestedCond() =
        compare " if true then if false then 1 else 13 else 4" <| I 13

    [<Test>]
    member that.simpleTry() =
        compare "try if true then raise else 1 except fn(x: Int) { x+3 } 4" <| I 7
       
    [<Test>]
    member that.nestedTry() =
        compare " try try raise except 1 except 2" <| I 1


[<TestFixture>]
type TestLists() =

    [<Test>]
    member that.emptyList() =
        compare "[]" <| Nil

    [<Test>]
    member that.simpleList() =
        compare "['h']" <| OP(C 'h', Cons, Nil)

    [<Test>]
    member that.longList() =
        compare "[0,3+2,4,(\x => x+1) 3,4]" <|
            OP(I 0, Cons, OP(I 5, Cons, OP(I 4, Cons, OP(I 4, Cons, OP(I 4, Cons, Nil)))))

    [<Test>]
    member that.comprehension() =
        compare "[x*2 for x in [1,2,3]]" <| OP(I 2, Cons, OP(I 4, Cons, OP(I 6, Cons, Nil)))
           
    [<Test>]
    member that.recComprehension() =
        compare "[[x*2 for x in [1,2,3]], [1,2,3], [x for x in [y for y in [1,2,3]]]]" <|
            OP( OP(I 2, Cons, OP(I 4, Cons, OP(I 6, Cons, Nil))),
                Cons,
                OP( OP(I 1, Cons, OP(I 2, Cons, OP(I 3, Cons, Nil))),
                    Cons,
                    OP( OP(I 1, Cons, OP(I 2, Cons, OP(I 3, Cons, Nil))),
                        Cons,
                        Nil)))
    
    [<Test>]
    member that.simpleRange() =
        compare "[1..5]" <|
            OP(I 1, Cons, OP(I 2, Cons, OP(I 3, Cons, OP(I 4, Cons, OP(I 5, Cons, Nil)))))

    [<Test>]
    member that.range() =
        compare "[1,3..10]" <|
            OP(I 1, Cons, OP(I 3, Cons, OP(I 5, Cons, OP(I 7, Cons, OP(I 9, Cons, Nil)))))

    [<Test>]
    member that.negativeRange() =
        compare "[-30,-20..10]" <|
            OP(I -30, Cons, OP(I -20, Cons, OP(I -10, Cons, OP(I 0, Cons, OP(I 10, Cons, Nil)))))
        
    [<Test>]
    member that.subtractiveRange() =
        compare "[5,4..1]" <|
            OP(I 5, Cons, OP(I 4, Cons, OP(I 3, Cons, OP(I 2, Cons, OP(I 1, Cons, Nil)))))


[<TestFixture>]
type TestSequence() =

    [<Test>]
    member that.skipOutput() =
        compare    "skip;output \"hi\";3" <| I 3

    [<Test>]
    member that.printConcat() =
        compare    "let f(x, y) {
	                    output (\"the first argument is \"@x);
	                    output (\"the second argument is \"@y);
	                    x @ \" \" @ y
                    };
                    f \"hello\" \"world\"" <| (evaluate <| parse "\"hello world\"")

    [<Test>]
    member that.passUnit() =
        compare    "let f(x: Unit, y: Unit): Unit {
	                    x;y
                    };
                    f (output \"hello\") (output \"world\")" <| Skip

    [<Test>]
    member that.printInLet() =
        compare    "let x: Unit = output \"hi\";
                    x" <| Skip
                    
    [<Test>]
    member that.printInLetEscaped() =
        compare    "let x = ((output \"hi\");3);
                    x" <| I 3

           
[<TestFixture>]
type TestInteractions() =

    [<Test>]
    member that.simpleLetAndCond() =
        compare    "let x: Int = 3;
                    let y: Int = 4;
                    let b: Bool = false;
                    if b then
	                    (x + y)
                    else
	                    (x - y)" <| I -1

    [<Test>]
    member that.app3() =
        compare    "let app3: (Int -> Int) -> Int = fn(f: Int -> Int) {
                        f 3
                    };
                    app3 fn(x: Int) {
                        (x + 1)
                    }" <| I 4

    [<Test>]
    member that.factorial() =
        compare    "let rec fat(x: Int): Int {
                    if x = 0 then 1 else x*(fat (x-1))
                    };
                    fat 5" <| I 120

    [<Test>]
    member that.facList() =
        compare    "let rec faclist(x: Int): [Int] {
                        let rec fac(y: Int): Int {
                            if y = 0 then 1 else y*(fac (y-1))
                        };
                        if x = 0 then
                            nil
                        else
                            (fac x) :: (faclist (x-1))
                    };
                    reverse <| faclist 5" <| OP(I 1, Cons, OP(I 2, Cons, 
                        OP(I 6, Cons, OP(I 24, Cons, OP(I 120, Cons, Nil)))))

    [<Test>]
    member that.letRecList() =
        compare    "let rec sum(x: [Int]): Int {
                        if empty? x then 0 else (head x)+(sum(tail x))
                    };
                    sum(4::3::2::1::nil)" <| I 10