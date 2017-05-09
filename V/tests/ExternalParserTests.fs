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
    (fun () -> parse text |> ignore) |> should throw typeof<ParseException> 

[<TestFixture>]
type TestInfixParsing() =
    
    [<Test>]
    member that.leftAssociationPriority() =
        compare "1 * 2 + 3" <| ResI 5
        
    [<Test>]
    member that.rightAssociationPriority() =
        compare "1 + 2 * 3" <| ResI 7
        
    [<Test>]
    member that.parenthesisPriority() =
        compare "(1 + 2) * 3" <| ResI 9

    [<Test>]
    member that.centerAssociation() =
        compare "(1 + 2) * (3 + 4)" <| ResI 21
        
    [<Test>]
    member that.infixFollowedByPrefix() =
        compare "'a' != head \"hello\"" <| ResB true
        
    [<Test>]
    member that.infixFollowedByInfix() =
        shouldFail "3 != + 3"

    [<Test>]
    member that.rightAssociationCons() =
        compare "3::4::[] = [3,4]" <| ResB true
        
[<TestFixture>]
type TestLetParsing() =
    
    [<Test>]
    member that.simpleLetDeclaration() =
        compare "   let   t   = 4 +3; t" <| ResI 7
        
    [<Test>]
    member that.nestedLetDeclaration() =
        compare "   let   t   = let x = 3;x+4; t" <| ResI 7
        
    [<Test>]
    member that.typedLetDeclaration() =
        compare "   let   t:Int   = let x: Int = 3;x+4; t" <| ResI 7
        
    [<Test>]
    member that.consLetDeclaration() =
        compare "   let  (x :: (y: Int) :: z) : [Int]   = [1,2,3,4]; x + y" <| ResI 3
        
    [<Test>]
    member that.duplicateVars() =
        shouldFail "let (x, x) = (3,4); x + x"
    
    [<Test>]
    member that.listLetDeclaration() =
        compare "   let  [x,y,z]: [Int]   = [1,2,3]; x + y + z" <| ResI 6

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
        compare "   let  rec  t x = x*x ; t 4" <| ResI 16
        
    [<Test>]
    member that.multiParameterLetRec() =
        compare "let rec f (x:Int) (y:Int):Int = x+y; f 3 4" <| ResI 7

    [<Test>]
    member that.nestedLetRec() =
        compare "   let  rec t x = let rec f y = x-y; f x ; t 5" <| ResI 0
        
    [<Test>]
    member that.typedLetRec() =
        compare "   let  rec  t (x: Int): Int = x*x ; t 4" <| ResI 16

    [<Test>]
    member that.simpleLetFunction() =
        compare "   let t x = x*x; t 4" <| ResI 16
        
    [<Test>]
    member that.PatternedLetFunction() =
        shouldFail "   let (t,g) x = x*x; t 4"
        
    [<Test>]
    member that.multiParameterLetFunction() =
        compare "let f (x:Int) (y:Int) (z: Int):Int = x-y-z; f 10 2 4" <| ResI 4

    [<Test>]
    member that.nestedLetFunction() =
        compare "   let  t x = let f y = x-y; f x ; t 5" <| ResI 0
          
    [<Test>]
    member that.sequentialLetFunction() =
        compare "   let  t x = x*2; let f x y = x-y; f 5 (t 2)" <| ResI 1
        
    [<Test>]
    member that.typedLetFunction() =
        compare "   let  t (x: Char): String = 'a'::\"hi\"; t 'a'" <|
            ResCons (ResC 'a', ResCons (ResC 'h', ResCons (ResC 'i', ResNil)))
        
    [<Test>]
    member that.incompleteLetFunction() =
        shouldFail "   let  t x = 3+4;"
        
[<TestFixture>]
type TestFunctionParsing() =

    [<Test>]
    member that.simpleLambda() =
        compare " (\x -> x*x) 4" <| ResI 16
        
    [<Test>]
    member that.multiParameterLambda() =
        compare "(\(x:Int) (y:Int) -> x - y) 3 4" <| ResI -1

    [<Test>]
    member that.nestedLambda() =
        compare "   (\x -> (\y -> x - y))  5 4" <| ResI 1
       
    [<Test>]
    member that.typedLambda() =
        compare "  (\(x:Int) -> x*x) 4" <| ResI 16
        
    [<Test>]
    member that.maltypedLambda() =
        shouldFail "   (\x: -> x) 3"
        

[<TestFixture>]
type TestCond() =

    [<Test>]
    member that.simpleCond() =
        compare " if 0 = 0 then 16 else 0" <| ResI 16
        
    [<Test>]
    member that.nestedCond() =
        compare " if true then if false then 1 else 13 else 4" <| ResI 13

[<TestFixture>]
type TestLists() =

    [<Test>]
    member that.emptyList() =
        compare "[]" <| ResNil

    [<Test>]
    member that.simpleList() =
        compare "['h']" <| ResCons (ResC 'h', ResNil)

    [<Test>]
    member that.longList() =
        compare "[0,3+2,4,(\x -> x+1) 3,4]" <|
            ResCons(ResI 0, ResCons(ResI 5, ResCons(ResI 4, ResCons(ResI 4, ResCons(ResI 4, ResNil)))))

    [<Test>]
    member that.comprehension() =
        compare "[x*2 for x in [1,2,3]]" <| ResCons(ResI 2, ResCons(ResI 4, ResCons(ResI 6, ResNil)))
           
    [<Test>]
    member that.recComprehension() =
        compare "[[x*2 for x in [1,2,3]], [1,2,3], [x for x in [y for y in [1,2,3]]]]" <|
            ResCons( ResCons(ResI 2, ResCons(ResI 4, ResCons(ResI 6, ResNil))),
                ResCons( ResCons(ResI 1, ResCons(ResI 2, ResCons(ResI 3, ResNil))),
                    ResCons( ResCons(ResI 1, ResCons(ResI 2, ResCons(ResI 3, ResNil))),
                        ResNil)))
    
    [<Test>]
    member that.simpleRange() =
        compare "[1..5]" <|
            ResCons(ResI 1, ResCons(ResI 2, ResCons(ResI 3, ResCons(ResI 4, ResCons(ResI 5, ResNil)))))

    [<Test>]
    member that.range() =
        compare "[1,3..10]" <|
            ResCons(ResI 1, ResCons(ResI 3, ResCons(ResI 5, ResCons(ResI 7, ResCons(ResI 9, ResNil)))))

    [<Test>]
    member that.negativeRange() =
        compare "[-30,-20..10]" <|
            ResCons(ResI -30, ResCons(ResI -20, ResCons(ResI -10, ResCons(ResI 0, ResCons(ResI 10, ResNil)))))
        
    [<Test>]
    member that.subtractiveRange() =
        compare "[5,4..1]" <|
            ResCons(ResI 5, ResCons(ResI 4, ResCons(ResI 3, ResCons(ResI 2, ResCons(ResI 1, ResNil)))))

[<TestFixture>]
type TestTupleRecords() =

    [<Test>]
    member that.emptyTuple() =
        shouldFail "(   )"
        
    [<Test>]
    member that.singletonTerm() =
        compare "( 3 + 4  )" <| ResI 7

    [<Test>]
    member that.namedSingletonTerm() =
        compare "{a : 3 + 4  }" <| ResRecord ["a", ResI 7]

    [<Test>]
    member that.twoTuple() =
        compare "( 3 + 4, true  )" <| ResTuple [ResI 7; ResB true]
        
    [<Test>]
    member that.mixedNaming() =
        shouldFail "( a: 3 + 4, true  )"

    [<Test>]
    member that.twoTupleNamed() =
        compare "{ a: 3 + 4, b: true  }" <| 
            ResRecord ["a", ResI 7; "b", ResB true]

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
	                    (x - y)" <| ResI -1

    [<Test>]
    member that.app3() =
        compare    "let app3: (Int -> Int) -> Int = \\(f: Int -> Int) ->
                        f 3
                    ;
                    app3 (\\(x: Int) -> x + 1)" <| ResI 4

    [<Test>]
    member that.factorial() =
        compare    "let rec fat (x: Int): Int =
                        if x = 0 then 1 else x*(fat (x-1))
                    ;
                    fat 5" <| ResI 120

    [<Test>]
    member that.facList() =
        compare    "let rec faclist (x: Int): [Int] =
                        let rec fac (y: Int): Int =
                            if y = 0 then 1 else y*(fac (y-1))
                        ;
                        if x = 0 then
                            nil
                        else
                            (fac x) :: (faclist (x-1))
                    ;
                    reverse $ faclist 5" <| ResCons(ResI 1, ResCons(ResI 2,  
                        ResCons(ResI 6, ResCons(ResI 24, ResCons(ResI 120, ResNil)))))

    [<Test>]
    member that.letRecList() =
        compare    "let rec sum (x: [Int]): Int =
                        if empty? x then 0 else (head x)+(sum(tail x))
                    ;
                    sum(4::3::2::1::nil)" <| ResI 10