module ExternalParserTests

open NUnit.Framework
open FsUnit
open Definition
open Translation
open Evaluation
open Parser


let compare text term =
    let evaluated = text |> parse |> flip translate stdlib.stdEnv |> evaluate
    evaluated |> should equal term
    
let shouldFail text =
    (fun () -> text |> parse |> flip translate stdlib.stdEnv |> ignore) |> should throw typeof<ParseException> 

[<TestFixture>]
type TestInfixParsing() =
    
    [<Test>]
    member that.leftAssociationPriority() =
        compare "1 * 2 + 3" <| ResConstructor (I 5, [])
        
    [<Test>]
    member that.rightAssociationPriority() =
        compare "1 + 2 * 3" <| ResConstructor (I 7, [])
        
    [<Test>]
    member that.parenthesisPriority() =
        compare "(1 + 2) * 3" <| ResConstructor (I 9, [])

    [<Test>]
    member that.centerAssociation() =
        compare "(1 + 2) * (3 + 4)" <| ResConstructor (I 21, [])
        
    [<Test>]
    member that.infixFollowedByPrefix() =
        compare "'a' != head \"hello\"" <| ResConstructor (B true, [])
        
    [<Test>]
    member that.infixFollowedByInfix() =
        shouldFail "3 != + 3"

    [<Test>]
    member that.rightAssociationCons() =
        compare "3::4::[] = [3,4]" <| ResConstructor (B true, [])
        
[<TestFixture>]
type TestLetParsing() =
    
    [<Test>]
    member that.simpleLetDeclaration() =
        compare "   let   t   = 4 +3; t" <| ResConstructor (I 7, [])
        
    [<Test>]
    member that.nestedLetDeclaration() =
        compare "   let   t   = let x = 3;x+4; t" <| ResConstructor (I 7, [])
        
    [<Test>]
    member that.typedLetDeclaration() =
        compare "   let   t:Int   = let x: Int = 3;x+4; t" <| ResConstructor (I 7, [])
        
    [<Test>]
    member that.consLetDeclaration() =
        compare "   let  (x :: (y: Int) :: z) : [Int]   = [1,2,3,4]; x + y" <| ResConstructor (I 3, [])
        
    [<Test>]
    member that.duplicateVars() =
        shouldFail "let (x, x) = (3,4); x + x"
    
    [<Test>]
    member that.listLetDeclaration() =
        compare "   let  [x,y,z]: [Int]   = [1,2,3]; x + y + z" <| ResConstructor (I 6, [])

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
        compare "   let  rec  t x = x*x ; t 4" <| ResConstructor (I 16, [])
        
    [<Test>]
    member that.multiParameterLetRec() =
        compare "let rec f (x:Int) (y:Int):Int = x+y; f 3 4" <| ResConstructor (I 7, [])

    [<Test>]
    member that.nestedLetRec() =
        compare "   let  rec t x = let rec f y = x-y; f x ; t 5" <| ResConstructor (I 0, [])
        
    [<Test>]
    member that.typedLetRec() =
        compare "   let  rec  t (x: Int): Int = x*x ; t 4" <| ResConstructor (I 16, [])

    [<Test>]
    member that.simpleLetFunction() =
        compare "   let t x = x*x; t 4" <| ResConstructor (I 16, [])
        
    [<Test>]
    member that.PatternedLetFunction() =
        shouldFail "   let (t,g) x = x*x; t 4"
        
    [<Test>]
    member that.multiParameterLetFunction() =
        compare "let f (x:Int) (y:Int) (z: Int):Int = x-y-z; f 10 2 4" <| ResConstructor (I 4, [])

    [<Test>]
    member that.nestedLetFunction() =
        compare "   let  t x = let f y = x-y; f x ; t 5" <| ResConstructor (I 0, [])
          
    [<Test>]
    member that.sequentialLetFunction() =
        compare "   let  t x = x*2; let f x y = x-y; f 5 (t 2)" <| ResConstructor (I 1, [])
        
    //[<Test>]
    //member that.typedLetFunction() =
        //compare "   let  t (x: Char): String = 'a'::\"hi\"; t 'a'" <|
            //ResCons (ResC 'a', ResCons (ResC 'h', ResCons (ResC 'i', ResNil)))
        
    [<Test>]
    member that.incompleteLetFunction() =
        shouldFail "   let  t x = 3+4;"
        
[<TestFixture>]
type TestFunctionParsing() =

    [<Test>]
    member that.simpleLambda() =
        compare " (\x -> x*x) 4" <| ResConstructor (I 16, [])
        
    [<Test>]
    member that.multiParameterLambda() =
        compare "(\(x:Int) (y:Int) -> x - y) 3 4" <| ResConstructor (I -1, [])

    [<Test>]
    member that.nestedLambda() =
        compare "   (\x -> (\y -> x - y))  5 4" <| ResConstructor (I 1, [])
       
    [<Test>]
    member that.typedLambda() =
        compare "  (\(x:Int) -> x*x) 4" <| ResConstructor (I 16, [])
        
    [<Test>]
    member that.maltypedLambda() =
        shouldFail "   (\x: -> x) 3"
        
[<TestFixture>]
type TestDotSyntaxParsing() =
    
    let record = "let x = {a: {b:1,c:'c'},d:True, e:1};"
    
    [<Test>]
    member that.dotOnValue() =
        shouldFail <| "{a:1}.a"

    [<Test>]
    member that.trailingDot() =
        shouldFail <| "x."
        
    [<Test>]
    member that.nonIdentifier() =
        shouldFail (record + "x.2")
        
    [<Test>]
    member that.missingClosingParenthesis() =
        shouldFail (record + "x.(a")
        
    [<Test>]
    member that.emptyParenthesis() =
        shouldFail (record + "x.()")

    [<Test>]
    member that.singleName() =
        compare (record + "x.d") <| ResConstructor (B true, [])
        
    [<Test>]
    member that.compoundName() =
        compare (record + "x.a.b") <| ResConstructor (I 1, [])
        
    [<Test>]
    member that.simpleJoined() =
        compare (record + "x.(e, d)") <| ResConstructor (Tuple 2, [ResConstructor (I 1, []);ResConstructor (B true, [])])
        
    [<Test>]
    member that.simpleIdentifier() =
        compare (record + "let f = #d; x.'f") <| ResConstructor (B true, [])
        
    [<Test>]
    member that.trailingIdentifierMark() =
        shouldFail (record + "x.'")
        

[<TestFixture>]
type TestCond() =

    [<Test>]
    member that.simpleCond() =
        compare " if 0 = 0 then 16 else 0" <| ResConstructor (I 16, [])
        
    [<Test>]
    member that.nestedCond() =
        compare " if True then if False then 1 else 13 else 4" <| ResConstructor (I 13, [])

[<TestFixture>]
type TestLists() =

    [<Test>]
    member that.emptyList() =
        compare "[]" <| ResConstructor (Nil, [])

    [<Test>]
    member that.simpleList() =
        compare "['h']" <| ResConstructor (Cons, [ResConstructor (C 'h', []); ResConstructor (Nil, [])])

    //[<Test>]
    //member that.longList() =
    //    compare "[0,3+2,4,(\x -> x+1) 3,4]" <|
    //        ResCons(ResConstructor (I 0, []), ResCons(ResConstructor (I 5, []), ResCons(ResConstructor (I 4, []), ResCons(ResConstructor (I 4, []), ResCons(ResConstructor (I 4, []), ResNil)))))

    //[<Test>]
    //member that.comprehension() =
    //    compare "[x*2 for x in [1,2,3]]" <| ResCons(ResConstructor (I 2, []), ResCons(ResConstructor (I 4, []), ResCons(ResConstructor (I 6, []), ResNil)))
           
    //[<Test>]
    //member that.recComprehension() =
    //    compare "[[x*2 for x in [1,2,3]], [1,2,3], [x for x in [y for y in [1,2,3]]]]" <|
    //        ResCons( ResCons(ResConstructor (I 2, []), ResCons(ResConstructor (I 4, []), ResCons(ResConstructor (I 6, []), ResNil))),
    //            ResCons( ResCons(ResConstructor (I 1, []), ResCons(ResConstructor (I 2, []), ResCons(ResConstructor (I 3, []), ResNil))),
    //                ResCons( ResCons(ResConstructor (I 1, []), ResCons(ResConstructor (I 2, []), ResCons(ResConstructor (I 3, []), ResNil))),
    //                    ResNil)))
    
    //[<Test>]
    //member that.simpleRange() =
    //    compare "[1..5]" <|
    //        ResCons(ResConstructor (I 1, []), ResCons(ResConstructor (I 2, []), ResCons(ResConstructor (I 3, []), ResCons(ResConstructor (I 4, []), ResCons(ResConstructor (I 5, []), ResNil)))))

    //[<Test>]
    //member that.range() =
    //    compare "[1,3..10]" <|
    //        ResCons(ResConstructor (I 1, []), ResCons(ResConstructor (I 3, []), ResCons(ResConstructor (I 5, []), ResCons(ResConstructor (I 7, []), ResCons(ResConstructor (I 9, []), ResNil)))))

    //[<Test>]
    //member that.negativeRange() =
    //    compare "[-30,-20..10]" <|
    //        ResCons(ResConstructor (I -30, []), ResCons(ResConstructor (I -20, []), ResCons(ResConstructor (I -1, [])0, ResCons(ResConstructor (I 0, []), ResCons(ResConstructor (I 10, []), ResNil)))))
        
    //[<Test>]
    //member that.subtractiveRange() =
        //compare "[5,4..1]" <|
            //ResCons(ResConstructor (I 5, []), ResCons(ResConstructor (I 4, []), ResCons(ResConstructor (I 3, []), ResCons(ResConstructor (I 2, []), ResCons(ResConstructor (I 1, []), ResNil)))))

[<TestFixture>]
type TestTupleRecords() =

    [<Test>]
    member that.emptyTuple() =
        shouldFail "(   )"
        
    [<Test>]
    member that.singletonTerm() =
        compare "( 3 + 4  )" <| ResConstructor (I 7, [])

    [<Test>]
    member that.namedSingletonTerm() =
        compare "{a : 3 + 4  }" <| ResRecord ["a", ResConstructor (I 7, [])]

    [<Test>]
    member that.twoTuple() =
        compare "( 3 + 4, True  )" <| ResConstructor (Tuple 2, [ResConstructor (I 7, []); ResConstructor (B true, [])])
        
    [<Test>]
    member that.mixedNaming() =
        shouldFail "( a: 3 + 4, True  )"

    [<Test>]
    member that.twoTupleNamed() =
        compare "{ a: 3 + 4, b: True  }" <| 
            ResRecord ["a", ResConstructor (I 7, []); "b", ResConstructor (B true, [])]

[<TestFixture>]
type TestInteractions() =

    [<Test>]
    member that.simpleLetAndCond() =
        compare    "let x: Int = 3;
                    let y: Int = 4;
                    let b: Bool = False;
                    if b then
	                    (x + y)
                    else
	                    (x - y)" <| ResConstructor (I -1, [])

    [<Test>]
    member that.app3() =
        compare    "let app3: (Int -> Int) -> Int = \\(f: Int -> Int) ->
                        f 3
                    ;
                    app3 (\\(x: Int) -> x + 1)" <| ResConstructor (I 4, [])

    [<Test>]
    member that.factorial() =
        compare    "let rec fat (x: Int): Int =
                        if x = 0 then 1 else x*(fat (x-1))
                    ;
                    fat 5" <| ResConstructor (I 120, [])

    //[<Test>]
    //member that.facList() =
        //compare    "let rec faclist (x: Int): [Int] =
                    //    let rec fac (y: Int): Int =
                    //        if y = 0 then 1 else y*(fac (y-1))
                    //    ;
                    //    if x = 0 then
                    //        nil
                    //    else
                    //        (fac x) :: (faclist (x-1))
                    //;
                    //reverse $ faclist 5" <| ResCons(ResConstructor (I 1, []), ResCons(ResConstructor (I 2, []),  
                        //ResCons(ResConstructor (I 6, []), ResCons(ResConstructor (I 24, []), ResCons(ResConstructor (I 120, []), ResNil)))))

    [<Test>]
    member that.letRecList() =
        compare    "let rec sum (x: [Int]): Int =
                        if empty? x then 0 else (head x)+(sum(tail x))
                    ;
                    sum(4::3::2::1::Nil)" <| ResConstructor (I 10, [])

