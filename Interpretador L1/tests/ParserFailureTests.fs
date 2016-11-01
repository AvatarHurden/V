module ParserFailureTests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation
open Parser

let compare (text, term) =
    let evaluated = evaluate <| parseTerm text (List.empty)
    evaluated |> should equal term

let shouldFail text =
    (fun () -> parseTerm text (List.empty) |> ignore) |> should throw typeof<InvalidEntryText> 

let shouldNotFail text =
    let t = parseTerm text (List.empty)
    true |> should equal true

[<TestFixture>]
type TestStringLiterals() =

    [<Test>]
    member that.nonClosedString() =
        shouldFail "\"My name is"

    [<Test>]
    member that.unclosedParenthesis() =
        compare ("\"((\"", OP(C 'C', Cons, OP(C '(', Cons, Nil)))

    [<Test>]
    member that.closingParamethesisInString() =
        shouldNotFail "(\")\")"

    [<Test>]
    member that.randomSemicolon() =
        compare ("\";Hi;\"", 
            OP(C ';', Cons, OP(C 'H', Cons, OP(C 'i', Cons, OP(C ';', Cons, Nil)))))

    [<Test>]
    member that.emptyString() =
        compare ("\"\"", Nil)

    [<Test>]
    member that.escapedDoubleQuote() =
        compare ("\"\\\"he\\\"\"", 
            OP(C '"', Cons, OP(C 'h', Cons, OP(C 'e', Cons, OP(C '"', Cons, Nil)))))

[<TestFixture>]
type TestCharLiterals() =

    [<Test>]
    member that.nonClosedChar() =
        shouldFail "'"

    [<Test>]
    member that.invalidEscapedChar() =
        shouldFail "'\\d'"

    [<Test>]
    member that.escapedQuote() =
        compare ("'\\''", C '\'')
        
    [<Test>]
    member that.escapedNewLine() =
        compare ("'\\n'", C '\n')

    [<Test>]
    member that.simpleChar() =
        compare ("'a'", C 'a')

[<TestFixture>]
type TestImport() =

    [<Test>]
    member that.simpleImportFail() =
        shouldFail "import a"
          
    [<Test>]
    member that.fullImportFail() =
        shouldFail "import \"math.l4\""

    [<Test>]
    member that.simpleImport() =
        shouldNotFail "import math 3"

    [<Test>]
    member that.fullImport() =
        shouldNotFail "import \"math.l1\" 3"
      
[<TestFixture>]
type TestDelimiters() =

    [<Test>]
    member that.nonClosedParenthesis() =
        shouldFail "(("

    [<Test>]
    member that.nonOpenedParenthesis() =
        shouldFail "((3)))"

    [<Test>]
    member that.closedParenthesis() =
        compare ("(3*(3+3))", I 18)

        
    [<Test>]
    member that.nonClosedLambda() =
        shouldFail "\x 3"

    [<Test>]
    member that.closedLambda() =
        shouldNotFail "\x => x+3"

    [<Test>]
    member that.nestedLambda() =
        compare ("(\x => \y => x-y) 3 4", I -1)

    [<Test>]
    member that.nestedTry() =
        compare ("(\x => \y => x-y) 3 4", I -1)

[<TestFixture>]
type TestIdTypePair() =

    [<Test>]
    member that.normalFunction() =
        shouldNotFail "let x:Int  ->Int->Int  = 3;x"
        compare ("let x:Int  ->Int->Int  = 3;x", I 3)

    [<Test>]
    member that.leftAssociatedFunction() =
        shouldNotFail "let x:(  Int ->  Int)->Int= 3;x"
        compare ("let x:(  Int ->  Int)->Int= 3;x", I 3)
        
    [<Test>]
    member that.randomCharInType() =
        shouldFail "let x:(Int->Int4 )->Int= 3;x"

    [<Test>]
    member that.multipleParameters() =
        shouldNotFail "let x(y:Int, z:Int->Int, g:[[Bool]->[Int]]): Int { 3 };x 1 2 3"
        compare ("let x(y:Int, z:Int->Int, g:[[Bool]->[Int]]): Int { 3 };x 1 2 3", I 3)