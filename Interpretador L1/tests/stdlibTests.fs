module stdlibTests

open NUnit.Framework
open FsUnit
open Definition
open Evaluation
open TypeInference
open Parser

let compare (text, term) =
    let parsed = parse text
    let typ = typeInfer <| parsed
    let evaluated = evaluate <| parsed
    evaluated |> should equal term

let matchesType text typ =
    let parsed = parsePure text
    let typ' = typeInfer <| parsed
    let freeVars = getFreeVars typ Map.empty
    let freeVars' = getFreeVars typ' Map.empty
    let freePairs = List.zip freeVars freeVars'
    let replaced = List.fold (fun acc (x, x') -> substituteInType (x', VarType x) acc)
                        typ' freePairs
    typ |> should equal replaced

let hasType text typ =
    let parsed = parsePure text
    let typ' = typeInfer <| parsed
    typ |> should equal typ'


let equals text term =
    let parsed = parsePure text
    let typ = typeInfer <| parsed
    let evaluated = evaluate <| parsed
    evaluated |> should equal term

let equalsParsed text text' =
    let parsed = parsePure text
    let parsed' = parsePure text'
    let typ = typeInfer <| parsed
    let typ' = typeInfer <| parsed'
    let evaluated = evaluate <| parsed
    let evaluated' = evaluate <| parsed'
    evaluated |> should equal evaluated'

let throwsWrongType text =
    let parsed = parsePure text
    (fun () -> typeInfer parsed |> ignore) |> should throw typeof<InvalidType>

[<TestFixture>]
type Remainder() =

    static member func = """
let rec remainder(x, y) {
    if y = 0 then  
        raise
    else if x<y then
        x
    else
        remainder (x-y) y
};
"""

    [<Test>]
    member that.testType() =
        hasType (Remainder.func + "remainder") <| Function (Int, Function (Int, Int))
     
    [<Test>]
    member that.testType2() =
        hasType (Remainder.func + "remainder 4") <| Function (Int, Int)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Remainder.func + "remainder 'c' 3")
        throwsWrongType (Remainder.func + "remainder true 2")
        throwsWrongType (Remainder.func + "remainder [1,2] 4")

    [<Test>]
    member that.largerX() =
        equals (Remainder.func + "remainder 10 3") <| ResI 1
        
    [<Test>]
    member that.largerY() =
        equals (Remainder.func + "remainder 3 6") <| ResI 3

    [<Test>]
    member that.Y0() =
        equals (Remainder.func + "remainder 3 0") <| ResRaise


[<TestFixture>]
type Negate() =

    static member func = """
let negate(x) {
	0-x
};
"""

    [<Test>]
    member that.testType() =
        hasType (Negate.func + "negate") <| Function (Int, Int)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Negate.func + "negate true")
        throwsWrongType (Negate.func + "negate \"hj\"")
        throwsWrongType (Negate.func + "negate 'c'")

    [<Test>]
    member that.positive() =
        equals (Negate.func + "negate 5") <| ResI -5
        
    [<Test>]
    member that.negative() =
        equals (Negate.func + "negate (0-5)") <| ResI 5

    [<Test>]
    member that.zero() =
        equals (Negate.func + "negate 0") <| ResI 0
        

[<TestFixture>]
type Abs() =

    static member func = 
        Negate.func + """
let abs(x) {
	if x < 0 then
		negate x
	else
		x
};
"""

    [<Test>]
    member that.testType() =
        hasType (Abs.func + "abs") <| Function (Int, Int)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Abs.func + "abs [1,2]")
        throwsWrongType (Abs.func + "abs true")
        throwsWrongType (Abs.func + "abs 'c'")

    [<Test>]
    member that.positive() =
        equals (Abs.func + "abs 5") <| ResI 5
        
    [<Test>]
    member that.negative() =
        equals (Abs.func + "abs (0-5)") <| ResI 5

    [<Test>]
    member that.zero() =
        equals (Abs.func + "abs 0") <| ResI 0


[<TestFixture>]
type Not() =

    static member func = """
let not(t) {
	if t then
		false
	else
		true
};
"""

    [<Test>]
    member that.testType() =
        hasType (Not.func + "not") <| Function (Bool, Bool)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Not.func + "not 4")
        throwsWrongType (Not.func + "not [true]")

    [<Test>]
    member that.negateTrue() =
        equals (Not.func + "not true") <| ResFalse
        
    [<Test>]
    member that.negateFalse() =
        equals (Not.func + "not false") <| ResTrue


[<TestFixture>]
type Xor() =

    static member func = 
        Not.func + """
let xor(t1, t2) {
	if t1 then
		not t2
	else
		t2
};
"""

    [<Test>]
    member that.testType() =
        hasType (Xor.func + "xor") <| Function (Bool, Function (Bool, Bool))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Xor.func + "xor true 4")
        throwsWrongType (Xor.func + "xor \"string\" true")
        throwsWrongType (Xor.func + "xor false skip")

    [<Test>]
    member that.xorTrueFalse() =
        equals (Xor.func + "xor true false") <| ResTrue
        
    [<Test>]
    member that.xorTrueTrue() =
        equals (Xor.func + "xor true true") <| ResFalse
        
    [<Test>]
    member that.xorFalseFalse() =
        equals (Xor.func + "xor false false") <| ResFalse
        
    [<Test>]
    member that.xorFalseTrue() =
        equals (Xor.func + "xor false true") <| ResTrue


[<TestFixture>]
type Append() =

    static member func = """
let rec append(x, ls) {
	if empty? ls then
		x::ls
	else
		(head ls)::(append x (tail ls))
};
"""

    [<Test>]
    member that.testType() =
        matchesType (Append.func + "append") <| 
            Function (VarType "x", Function (List <| VarType "x", List <| VarType "x"))
     
    [<Test>]
    member that.testType2() =
        matchesType (Append.func + "append 4") <| 
            Function (List Int, List Int)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Append.func + "append 4 [true]")
        throwsWrongType (Append.func + "append \"string\" \"hi\"")
        throwsWrongType (Append.func + "append skip [1,2,3]")

    [<Test>]
    member that.toEmpty() =
        equalsParsed (Append.func + "append true []") "[true]"
        
    [<Test>]
    member that.goesToEnd() =
        equalsParsed (Append.func + "append 'c' \"hi\"") "\"hic\""
        
    [<Test>]
    member that.goesToEnd2() =
        equalsParsed (Append.func + "append 34 [12,3,4,4]") "[12,3,4,4,34]"


[<TestFixture>]
type Concat() =

    static member func = """
let rec concat(ls1, ls2) {
	if empty? ls1 then
		ls2
	else
		(head ls1)::(concat (tail ls1) ls2)
};
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType "x"
        matchesType (Concat.func + "concat") <| 
            Function (List x1, Function (List x1, List x1))
     
    [<Test>]
    member that.testType2() =
        matchesType (Concat.func + "concat [true]") <| 
            Function (List Bool, List Bool)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Concat.func + "concat [4] [true]")
        throwsWrongType (Concat.func + "concat 's' \"hi\"")
        throwsWrongType (Concat.func + "concat [4] [[1,2,3]]")

    [<Test>]
    member that.toEmpty() =
        equalsParsed (Concat.func + "concat [] [true]") "[true]"
        
    [<Test>]
    member that.toEmpty2() =
        equalsParsed (Concat.func + "concat [true] []") "[true]"

    [<Test>]
    member that.goesToEnd() =
        equalsParsed (Concat.func + "concat \"c\" \"hi\"") "\"chi\""
        
    [<Test>]
    member that.goesToEnd2() =
        equalsParsed (Concat.func + "concat [34] [12,3,4,4]") "[34,12,3,4,4]"

[<TestFixture>]
type Teststdlib() =

    [<Test>]
    member that.existsTrue() =
        compare ("exists [5] [[1],[2],[],[5]]", ResTrue)

    [<Test>]
    member that.existsFalse() =
        compare ("exists false [true, true, true]", ResFalse)

    [<Test>]
    member that.existsWrong() =
        (fun () -> compare ("exists (\x => x) []", True) |> ignore)
             |> should throw typeof<InvalidType>

    [<Test>]
    member that.indexOfPositive() =
        compare ("indexOf [5] [[1],[2],[],[5]]", ResI 3)

    [<Test>]
    member that.indexOfNegative() =
        compare ("indexOf false [true, true, true]", ResI -1)

    [<Test>]
    member that.indexOfWrong() =
        (fun () -> compare ("indexOf 4 [true]", Bool) |> ignore)
             |> should throw typeof<InvalidType>
             
    [<Test>]
    member that.maximumAndminimum() =
        compare ("minimum [[1],[2,4],[5]]", OP (I 1, Cons, Nil))
        compare ("maximum []", Raise)
        compare ("minimum [5, -3, 2, -56, 0, 10]", I -56)

    [<Test>]
    member that.sort() =
        compare ("sort [[1],[2,4],[],[5]]", evaluate <| parse "[[], [1], [2,4], [5]]")
        compare ("sort [5, -3, 2, -56, 0, 10]", evaluate <| parse "[-56,-3,0,2,5,10]")