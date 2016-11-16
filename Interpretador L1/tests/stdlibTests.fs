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
    let replaced = List.fold (fun acc ((x, traits), (x', traits')) -> substituteInType (x', VarType (x, traits')) acc)
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
        let x1 = VarType ("x", [])
        matchesType (Append.func + "append") <| 
            Function (x1, Function (List x1, List x1))
     
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
        let x1 = VarType ("x", [])
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
type Last() =

    static member func = """
let rec last(ls) {
	if empty? ls then
		raise
	else if empty? (tail ls) then
		head ls
	else
		last (tail ls)
};
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Last.func + "last") <| Function (List x1, x1)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Last.func + "last 4")
        throwsWrongType (Last.func + "last skip")

    [<Test>]
    member that.empty() =
        equalsParsed (Last.func + "last []") "raise"
        
    [<Test>]
    member that.oneItem() =
        equalsParsed (Last.func + "last [true]") "true"

    [<Test>]
    member that.multipleItems() =
        equalsParsed (Last.func + "last \"hfei\"") "'i'"
        

[<TestFixture>]
type Init() =

    static member func = """
let rec init(ls){
	if empty? ls then
		raise
	else if empty? (tail ls) then
		nil
	else
		(head ls)::(init (tail ls))
};
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Init.func + "init") <| Function (List x1, List x1)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Init.func + "init 4")

    [<Test>]
    member that.empty() =
        equalsParsed (Init.func + "init []") "raise"
        
    [<Test>]
    member that.oneItem() =
        equalsParsed (Init.func + "init [true]") "[]"

    [<Test>]
    member that.multipleItems() =
        equalsParsed (Init.func + "init \"hfei\"") "\"hfe\""
        

[<TestFixture>]
type Length() =

    static member func = """
let rec length(ls) {
	if empty? ls then
		0
	else
		1 + length (tail ls)
};
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Length.func + "length") <| Function (List x1, Int)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Length.func + "length 4")

    [<Test>]
    member that.empty() =
        equalsParsed (Length.func + "length []") "0"
        
    [<Test>]
    member that.oneItem() =
        equalsParsed (Length.func + "length [true]") "1"

    [<Test>]
    member that.multipleItems() =
        equalsParsed (Length.func + "length \"hfei\"") "4"
       

[<TestFixture>]
type Range() =

    static member func = """
let rec range(start, finish, inc) {
    if (inc > 0 && start <= finish) || (inc < 0 && start >= finish) then
		start::(range (start+inc) finish inc)
    else
        nil
};
"""

    [<Test>]
    member that.testType() =
        hasType (Range.func + "range") <| 
            Function (Int, Function (Int, Function (Int, List Int)))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Range.func + "range 'c'")
        throwsWrongType (Range.func + "range 4 true")
        throwsWrongType (Range.func + "range 4 3 []")
        throwsWrongType (Range.func + "range [4] 3 []")

    [<Test>]
    member that.emptyGenerator() =
        equalsParsed (Range.func + "range 0 1 (0-1)") "[]"
        
    [<Test>]
    member that.sameStartAndEnd() =
        equalsParsed (Range.func + "range 1 1 1") "[1]"

    [<Test>]
    member that.postiveInc() =
        equalsParsed (Range.func + "range 0 5 2") "[0, 2, 4]"
       
    [<Test>]
    member that.negativeInc() =
        equalsParsed (Range.func + "range 5 0 (0-2)") "[5, 3, 1]"
        
    [<Test>]
    member that.negativeEnd() =
        equalsParsed (Range.func + "range 0 (0-5) (0-2)") "[0, (0-2), (0-4)]"
       

[<TestFixture>]
type Reverse() =

    static member func = """
let reverse(ls) {
    let rec f(lsOld, lsNew) {
        if empty? lsOld then
            lsNew
        else
            f (tail lsOld) ((head lsOld)::lsNew)
	};
    f ls []
};
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Reverse.func + "reverse") <| 
            Function (List x1, List x1)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Reverse.func + "reverse 'c'")
        throwsWrongType (Reverse.func + "reverse 4")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Reverse.func + "reverse []") "[]"
        
    [<Test>]
    member that.oneItem() =
        equalsParsed (Reverse.func + "reverse [1]") "[1]"

    [<Test>]
    member that.multipleItems() =
        equalsParsed (Reverse.func + "reverse [1,2,3]") "[3,2,1]"
       
    [<Test>]
    member that.reverseString() =
        equalsParsed (Reverse.func + "reverse \"hello\"") "\"olleh\""
        

[<TestFixture>]
type Map() =

    static member func = """
let rec map(f, ls) {
    if empty? ls then
        nil
    else
        (f (head ls))::(map f (tail ls))
};
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        let x2 = VarType ("y", [])
        matchesType (Map.func + "map") <| 
            Function (Function (x2, x1), Function (List x2, List x1))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Map.func + "map [1,2,3]")
        throwsWrongType (Map.func + "map (\\x => x = true) [1,2,3]")
        throwsWrongType (Map.func + "map (\\x => x = true) true")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Map.func + "map (\\x => x) []") "[]"
        
    [<Test>]
    member that.mapIdentity() =
        equalsParsed (Map.func + "map (\\x => x) [1,2]") "[1,2]"

    [<Test>]
    member that.mapReverse() =
        equalsParsed (Map.func + Reverse.func + 
            "map reverse [[1,2],[3,4]]") "[[2,1],[4,3]]"
       
    [<Test>]
    member that.mapOtherType() =
        equalsParsed (Map.func + "map (\\x => x > 3) [2,5,3,6]") 
            "[false, true, false, true]"
        

[<TestFixture>]
type Fold() =

    static member func = """
let rec fold(f, acc, ls) {
    if empty? ls then
        acc
    else
        fold f (f acc (head ls)) (tail ls)
};
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        let x2 = VarType ("y", [])
        matchesType (Fold.func + "fold") <| 
            Function (Function (x2, Function (x1, x2)), Function (x2, Function (List x1, x2)))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Fold.func + "fold [1,2,3]")
        throwsWrongType (Fold.func + "fold (\\x => x = true) true [1,2,3]")
        throwsWrongType (Fold.func + "fold (\\acc, x => acc && x % 4 = 0) true \"hi\"")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Fold.func + "fold (\\acc, x => acc + x) 0 []") "0"
        
    [<Test>]
    member that.foldSum() =
        equalsParsed (Fold.func + "fold (\\acc, x => acc + x) 0 [1,2,3]") "6"

    [<Test>]
    member that.foldXor() =
        equalsParsed (Fold.func + Xor.func + 
            "fold xor true [true,false,true]") "true"
       
    [<Test>]
    member that.foldChangeType() =
        equalsParsed (Fold.func + 
            "fold (\\acc, x => if x then acc+1 else acc) 0 [true,false,true]") 
            "2"
   

[<TestFixture>]
type Reduce() =

    static member func = 
        Fold.func + """
let reduce(f, ls) {
    if empty? ls then
        raise
    else
        fold f (head ls) (tail ls)
};
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Reduce.func + "reduce") <| 
            Function (Function (x1, Function (x1, x1)), Function (List x1, x1))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Reduce.func + "reduce [1,2,3]")
        throwsWrongType (Reduce.func + "reduce (\\x => x = true) [1,2,3]")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Reduce.func + "reduce (\\acc, x => acc + x) []") "raise"
        
    [<Test>]
    member that.reduceSum() =
        equalsParsed (Reduce.func + "reduce (\\acc, x => acc + x) [1,2,3]") "6"

    [<Test>]
    member that.reduceXor() =
        equalsParsed (Reduce.func + Xor.func + 
            "reduce xor [true,false,true]") "false"
       

[<TestFixture>]
type All() =

    static member func = 
        Not.func + """
let rec all(pred, ls) {
	if empty? ls then
		true
	else if (head ls) |> pred |> not then
        false
	else
		(tail ls) |> all pred
};
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (All.func + "all") <| 
            Function (Function (x1, Bool), Function (List x1, Bool))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (All.func + "all [1,2,3]")
        throwsWrongType (All.func + "all (\\x => x = true) [1,2,3]")

    [<Test>]
    member that.emptyList() =
        equalsParsed (All.func + "all (\\x => x > 2) []") "true"
        
    [<Test>]
    member that.allMatch() =
        equalsParsed (All.func + "all (\\x => x > 3) [4,5,6]") "true"
        
    [<Test>]
    member that.oneFails() =
        equalsParsed (All.func + "all (\\x => x > 3) [3,5,6]") "false"


[<TestFixture>]
type Any() =

    static member func = """
let rec any(pred, ls) {
	if empty? ls then
		false
	else if (head ls) |> pred then
		true
	else
		(tail ls) |> any pred
};
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Any.func + "any") <| 
            Function (Function (x1, Bool), Function (List x1, Bool))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Any.func + "any [1,2,3]")
        throwsWrongType (Any.func + "any (\\x => x = true) [1,2,3]")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Any.func + "any (\\x => x > 2) []") "false"
        
    [<Test>]
    member that.allFail() =
        equalsParsed (Any.func + "any (\\x => x < 3) [4,5,6]") "false"
        
    [<Test>]
    member that.oneMatches() =
        equalsParsed (Any.func + "any (\\x => x > 3) [3,5,2]") "true"

[<TestFixture>]
type Maximum() =

    static member func = 
        Reduce.func + """
let maximum(ls) {
    reduce (\acc, x => if acc < x then x else acc) ls
};
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [Orderable])
        matchesType (Maximum.func + "maximum") <| 
            Function (List x1, x1)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Maximum.func + "maximum [true,false,true]")
        throwsWrongType (Maximum.func + "maximum [skip]")
        throwsWrongType (Maximum.func + "maximum 3")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Maximum.func + "maximum []") "raise"
        
    [<Test>]
    member that.maxNumber() =
        equalsParsed (Maximum.func + "maximum [1,5,3]") "5"

    [<Test>]
    member that.maxChar() =
        equalsParsed (Maximum.func + "maximum \"hello\"") "'o'"
      
    
[<TestFixture>]
type Minimum() =

    static member func = 
        Reduce.func + """
let minimum(ls) {
    reduce (\acc, x => if acc > x then x else acc) ls
};
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [Orderable])
        matchesType (Minimum.func + "minimum") <| 
            Function (List x1, x1)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Minimum.func + "minimum [true,false,true]")
        throwsWrongType (Minimum.func + "minimum [skip]")
        throwsWrongType (Minimum.func + "minimum 3")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Minimum.func + "minimum []") "raise"
        
    [<Test>]
    member that.minNumber() =
        equalsParsed (Minimum.func + "minimum [1,5,3]") "1"

    [<Test>]
    member that.minChar() =
        equalsParsed (Minimum.func + "minimum \"hello\"") "'e'"    
        
             
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
        (fun () -> compare ("exists (\\x => x) []", True) |> ignore)
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