module stdlibTests

open NUnit.Framework
open FsUnit
open Definition
open Translation
open Evaluation
open TypeInference
open Parser

let compare (text, term) =
    let parsed = text |> parsePure |> flip translate stdlib.stdEnv
    let typ = typeInfer <| parsed
    let evaluated = evaluate <| parsed
    evaluated |> should equal term

let matchesType text typ =
    let parsed = text |> parsePure |> flip translate stdlib.stdEnv
    let typ' = typeInfer <| parsed
    let freeVars = List.sort <| getFreeVars typ defaultEnv |> List.unzip |> fst
    let freeVars' = List.sort <| getFreeVars typ' defaultEnv  |> List.unzip |> fst
    let freePairs = List.zip freeVars freeVars'
    let replaced = List.fold (fun acc (x, x') -> substituteInType (NameSub (x', x)) acc)
                        typ' freePairs
    typ |> should equal replaced

let hasType text typ =
    let parsed = text |> parsePure |> flip translate stdlib.stdEnv
    let typ' = typeInfer <| parsed
    typ |> should equal typ'


let equals text term =
    let parsed = text |> parsePure |> flip translate stdlib.stdEnv
    let typ = typeInfer <| parsed
    let evaluated = evaluate <| parsed
    evaluated |> should equal term

let equalsParsed text text' =
    let parsed = text |> parsePure |> flip translate stdlib.stdEnv
    let parsed' = text' |> parsePure |> flip translate stdlib.stdEnv
    let typ = typeInfer <| parsed
    let typ' = typeInfer <| parsed'
    let evaluated = evaluate <| parsed
    let evaluated' = evaluate <| parsed'
    evaluated |> should equal evaluated'

let throwsWrongType text =
    let parsed = text |> parsePure |> flip translate stdlib.stdEnv
    (fun () -> typeInfer parsed |> ignore) |> should throw typeof<TypeException>

[<TestFixture>]
type Id() =

    static member func = """
let id x = x;
"""

    [<Test>]
    member that.testType() =
        let x = VarType ("x", [])
        matchesType (Id.func + "id") <| 
            Function (x, x)

[<TestFixture>]
type Const() =

    static member func = """
let const x _ = x;
"""

    [<Test>]
    member that.testType() =
        let x = VarType ("x", [])
        let y = VarType ("y", [])
        matchesType (Const.func + "const") <| 
            Function (x, Function(y, x))

    [<Test>]
    member that.raise() =
        equals (Const.func + "const 3 raise") <| ResRaise
        
[<TestFixture>]
type Flip() =

    static member func = """
let flip f x y = f y x;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("y", [])
        let x2 = VarType ("x", [])
        let x3 = VarType ("z", [])
        matchesType (Flip.func + "flip") <| 
            Function (Function (x1, Function(x2, x3)), 
                Function(x2, Function(x1, x3)))

[<TestFixture>]
type Apply() =

    static member func = """
let apply f x = f x;
let infixr 1 ($) = apply;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        let x2 = VarType ("y", [])
        matchesType (Apply.func + "apply") <| 
            Function (Function (x1, x2), 
                Function(x1, x2))

[<TestFixture>]
type Compose() =

    static member func = """
let compose f g x = f (g x);
let infixr 9 (.) = compose;
"""

    [<Test>]
    member that.testType() =
        let x = VarType ("x", [])
        let z = VarType ("y", [])
        let y = VarType ("z", [])     
        matchesType (Compose.func + "compose") <| 
            Function (Function (y, x), 
                Function (Function(z, y), Function (z, x)))

[<TestFixture>]
type Remainder() =

    static member func = """
let rec remainder x y = x - (x/y)*y;
let infixl 8 (%) = remainder;
"""

    [<Test>]
    member that.testType() =
        hasType (Remainder.func + "remainder") <| Function ((ConstType (Int, [])), Function ((ConstType (Int, [])), (ConstType (Int, []))))
     
    [<Test>]
    member that.testType2() =
        hasType (Remainder.func + "remainder 4") <| Function ((ConstType (Int, [])), (ConstType (Int, [])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Remainder.func + "remainder 'c' 3")
        throwsWrongType (Remainder.func + "remainder true 2")
        throwsWrongType (Remainder.func + "remainder [1,2] 4")

    [<Test>]
    member that.largerX() =
        equals (Remainder.func + "remainder 10 3") <| ResConstructor (I 1, [])
        
    [<Test>]
    member that.largerY() =
        equals (Remainder.func + "remainder 3 6") <| ResConstructor (I 3, [])

    [<Test>]
    member that.Y0() =
        equals (Remainder.func + "remainder 3 0") <| ResRaise


[<TestFixture>]
type Negate() =

    static member func = """
let negate x =
	0-x
;
"""

    [<Test>]
    member that.testType() =
        hasType (Negate.func + "negate") <| Function ((ConstType (Int, [])), (ConstType (Int, [])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Negate.func + "negate true")
        throwsWrongType (Negate.func + "negate \"hj\"")
        throwsWrongType (Negate.func + "negate 'c'")

    [<Test>]
    member that.positive() =
        equals (Negate.func + "negate 5") <| ResConstructor (I -5, [])
        
    [<Test>]
    member that.negative() =
        equals (Negate.func + "negate (0-5)") <| ResConstructor (I 5, [])

    [<Test>]
    member that.zero() =
        equals (Negate.func + "negate 0") <| ResConstructor (I 0, [])
        

[<TestFixture>]
type Abs() =

    static member func = 
        Negate.func + """
let abs x =
	if x < 0 then
		negate x
	else
		x
;
"""

    [<Test>]
    member that.testType() =
        hasType (Abs.func + "abs") <| Function ((ConstType (Int, [])), (ConstType (Int, [])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Abs.func + "abs [1,2]")
        throwsWrongType (Abs.func + "abs true")
        throwsWrongType (Abs.func + "abs 'c'")

    [<Test>]
    member that.positive() =
        equals (Abs.func + "abs 5") <| ResConstructor (I 5, [])
        
    [<Test>]
    member that.negative() =
        equals (Abs.func + "abs (0-5)") <| ResConstructor (I 5, [])

    [<Test>]
    member that.zero() =
        equals (Abs.func + "abs 0") <| ResConstructor (I 0, [])

[<TestFixture>]
type Not() =

    static member func = """
let not t =
	if t then
		false
	else
		true
;
"""

    [<Test>]
    member that.testType() =
        hasType (Not.func + "not") <| Function ((ConstType (Bool, [])), (ConstType (Bool, [])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Not.func + "not 4")
        throwsWrongType (Not.func + "not [true]")

    [<Test>]
    member that.negateTrue() =
        equals (Not.func + "not true") <| ResConstructor (B false, [])
        
    [<Test>]
    member that.negateFalse() =
        equals (Not.func + "not false") <| ResConstructor (B true, [])


[<TestFixture>]
type Xor() =

    static member func = 
        Not.func + """
let xor t1 t2 =
	if t1 then
		not t2
	else
		t2
;
"""

    [<Test>]
    member that.testType() =
        hasType (Xor.func + "xor") <| Function ((ConstType (Bool, [])), Function ((ConstType (Bool, [])), (ConstType (Bool, []))))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Xor.func + "xor true 4")
        throwsWrongType (Xor.func + "xor \"string\" true")

    [<Test>]
    member that.xorTrueFalse() =
        equals (Xor.func + "xor true false") <| ResConstructor (B true, [])
        
    [<Test>]
    member that.xorTrueTrue() =
        equals (Xor.func + "xor true true") <| ResConstructor (B false, [])
        
    [<Test>]
    member that.xorFalseFalse() =
        equals (Xor.func + "xor false false") <| ResConstructor (B false, [])
        
    [<Test>]
    member that.xorFalseTrue() =
        equals (Xor.func + "xor false true") <| ResConstructor (B true, [])

[<TestFixture>]
type Fst() =

    static member func = """
let fst (x, _) = x;
"""

    [<Test>]
    member that.testType() =
        let x = VarType("x", [])
        let y = VarType("y", [])
        matchesType (Fst.func + "fst") <| 
            Function (Type.Tuple [x; y], x)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Fst.func + "fst (true, 4, 4)")
        throwsWrongType (Fst.func + "fst 3")

    [<Test>]
    member that.raiseFirst() =
        equals (Fst.func + "fst (raise, 3)") <| ResRaise
        
    [<Test>]
    member that.raiseSecond() =
        equals (Fst.func + "fst (3, raise)") <| ResRaise


[<TestFixture>]
type Snd() =

    static member func = """
let snd (_, y) = y;
"""

    [<Test>]
    member that.testType() =
        let x = VarType("x", [])
        let y = VarType("y", [])
        matchesType (Snd.func + "snd") <| 
            Function (Type.Tuple [x; y], y)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Snd.func + "snd (true, 4, 4)")
        throwsWrongType (Snd.func + "snd 3")

    [<Test>]
    member that.raiseFirst() =
        equals (Snd.func + "snd (raise, 3)") <| ResRaise
        
    [<Test>]
    member that.raiseSecond() =
        equals (Snd.func + "snd (3, raise)") <| ResRaise

[<TestFixture>]
type Swap() =

    static member func = """
let swap (x, y) = (y, x);
"""

    [<Test>]
    member that.testType() =
        let x = VarType("x", [])
        let y = VarType("y", [])
        matchesType (Swap.func + "swap") <| 
            Function (Type.Tuple [x; y], Type.Tuple [y; x])
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Swap.func + "swap (true, 4, 4)")
        throwsWrongType (Swap.func + "swap 3")

    [<Test>]
    member that.raiseFirst() =
        equals (Swap.func + "swap (raise, 3)") <| ResRaise
        
    [<Test>]
    member that.raiseSecond() =
        equals (Swap.func + "swap (3, 'a')") <| ResTuple [ResConstructor (C 'a', []); ResConstructor (I 3, [])]


[<TestFixture>]
type Set() =

    static member func = Apply.func + Snd.func + """
let set acc v r = snd $ acc v r;
"""

    [<Test>]
    member that.testType() =
        let w = VarType("w", [])
        let x = VarType("x", [])
        let y = VarType("y", [])
        let z = VarType("z", [])
        let accTyp = Function (z, Function (w, Type.Tuple [x; y]))
        matchesType (Set.func + "set") <| 
            Function (accTyp, Function (z, Function (w, y)))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Set.func + "set (true, 4, 4)")
        throwsWrongType (Set.func + "set #name 4 {names:3}")
        throwsWrongType (Set.func + "set #name 4 {name:'a'}")

    [<Test>]
    member that.simple() =
        equals (Set.func + "set #a 5 {a:4, b:3}") <| ResRecord ["a", ResConstructor (I 5, []); "b", ResConstructor (I 3, [])]
    
    [<Test>]
    member that.raiseField() =
        equals (Set.func + "set #a 5 {a:raise, b:3}") <| ResRaise
    
    [<Test>]
    member that.nonRaiseField() =
        equals (Set.func + "set #a 5 {a:4, b:raise}") <| ResRaise

    [<Test>]
    member that.raiseRecord() =
        equals (Set.func + "set #a 4 raise") <| ResRaise
    

[<TestFixture>]
type Modify() =

    static member func = Set.func + """
let modify acc f r =
    let oldV = get acc r;
    set acc (f oldV) r
;
"""

    [<Test>]
    member that.testType() =
        let w = VarType("w", [])
        let x = VarType("x", [])
        let y = VarType("y", [])
        let z = VarType("z", [])
        let accTyp = Function (z, Function (w, Type.Tuple [y; x]))
        matchesType (Modify.func + "modify") <| 
            Function (accTyp, Function (Function (y, z), Function (w, x)))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Modify.func + "modify (true, 4, 4)")
        throwsWrongType (Modify.func + "modify #name (\x -> x + 1) {names:3}")
        throwsWrongType (Modify.func + "modify #name (\x -> x + 1) {name:'a'}")

    [<Test>]
    member that.simple() =
        equals (Modify.func + "modify #a (\x -> x) {a:4, b:3}") <| ResRecord ["a", ResConstructor (I 4, []); "b", ResConstructor (I 3, [])]
    
    [<Test>]
    member that.simpleMod() =
        equals (Modify.func + "modify #a ((+) 1) {a:2, b:3}") <| ResRecord ["a", ResConstructor (I 3, []); "b", ResConstructor (I 3, [])]
    
    [<Test>]
    member that.raiseField() =
        equals (Modify.func + "modify #a (\x -> 1) {a:raise, b:3}") <| ResRaise

    [<Test>]
    member that.nonRaiseField() =
        equals (Modify.func + "modify #a (\x -> x * 2) {a:4, b:raise}") <| ResRaise

    [<Test>]
    member that.raiseRecord() =
        equals (Modify.func + "modify #a (\x -> 1) raise") <| ResRaise
    

[<TestFixture>]
type Head() =

    static member func = """
let head (x :: xs) = x;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Head.func + "head") <| 
            Function (ConstType (List, [x1]), x1)

    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Head.func + "head 4 [true]")

    [<Test>]
    member that.empty() =
        equalsParsed (Head.func + "head []") "raise"
        
    [<Test>]
    member that.firstString() =
        equalsParsed (Head.func + "head \"hi\"") "'h'"
        

[<TestFixture>]
type Tail() =

    static member func = """
let tail (x :: xs) = xs;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Tail.func + "tail") <| 
            Function (ConstType (List, [x1]), ConstType (List, [x1]))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Tail.func + "tail 4")

    [<Test>]
    member that.empty() =
        equalsParsed (Tail.func + "tail []") "raise"
        
    [<Test>]
    member that.firstString() =
        equalsParsed (Tail.func + "tail \"hi\"") "\"i\""
     
      
[<TestFixture>]
type Empty() =

    static member func = """
let empty? x =
    match x with
    | [] -> true
    | _ -> false
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Empty.func + "empty?") <| 
            Function (ConstType (List, [x1]), (ConstType (Bool, [])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Empty.func + "empty? 4")

    [<Test>]
    member that.empty() =
        equalsParsed (Empty.func + "empty? []") "true"
        
    [<Test>]
    member that.firstString() =
        equalsParsed (Empty.func + "empty? \"hi\"") "false"
        
        
[<TestFixture>]
type Append() =

    static member func = """
let rec append x ls =
    match ls with
    | [] -> [x]
    | l :: ls -> l :: append x ls 
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Append.func + "append") <| 
            Function (x1, Function (ConstType (List, [x1]), ConstType (List, [x1])))
     
    [<Test>]
    member that.testType2() =
        matchesType (Append.func + "append 4") <| 
            Function (ConstType (List, [ConstType (Int, [])]), ConstType (List, [ConstType (Int, [])]))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Append.func + "append 4 [true]")
        throwsWrongType (Append.func + "append \"string\" \"hi\"")
        throwsWrongType (Append.func + "append true [1,2,3]")

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
let rec concat ls1 ls2 =
    match ls1 with
    | [] -> ls2
    | x :: xs -> x :: concat xs ls2
;
let (@) = concat;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Concat.func + "concat") <| 
            Function (ConstType (List, [x1]), Function (ConstType (List, [x1]), ConstType (List, [x1])))
     
    [<Test>]
    member that.testType2() =
        matchesType (Concat.func + "concat [true]") <| 
            Function (ConstType (List, [ConstType (Bool, [])]), ConstType (List, [ConstType (Bool, [])]))
     
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
let rec last ls =
    match ls with
    | [x] -> x
    | _ :: xs -> last xs
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Last.func + "last") <| Function (ConstType (List, [x1]), x1)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Last.func + "last 4")
        throwsWrongType (Last.func + "last true")

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
let rec init ls =
    match ls with
    | [x] -> []
    | x :: xs -> x :: init xs
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Init.func + "init") <| Function (ConstType (List, [x1]), ConstType (List, [x1]))
     
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
let rec length ls =
    match ls with
    | [] -> 0
    | _ :: xs -> 1 + length xs
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Length.func + "length") <| Function (ConstType (List, [x1]), (ConstType (Int, [])))
     
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
let rec range start finish inc =
    if (inc > 0 && start <= finish) || (inc < 0 && start >= finish) then
        start::(range (start+inc) finish inc)
    else
        []
;
"""

    [<Test>]
    member that.testType() =
        let i = ConstType (Int, [])
        hasType (Range.func + "range") <| 
            Function (i, Function (i, Function (i, ConstType (List, [i]))))
     
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

    static member func = 
        Apply.func + """
let reverse ls =
    let rec f lsOld lsNew =
        match lsOld with
        | [] -> lsNew
        | x :: xs -> f xs $ x :: lsNew
    ;
    f ls []
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Reverse.func + "reverse") <| 
            Function (ConstType (List, [x1]), ConstType (List, [x1]))
     
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
let rec map f ls =
    match ls with
    | [] -> []
    | x :: xs -> f x :: map f xs
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("y", [])
        let x2 = VarType ("x", [])
        matchesType (Map.func + "map") <| 
            Function (Function (x2, x1), Function (ConstType (List, [x2]), ConstType (List, [x1])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Map.func + "map [1,2,3]")
        throwsWrongType (Map.func + "map (\\x -> x = true) [1,2,3]")
        throwsWrongType (Map.func + "map (\\x -> x = true) true")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Map.func + "map (\\x -> x) []") "[]"
        
    [<Test>]
    member that.mapIdentity() =
        equalsParsed (Map.func + "map (\\x -> x) [1,2]") "[1,2]"

    [<Test>]
    member that.mapReverse() =
        equalsParsed (Map.func + Reverse.func + 
            "map reverse [[1,2],[3,4]]") "[[2,1],[4,3]]"
       
    [<Test>]
    member that.mapOtherType() =
        equalsParsed (Map.func + "map (\\x -> x > 3) [2,5,3,6]") 
            "[false, true, false, true]"
        

[<TestFixture>]
type Fold() =

    static member func = """
let rec fold f acc ls =
    match ls with
    | [] -> acc
    | x :: xs -> fold f (f acc x) xs
;
"""

    [<Test>]
    member that.testType() =
        let x2 = VarType ("x", [])
        let x1 = VarType ("y", [])
        matchesType (Fold.func + "fold") <| 
            Function (Function (x2, Function (x1, x2)), Function (x2, Function (ConstType (List, [x1]), x2)))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Fold.func + "fold [1,2,3]")
        throwsWrongType (Fold.func + "fold (\\x -> x = true) true [1,2,3]")
        throwsWrongType (Fold.func + Remainder.func + "fold (\\acc x -> acc && x % 4 = 0) true \"hi\"")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Fold.func + "fold (\\acc x -> acc + x) 0 []") "0"
        
    [<Test>]
    member that.foldSum() =
        equalsParsed (Fold.func + "fold (\\acc x -> acc + x) 0 [1,2,3]") "6"

    [<Test>]
    member that.foldXor() =
        equalsParsed (Fold.func + Xor.func + 
            "fold xor true [true,false,true]") "true"
       
    [<Test>]
    member that.foldChangeType() =
        equalsParsed (Fold.func + 
            "fold (\\acc x -> if x then acc+1 else acc) 0 [true,false,true]") 
            "2"
   

[<TestFixture>]
type Reduce() =

    static member func = 
        Fold.func + """
let reduce f (x :: xs) = fold f x xs;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Reduce.func + "reduce") <| 
            Function (Function (x1, Function (x1, x1)), Function (ConstType (List, [x1]), x1))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Reduce.func + "reduce [1,2,3]")
        throwsWrongType (Reduce.func + "reduce (\\x -> x = true) [1,2,3]")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Reduce.func + "reduce (\\acc x -> acc + x) []") "raise"
        
    [<Test>]
    member that.reduceSum() =
        equalsParsed (Reduce.func + "reduce (\\acc x -> acc + x) [1,2,3]") "6"

    [<Test>]
    member that.reduceXor() =
        equalsParsed (Reduce.func + Xor.func + 
            "reduce xor [true,false,true]") "false"
       

[<TestFixture>]
type All() =

    static member func = 
        Not.func + Apply.func + """
let rec all pred ls =
    match ls with
    | [] -> true
    | x :: _ when not $ pred x -> false
    | _ :: xs -> all pred xs
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (All.func + "all") <| 
            Function (Function (x1, (ConstType (Bool, []))), Function (ConstType (List, [x1]), (ConstType (Bool, []))))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (All.func + "all [1,2,3]")
        throwsWrongType (All.func + "all (\\x -> x = true) [1,2,3]")

    [<Test>]
    member that.emptyList() =
        equalsParsed (All.func + "all (\\x -> x > 2) []") "true"
        
    [<Test>]
    member that.allMatch() =
        equalsParsed (All.func + "all (\\x -> x > 3) [4,5,6]") "true"
        
    [<Test>]
    member that.oneFails() =
        equalsParsed (All.func + "all (\\x -> x > 3) [3,5,6]") "false"


[<TestFixture>]
type Any() =

    static member func = """
let rec any pred ls =
    match ls with
    | [] -> false
    | x :: _ when pred x -> true
    | _ :: xs -> any pred xs
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Any.func + "any") <| 
            Function (Function (x1, (ConstType (Bool, []))), Function (ConstType (List, [x1]), (ConstType (Bool, []))))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Any.func + "any [1,2,3]")
        throwsWrongType (Any.func + "any (\\x -> x = true) [1,2,3]")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Any.func + "any (\\x -> x > 2) []") "false"
        
    [<Test>]
    member that.allFail() =
        equalsParsed (Any.func + "any (\\x -> x < 3) [4,5,6]") "false"
        
    [<Test>]
    member that.oneMatches() =
        equalsParsed (Any.func + "any (\\x -> x > 3) [3,5,2]") "true"

[<TestFixture>]
type Maximum() =

    static member func = 
        Reduce.func + """
let maximum ls =
    reduce (\acc x -> if acc < x then x else acc) ls
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [Orderable])
        matchesType (Maximum.func + "maximum") <| 
            Function (ConstType (List, [x1]), x1)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Maximum.func + "maximum [true,false,true]")
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
let minimum ls =
    reduce (\acc x -> if acc > x then x else acc) ls
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [Orderable])
        matchesType (Minimum.func + "minimum") <| 
            Function (ConstType (List, [x1]), x1)
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Minimum.func + "minimum [true,false,true]")
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
type Take() =

    static member func = """
let rec take n ls =
    match (n, ls) with
    | (0, _) -> []
    | (n, []) when n > 0 -> []
    | (n, x :: xs) when n > 0 -> x :: take (n-1) xs 
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Take.func + "take") <| 
            Function ((ConstType (Int, [])), Function (ConstType (List, [x1]), ConstType (List, [x1])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Take.func + "take true [true,false,true]")
        throwsWrongType (Take.func + "take 4 'c'")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Take.func + "take 0 []") "[]"
        
    [<Test>]
    member that.takeNegative() =
        equalsParsed (Take.func + "take (0-3) [2,3,4]") "raise"

    [<Test>]
    member that.takeZero() =
        equalsParsed (Take.func + "take 0 [2,3,4]") "[]"

    [<Test>]
    member that.takeNormal() =
        equalsParsed (Take.func + "take 2 [2,3,4]") "[2,3]"
             
    [<Test>]
    member that.takeMore() =
        equalsParsed (Take.func + "take 4 [2,3,4]") "[2,3,4]"


[<TestFixture>]
type Drop() =

    static member func = """
let rec drop n ls =
    match (n, ls) with
    | (0, ls) -> ls
    | (n, []) when n > 0 -> []
    | (n, x :: xs) when n > 0 -> drop (n-1) xs
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Drop.func + "drop") <| 
            Function ((ConstType (Int, [])), Function (ConstType (List, [x1]), ConstType (List, [x1])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Drop.func + "drop true [true,false,true]")
        throwsWrongType (Drop.func + "drop 4 'c'")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Drop.func + "drop 0 []") "[]"
        
    [<Test>]
    member that.dropNegative() =
        equalsParsed (Drop.func + "drop (0-3) [2,3,4]") "raise"

    [<Test>]
    member that.dropZero() =
        equalsParsed (Drop.func + "drop 0 [2,3,4]") "[2,3,4]"

    [<Test>]
    member that.dropNormal() =
        equalsParsed (Drop.func + "drop 2 [2,3,4]") "[4]"
             
    [<Test>]
    member that.dropMore() =
        equalsParsed (Drop.func + "drop 4 [2,3,4]") "[]"

           
[<TestFixture>]
type TakeWhile() =

    static member func = 
        Not.func + Apply.func + """
let rec takeWhile pred ls =
    match ls with
    | [] -> []
    | x :: xs when not $ pred x -> []
    | x :: xs -> x :: takeWhile pred xs
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (TakeWhile.func + "takeWhile") <| 
            Function (Function(x1, (ConstType (Bool, []))), Function (ConstType (List, [x1]), ConstType (List, [x1])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (TakeWhile.func + "takeWhile true [true,false,true]")
        throwsWrongType (TakeWhile.func + "takeWhile 4 'c'")

    [<Test>]
    member that.emptyList() =
        equalsParsed (TakeWhile.func + "takeWhile (\x -> x) []") "[]"
        
    [<Test>]
    member that.failsFirst() =
        equalsParsed (TakeWhile.func + "takeWhile (\x -> x > 2)  [2,3,4]") "[]"

    [<Test>]
    member that.failsMiddle() =
        equalsParsed (TakeWhile.func + "takeWhile (\x -> x > 2) [4,3,2,4]") "[4,3]"

    [<Test>]
    member that.neverFails() =
        equalsParsed (TakeWhile.func + "takeWhile (\x -> x < 5) [2,3,4]") "[2,3,4]"
             

[<TestFixture>]
type DropWhile() =

    static member func = 
        Not.func + Apply.func + """
let rec dropWhile pred ls =
    match ls with
    | [] -> []
    | x :: xs when not $ pred x -> ls
    | _ :: xs -> dropWhile pred xs
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (DropWhile.func + "dropWhile") <| 
            Function (Function(x1, (ConstType (Bool, []))), Function (ConstType (List, [x1]), ConstType (List, [x1])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (DropWhile.func + "dropWhile true [true,false,true]")
        throwsWrongType (DropWhile.func + "dropWhile 4 'c'")

    [<Test>]
    member that.emptyList() =
        equalsParsed (DropWhile.func + "dropWhile (\x -> x) []") "[]"
        
    [<Test>]
    member that.failsFirst() =
        equalsParsed (DropWhile.func + "dropWhile (\x -> x > 2)  [2,3,4]") "[2,3,4]"

    [<Test>]
    member that.failsMiddle() =
        equalsParsed (DropWhile.func + "dropWhile (\x -> x > 2) [4,3,2,4]") "[2,4]"

    [<Test>]
    member that.neverFails() =
        equalsParsed (DropWhile.func + "dropWhile (\x -> x < 5) [2,3,4]") "[]"
             

[<TestFixture>]
type Sublist() =

    static member func = 
        Take.func + Drop.func + Length.func + Apply.func + """
let sublist start size ls =
    if start < 0 || size > length ls then
        raise
    else
        take size $ drop start ls 
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Sublist.func + "sublist") <| 
            Function ((ConstType (Int, [])), Function ((ConstType (Int, [])), Function (ConstType (List, [x1]), ConstType (List, [x1]))))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Sublist.func + "sublist 'c'")
        throwsWrongType (Sublist.func + "sublist 4 'c'")
        throwsWrongType (Sublist.func + "sublist 0 2 'c'")

    [<Test>]
    member that.emptyList() =
        equalsParsed (Sublist.func + "sublist 0 0 []") "[]"
        
    [<Test>]
    member that.negativeStart() =
        equalsParsed (Sublist.func + "sublist (0-3) 2 [2,3,4]") "raise"
        
    [<Test>]
    member that.sizeLargerThanLength() =
        equalsParsed (Sublist.func + "sublist 0 4 [2,3,4]") "raise"

    [<Test>]
    member that.sublistAll() =
        equalsParsed (Sublist.func + "sublist  0 4 [4,3,2,4]") "[4,3,2,4]"

    [<Test>]
    member that.sublistTwo() =
        equalsParsed (Sublist.func + "sublist 1 2 [2,3,4]") "[3,4]"


[<TestFixture>]
type Exists() =

    static member func = """
let rec exists t ls =
    match ls with
    | [] -> false
    | x :: _ when x = t -> true
    | _ :: xs -> exists t xs
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [Equatable])
        matchesType (Exists.func + "exists") <| 
            Function (x1, Function (ConstType (List, [x1]), (ConstType (Bool, []))))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Exists.func + "exists 'c' [1,2,3]")
        throwsWrongType (Exists.func + "exists (\x -> x) []")
        throwsWrongType (Exists.func + "exists true [2,6]")
        
    [<Test>]
    member that.emptyList() =
        equalsParsed (Exists.func + "exists 5 []") "false"
        
    [<Test>]
    member that.doesntExist() =
        equalsParsed (Exists.func + "exists false [true, true, true]") "false"
        
    [<Test>]
    member that.exists() =
        equalsParsed (Exists.func + "exists 4 [1,2,3,4]") "true"

    [<Test>]
    member that.listOfLists() =
        equalsParsed (Exists.func + "exists [5] [[1],[2],[],[5]]") "true"
        

[<TestFixture>]
type Filter() =

    static member func = """
let rec filter pred ls =
    match ls with
    | [] -> []
    | x :: xs when pred x -> x :: filter pred xs
    | _ :: xs -> filter pred xs
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Filter.func + "filter") <| 
            Function (Function (x1, (ConstType (Bool, []))), Function (ConstType (List, [x1]), ConstType (List, [x1])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Filter.func + "filter 'c'")
        throwsWrongType (Filter.func + "filter (\x -> x) [1,2,3]")
        throwsWrongType (Filter.func + Remainder.func + 
            "filter (\x -> x % 2 = 0) \"hi\"")
        
    [<Test>]
    member that.emptyList() =
        equalsParsed (Filter.func + "filter (\x -> x) []") "[]"
        
    [<Test>]
    member that.doesntExist() =
        equalsParsed (Filter.func + "filter (\x -> x) [false,false,false]") "[]"
        
    [<Test>]
    member that.exists() =
        equalsParsed (Filter.func + Remainder.func + 
            "filter (\x -> x%2=0) [1,2,3,4]") "[2,4]"
        

[<TestFixture>]
type IndexOf() =

    static member func = 
        Negate.func + """
let indexOf t ls =
    let rec f index ls =
        match ls with
        | [] -> -1
        | x :: _ when t = x -> index
        | _ :: xs -> f (index + 1) xs
    ;
    f 0 ls
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [Equatable])
        matchesType (IndexOf.func + "indexOf") <| 
            Function (x1, Function (ConstType (List, [x1]), (ConstType (Int, []))))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (IndexOf.func + "indexOf 'c' [1,2,3]")
        throwsWrongType (IndexOf.func + "indexOf (\x -> x) []")
        throwsWrongType (IndexOf.func + "indexOf 1 [true,false]")
        
    [<Test>]
    member that.emptyList() =
        equalsParsed (IndexOf.func + "indexOf 5 []") "0-1"
        
    [<Test>]
    member that.doesntExist() =
        equalsParsed (IndexOf.func + "indexOf false [true, true, true]") "0-1"
        
    [<Test>]
    member that.exists() =
        equalsParsed (IndexOf.func + "indexOf 3 [1,2,3,4]") "2"

    [<Test>]
    member that.existsFirst() =
        equalsParsed (IndexOf.func + "indexOf 1 [1,2,3,4]") "0"
        

[<TestFixture>]
type Nth() =

    static member func = Flip.func +  """
let rec nth index ls =
    match (index, ls) with
    | (0, x :: _) -> x
    | (n, _ :: xs) when n > 0 -> nth (n-1) xs
;
let infixl 9 (!!) = flip nth;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        matchesType (Nth.func + "nth") <| 
            Function ((ConstType (Int, [])), Function (ConstType (List, [x1]), x1))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Nth.func + "nth 'c'")
        throwsWrongType (Nth.func + "nth (\x -> x) []")
        throwsWrongType (Nth.func + "nth 2 3")
        
    [<Test>]
    member that.emptyList() =
        equalsParsed (Nth.func + "nth 0 []") "raise"
        
    [<Test>]
    member that.negativeIndex() =
        equalsParsed (Nth.func + "nth (0-1) [1,2,3]") "raise"
        
    [<Test>]
    member that.largeIndex() =
        equalsParsed (Nth.func + "nth 4 [4,2,3,4]") "raise"

    [<Test>]
    member that.middleIndex() =
        equalsParsed (Nth.func + "nth 2 [1,2,3,4]") "3"
              
    [<Test>]
    member that.infix() =
        equalsParsed (Nth.func + "[1,2,3,4] !! 2") "3"
              

[<TestFixture>]
type Sort() =

    static member func = 
        Filter.func + Concat.func + Apply.func + Flip.func + """
let rec sort ls =
    match ls with
    | [] -> []
    | pivot :: xs ->
        (sort $ filter ((>) pivot) xs)
        @ [pivot] @
        (sort $ filter ((<=) pivot) xs)
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [Orderable])
        
        matchesType (Sort.func + "sort") <| 
            Function (ConstType (List, [x1]), ConstType (List, [x1]))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Sort.func + "sort 'c'")
        throwsWrongType (Sort.func + "sort [(\x -> x)]")
        throwsWrongType (Sort.func + "sort [true, false]")
        
    [<Test>]
    member that.emptyList() =
        equalsParsed (Sort.func + "sort []") "[]"
        
    [<Test>]
    member that.inOrder() =
        equalsParsed (Sort.func + "sort [1,2,3]") "[1,2,3]"
        
    [<Test>]
    member that.outOfOrder() =
        equalsParsed (Sort.func + "sort [4,2,3,1]") "[1,2,3,4]"

    [<Test>]
    member that.repeatedElements() =
        equalsParsed (Sort.func + "sort [4,2,1,4]") "[1,2,4,4]"


[<TestFixture>]
type Zip() =

    static member func = """
let rec zip x y =
    match (x, y) with
    | ([], _) -> []
    | (_, []) -> []
    | (x :: xs, y :: ys) -> (x, y) :: zip xs ys
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        let x2 = VarType ("y", [])

        matchesType (Zip.func + "zip") <| 
            Function (ConstType (List, [x1]), Function (ConstType (List, [x2]), ConstType (List, [Type.Tuple [x1;x2]])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Zip.func + "zip 'c'")
        throwsWrongType (Zip.func + "zip 3")
        throwsWrongType (Zip.func + "zip [true, false] false")
        
    [<Test>]
    member that.emptyList() =
        equalsParsed (Zip.func + "zip [] []") "[]"
        
    [<Test>]
    member that.sameSize() =
        equalsParsed (Zip.func + "zip [1,2,3] ['a', 'b', 'c']") <|
            "[(1, 'a'), (2, 'b'), (3, 'c')]"
        
    [<Test>]
    member that.differentSize() =
        equalsParsed (Zip.func + "zip [1,2,3] ['a', 'b']") <|
            "[(1, 'a'), (2, 'b')]"


[<TestFixture>]
type ZipWith() =

    static member func = """
let rec zipWith f x y =
    match (x, y) with
    | ([], _) -> []
    | (_, []) -> []
    | (x :: xs, y :: ys) -> f x y :: zipWith f xs ys
;

"""

    [<Test>]
    member that.testType() =
        let x = VarType ("x", [])
        let y = VarType ("y", [])
        let z = VarType ("z", [])

        matchesType (ZipWith.func + "zipWith") <| 
            Function (Function (y, Function (x, z)), 
                Function (ConstType (List, [y]), Function (ConstType (List, [x]), ConstType (List, [z]))))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (ZipWith.func + "zipWith (\x y -> x + y) ['a']")
        throwsWrongType (ZipWith.func + Concat.func + "zipWith (\x y -> x @ y) [\"alo\"] [[1,2],[2,3]]")
        throwsWrongType (ZipWith.func + "zipWith [true, false] false")
        
    [<Test>]
    member that.emptyList() =
        equalsParsed (ZipWith.func + "zipWith (\x y -> x + y) [] []") "[]"
        
    [<Test>]
    member that.sameSize() =
        equalsParsed (ZipWith.func + "zipWith (\x y -> x + y) [1,2,3] [1,2,3]") <|
            "[2,4,6]"
        
    [<Test>]
    member that.differentSize() =
        equalsParsed (ZipWith.func + "zipWith (\x y -> x + y) [1,2,3] [1,3]") <|
            "[2,5]"


[<TestFixture>]
type Unzip() =

    static member func = 
        Map.func + """
let unzip ls =
    let x = map (\(x, _) -> x) ls;
    let y = map (\(_, y) -> y) ls;
    (x, y)
;
"""

    [<Test>]
    member that.testType() =
        let x1 = VarType ("x", [])
        let x2 = VarType ("z", [])
        let x3 = Type.Tuple [x1; x2]

        matchesType (Unzip.func + "unzip") <| 
            Function (ConstType (List, [x3]), Type.Tuple [ConstType (List, [x1]); ConstType (List, [x2])])
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (Unzip.func + "unzip ['a']")
        throwsWrongType (Unzip.func + "unzip (1, 'a', 3)")
        
    [<Test>]
    member that.emptyList() =
        equalsParsed (Unzip.func + "unzip []") "([], [])"
        
    [<Test>]
    member that.sameSize() =
        equalsParsed (Unzip.func + "unzip [(1, 'a'), (2, 'b')]") <|
            "([1,2], ['a', 'b'])"
        

[<TestFixture>]
type ParseInt() =

    static member func = 
        Negate.func + Reverse.func + Compose.func + """
let parseInt (s: String): (Int) =
    match s with
    | x :: xs ->
        let rec f (s: String): (Int) =
            match s with
            | [] -> 0
            | x :: xs ->
                let n = 
                    match x with
                    | '0' -> 0
                    | '1' -> 1
                    | '2' -> 2
                    | '3' -> 3
                    | '4' -> 4
                    | '5' -> 5
                    | '6' -> 6
                    | '7' -> 7
                    | '8' -> 8
                    | '9' -> 9;
                n + 10 * f xs
        ;
        if x = '-' then
            negate . f . reverse $ xs
        else
            f (reverse s)
;
"""

    [<Test>]
    member that.testType() =
        matchesType (ParseInt.func + "parseInt") <| 
            Function (ConstType (List, [ConstType (Char, [])]), (ConstType (Int, [])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (ParseInt.func + "parseInt 'c'")
        throwsWrongType (ParseInt.func + "parseInt [1,2]")
        
    [<Test>]
    member that.emptyString() =
        equalsParsed (ParseInt.func + "parseInt \"\"") "raise"
        
    [<Test>]
    member that.negativeNumber() =
        equalsParsed (ParseInt.func + "parseInt \"-33\"") "0-33"
        
    [<Test>]
    member that.positiveNumber() =
        equalsParsed (ParseInt.func + "parseInt \"345\"") "345"
        
    [<Test>]
    member that.invalidNumber() =
        equalsParsed (ParseInt.func + "parseInt \"34.5\"") "raise"
        equalsParsed (ParseInt.func + "parseInt \"34a5\"") "raise"
        equalsParsed (ParseInt.func + "parseInt \"'35\"") "raise"


[<TestFixture>]
type PrintInt() =

    static member func = 
        Negate.func + Remainder.func + Concat.func + """
let rec printInt (i: Int): String =
    let printDigit d =
        match d with
        | 0 -> "0"
        | 1 -> "1"
        | 2 -> "2"
        | 3 -> "3"
        | 4 -> "4"
        | 5 -> "5"
        | 6 -> "6"
        | 7 -> "7"
        | 8 -> "8"
        | 9 -> "9"
    ;
    if i < 0 then   
        '-' :: printInt (-i)
    else if i < 10 then
        printDigit i
    else 
        let c = printDigit (i % 10);
        printInt (i/10) @ c
;
"""

    [<Test>]
    member that.testType() =
        matchesType (PrintInt.func + "printInt") <| 
            Function ((ConstType (Int, [])), ConstType (List, [ConstType (Char, [])]))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (PrintInt.func + "printInt 'c'")
        throwsWrongType (PrintInt.func + "printInt [1,2]")
        
    [<Test>]
    member that.eliminateZeroes() =
        equalsParsed (PrintInt.func + "printInt 001") "\"1\""
        
    [<Test>]
    member that.negativeNumber() =
        equalsParsed (PrintInt.func + "printInt (-33)") "\"-33\""
        
    [<Test>]
    member that.positiveNumber() =
        equalsParsed (PrintInt.func + "printInt 345") "\"345\""
        

[<TestFixture>]
type ParseBool() =

    static member func = """
let parseBool (s: String): Bool =
    if s = "true" then
        true
    else if s = "false" then
        false
    else 
        raise
;
"""

    [<Test>]
    member that.testType() =
        matchesType (ParseBool.func + "parseBool") <| 
            Function (ConstType (List, [ConstType (Char, [])]), (ConstType (Bool, [])))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (ParseBool.func + "parseBool 'c'")
        throwsWrongType (ParseBool.func + "parseBool [1,2]")
        
    [<Test>]
    member that.emptyString() =
        equalsParsed (ParseBool.func + "parseBool \"\"") "raise"
        
    [<Test>]
    member that.parseTrue() =
        equalsParsed (ParseBool.func + "parseBool \"true\"") "true"
        
    [<Test>]
    member that.parseFalse() =
        equalsParsed (ParseBool.func + "parseBool \"false\"") "false"
        
    [<Test>]
    member that.parseInvalid() =
        equalsParsed (ParseBool.func + "parseBool \"tru\"") "raise"
        equalsParsed (ParseBool.func + "parseBool \"trues\"") "raise"
        equalsParsed (ParseBool.func + "parseBool \"fasle\"") "raise"


[<TestFixture>]
type PrintBool() =

    static member func = """
let printBool (b: Bool): String =
    if b then
        "true"
    else
        "false"
;
"""

    [<Test>]
    member that.testType() =
        matchesType (PrintBool.func + "printBool") <| 
            Function ((ConstType (Bool, [])), ConstType (List, [ConstType (Char, [])]))
     
    [<Test>]
    member that.wrongParameter() =
        throwsWrongType (PrintBool.func + "printBool 'c'")
        throwsWrongType (PrintBool.func + "printBool 1")
        
    [<Test>]
    member that.printTrue() =
        equalsParsed (PrintBool.func + "printBool true") "\"true\""
        
    [<Test>]
    member that.printFalse() =
        equalsParsed (PrintBool.func + "printBool false") "\"false\""
        