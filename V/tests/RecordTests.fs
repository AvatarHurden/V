module RecordTests

open NUnit.Framework
open FsUnit
open Definition
open Translation
open Evaluation
open Parser
open TypeInference

let private definitions = 
                ["""

                type alias Address = {
	                street: String,
	                number: Int,
	                city: String
                };

                type alias Person = {
	                name: String,
	                phone: String,
	                address: Address
                };


                let home: Address = {
	                street: "Ipiranga",
	                number: 456,
	                city: "Porto Alegre"
                };

                let me: Person = {
	                name: "Arthur",
	                phone: "+5551912345678",
	                address: home
                };
                """;
                "let stackedNumber = #address.number;";
                "let numberString = stackedNumber ~. (printInt, const . parseInt);";
                """let phoneToStruct phone =
                        let country = take 3 phone;
                        let prefix = take 2 $ drop 3 phone;
                        let rest = drop 5 phone;
                        {country: country, prefix: prefix, number: rest}
                    ;
                    let structToPhone struct phone =
                        let country = get #country struct;
                        let prefix = get #prefix struct;
                        let rest = get #number struct;
                        country @ prefix @ rest
                    ;
                    let phoneAsStruct = #phone ~. (phoneToStruct, structToPhone);""";
                  "let numberAndCountry = #('stackedNumber, 'phoneAsStruct.country);"]

let until n text =
    Seq.take n definitions |> flip Seq.append [text] |> String.concat "\n"

let isValid text =
    text |> parse |> flip translate stdlib.stdEnv |> typeInfer |> ignore

let evaluatesTo result text =
    let evaluated = text |> parse |> flip translate stdlib.stdEnv |> evaluate
    let expected = result|> parse |> flip translate stdlib.stdEnv |> evaluate
    evaluated |> should equal expected
    
let shouldFail text =
    (fun () -> text |> parse |> flip translate stdlib.stdEnv |> ignore) |> should throw typeof<ParseException> 
    

let compare text term =
    let evaluated = text |> parse |> flip translate stdlib.stdEnv |> evaluate
    evaluated |> should equal term
    
[<TestFixture>]
type TestRecordAccess() =

    [<Test>]
    member that.stack() =
        isValid <| until 2 "stackedNumber"
        evaluatesTo "456" <| until 2 "get stackedNumber me"

    [<Test>]
    member that.distort() =
        isValid <| until 3 "numberString"
        evaluatesTo "\"456\"" <| until 3 "get numberString me"

    [<Test>]
    member that.distort2() =
        isValid <| until 4 "phoneAsStruct"
        evaluatesTo "\"51\"" <| until 4 "me.'phoneAsStruct.prefix"
        
    [<Test>]
    member that.joined() =
        isValid <| until 5 "numberAndCountry"
        evaluatesTo "(456, \"+55\")" <| until 5 "me.'numberAndCountry"

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
type TestUpdateSyntax() =

    let record = "{a: {b:1,c:'c'},d:True, e:1}"

    let inner = ResRecord (["b", ResConstructor (I 1, []); "c", ResConstructor (C 'c', [])])
    
    [<Test>]
    member that.singleFieldUpdate() =
        compare ("(update d <- False)" + record) <| ResRecord (["a", inner
                                                                "d", ResConstructor (B false, []);
                                                                "e", ResConstructor (I 1, [])])

    [<Test>]
    member that.singleFieldUpdateBrackets() =
        compare ("update { d <- False}" + record) <| ResRecord (["a", inner
                                                                 "d", ResConstructor (B false, []);
                                                                 "e", ResConstructor (I 1, [])])
    
    [<Test>]
    member that.multipleUpdateFail() =
        shouldFail ("(update d <- False; e <- 2)" + record)
            
    [<Test>]
    member that.multipleUpdate() =
        compare ("update { d <- False; e <- 2}" + record) <| ResRecord (["a", inner
                                                                         "d", ResConstructor (B false, []);
                                                                         "e", ResConstructor (I 2, [])])
    [<Test>]
    member that.multipleUpdateOrder() =
        compare ("update { e <- 3; e <- 2}" + record) <| ResRecord (["a", inner
                                                                     "d", ResConstructor (B true, []);
                                                                     "e", ResConstructor (I 2, [])])
                                             
    [<Test>]
    member that.updateModify() =
        compare ("let f x = x + 1; update { e <~ f }" + record) <| ResRecord (["a", inner
                                                                               "d", ResConstructor (B true, []);
                                                                               "e", ResConstructor (I 2, [])])

    [<Test>]
    member that.updateModifyInside() =
        compare ("update { let f x = x + 1; e <~ f }" + record) <| ResRecord (["a", inner
                                                                               "d", ResConstructor (B true, []);
                                                                               "e", ResConstructor (I 2, [])])

    [<Test>]
    member that.updateDeclarationFail() =
        shouldFail ("update { e <~ f ; let f x = x + 1 }" + record)
        
    [<Test>]
    member that.updateUselessDeclaration() =
        compare ("update { e <- 2 ; let f x = x + 1 }" + record) <| ResRecord (["a", inner
                                                                                "d", ResConstructor (B true, []);
                                                                                "e", ResConstructor (I 2, [])])