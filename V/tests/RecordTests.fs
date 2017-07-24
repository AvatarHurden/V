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
                "let stackedNumber = #address :. #number;";
                "let numberString = stackedNumber ~. (printInt, parseInt);";
                """let phoneToStruct phone =
                        let country = take 3 phone;
                        let prefix = take 2 $ drop 3 phone;
                        let rest = drop 5 phone;
                        {country: country, prefix: prefix, number: rest}
                    ;
                    let structToPhone struct =
                        let country = get #country struct;
                        let prefix = get #prefix struct;
                        let rest = get #number struct;
                        country @ prefix @ rest
                    ;
                    let phoneAsStruct = #phone ~. (phoneToStruct, structToPhone);""";
                  "let numberAndCountry = #(stackedNumber, phoneAsStruct :. #country);"]

let until n text =
    Seq.take n definitions |> flip Seq.append [text] |> String.concat "\n"

let isValid text =
    text |> parse |> flip translate stdlib.stdEnv |> typeInfer |> ignore

let evaluatesTo result text =
    let evaluated = text |> parse |> flip translate stdlib.stdEnv |> evaluate
    let expected = result|> parse |> flip translate stdlib.stdEnv |> evaluate
    evaluated |> should equal expected

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
        evaluatesTo "\"51\"" <| until 4 "me ^. phoneAsStruct :. #prefix"
        
    [<Test>]
    member that.joined() =
        isValid <| until 5 "numberAndCountry"
        evaluatesTo "(456, \"+55\")" <| until 5 "me ^. numberAndCountry"
    