module InternalTypeInferenceTests

open NUnit.Framework
open FsUnit
open Definition
open TypeInference

[<TestFixture>]
type TestEnvironment() =

    [<SetUp>]
    member this.setup() =
        TypeInference.varType <- 0

    [<Test>]
    member that.generateNew() =
        let env', typ = defaultEnv.instantiate (VarType ("a", []))

        typ |> should equal (VarType ("X0", []))
        env' |> should equal (defaultEnv.addVarAssoc "a" typ)

    [<Test>]
    member that.keepTraits() =
        let env', typ = defaultEnv.instantiate (VarType ("a", [Equatable]))

        typ |> should equal (VarType ("X0", [Equatable]))
        env' |> should equal (defaultEnv.addVarAssoc "a" typ)

    [<Test>]
    member that.addTraits() =
        let env = defaultEnv.addVarAssoc "a" (VarType ("X0", []))
        let env', typ = env.instantiate (VarType ("a", [Equatable]))

        typ |> should equal (VarType ("X0", [Equatable]))
        env' |> should equal env

    [<Test>]
    member that.traverseTraits() =
        let inner = (VarType ("b", []))
        let first = (VarType ("a", [RecordLabel ("w", inner)]))
        let tupled = ConstType (ConstructorType.Tuple 2, [first; inner])
        let env, typ = defaultEnv.instantiate tupled

        let inner' = (VarType ("X0", []))
        let first' = (VarType ("X1", [RecordLabel ("w", inner')]))
        let tupled' = ConstType (ConstructorType.Tuple 2, [first'; inner'])
        typ |> should equal tupled'

        let env' = defaultEnv.addVarAssoc "a" first'
        let env' = env'.addVarAssoc "b" inner'
        env |> should equal env'   