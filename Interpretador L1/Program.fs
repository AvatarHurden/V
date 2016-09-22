// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open Definition
open Evaluation

[<EntryPoint>]
let main argv = 
    printfn "%A" argv

    let app = App(Fn(Ident.X("x"), Int, OP(X(Ident.X("x")), Add, V(I(1)))), OP(X(Ident.X("x")), Add, X(Ident.X("y"))))
    let defy = Let(Ident.X("y"), Int, V(I(40)), app)
    let defx = Let(Ident.X("x"), Int, OP(V(I(10)), Add, V(I(3))), defy)

    printfn "%A" defy
    printfn "%A" (replace (Ident.X("x")) (V(I(13))) defy)

    let t2 = System.Console.ReadLine()
    0 // return an integer exit code

    