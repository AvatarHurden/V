// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open Definition
open Evaluation

[<EntryPoint>]
let main argv = 
    printfn "%A" argv

    let app = App(Fn(Ident.X("x"), Int, OP(X(Ident.X("x")), Add, I(1))), OP(X(Ident.X("x")), Add, X(Ident.X("y"))))
    let defy = Let(Ident.X("y"), Int, I(40), app)
    let defx = Let(Ident.X("x"), Int, OP(I(10), Add, I(3)), defy)

    printfn "%A" defy
    printfn "%A" (replace (Ident.X("x")) (I(13)) defy)

    
    let fatName = Ident.X("fat")
    let xName = Ident.X("x")
    let fatMult = OP(X(xName), Multiply, App(X(fatName), OP(X(xName), Subtract, I(1))))
    let fnTerm =  Cond(OP(X(xName), Equal, I(0)), I(1), fatMult)
    let fat = LetRec(fatName, Int, Int, xName, fnTerm, App(X(fatName), I(5))) in

    printfn "%A"  (eval fat)

    let t2 = System.Console.ReadLine()
    0 // return an integer exit code

    