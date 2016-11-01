module Parser2

open System.Text.RegularExpressions
open Definition
open System
open stdlib

//#region Helper Types, Modules and Functions

module Path =
    let appDir = AppDomain.CurrentDomain.SetupInformation.ApplicationBase
    let makeAppRelative fileName = System.IO.Path.Combine(appDir, fileName)

exception InvalidEntryText of string

type private extendedOP =
    // Infix operators
    | Def of op
    | Pipe
    | BackwardsPipe
    | Remainder
    | Concat
    | And
    | Or
    // Prefix operators
    | Negate

let private operatorsAtPriority i =
    match i with             
    | 0 -> [Negate]                          
    | 1 -> [Def Application]            
    | 2 -> [Def Multiply; Def Divide; Remainder]  
    | 3 -> [Def Add; Def Subtract]   
    | 4 -> [Def Cons]
    | 5 -> [Concat]    
    | 6 -> 
        [Def LessOrEqual; Def LessThan; Def Equal; Def Different; 
        Def GreaterThan; Def GreaterOrEqual; Pipe; BackwardsPipe]
    | 7 -> [And]
    | 8 -> [Or]
    | _ -> []

type private extendedTerm =
    | Term of term
    | Prefix of extendedOP
    
let private splitSpaces (term: string) =
    term |> Seq.skipWhile Char.IsWhiteSpace |> String.Concat
  
let rec private matchStart (text: string) matches =
    match matches with
    | [] -> 
        false, ""
    | x::rest when text.StartsWith(x) ->
        true, x
    | x::rest ->
        matchStart text rest

let private raiseExp x = raise <| InvalidEntryText x

//#endregion

//#region Identifier and Type Functions

let parseIdent text = 
    let trimmedText = splitSpaces text
    let prohibited = " .,;:+-/*<=>(){}[]%!@\\'\"".ToCharArray()
    let ident = String.Concat (trimmedText |> 
        Seq.takeWhile (fun x -> not <| Seq.exists ((=) x) prohibited))
    match ident with
    | "let" | "true" | "false" | "if" | "then" | "else" 
    | "fn" | "letrec"| "nil" | "head" | "tail" | "raise" 
    | "try" | "except" | "for" | "in" | "empty?" ->
        raiseExp <| sprintf "A variable cannot be called %A at %A" ident text
    | "" ->
        raiseExp <| sprintf "Cannot declare an empty identifier at %A" text
    | _ ->
        trimmedText.Substring(ident.Length), ident

let rec parseType (text: string) closings =
    let trimmedText = splitSpaces text
    
    let remainingText, typ1 = 
        if trimmedText.StartsWith("(") then
            let (s: string), t = parseType (trimmedText.Substring 1) [")"]
            s.Substring 1, t
        elif trimmedText.StartsWith("[") then
            let (s: string), t = parseType (trimmedText.Substring 1) ["]"]
            s.Substring 1, List t
        elif trimmedText.StartsWith("Int") then
            trimmedText.Substring("Int".Length), Int
        elif trimmedText.StartsWith("Bool") then
            trimmedText.Substring("Bool".Length), Bool
        elif trimmedText.StartsWith("Char") then
            trimmedText.Substring("Char".Length), Definition.Char
        elif trimmedText.StartsWith("String") then
            trimmedText.Substring("String".Length), List Definition.Char
        else
            raiseExp <| sprintf "Could not parse type at %A" trimmedText
    
    let nextToken = splitSpaces remainingText

    let ends, closing = matchStart nextToken closings
    if ends then
        nextToken, typ1
    elif nextToken.StartsWith("->") then
        let typ2Text = nextToken.Substring("->".Length)
        let remaining, typ2 = parseType typ2Text closings
        remaining, Function (typ1, typ2)
    else
        raiseExp <| sprintf "Could not parse type at %A" nextToken

let rec parseIdentTypePair (text:string) closings =
    let typeString, id = parseIdent text
    
    let trimmedText = splitSpaces typeString
    
    let rest, typ =
        let ends, closing = matchStart trimmedText closings
        if ends then
            trimmedText, None
        elif trimmedText.StartsWith(":") then
            let s, t = parseType (trimmedText.Substring 1) closings
            s, Some t
        else
            raiseExp <| sprintf "Expected %A, but found %A" closings trimmedText

    rest, (id, typ)
            
let rec parseParameters text closings =
    let trimmedText = splitSpaces text

    let ends, closing = matchStart trimmedText closings
    if ends then
        trimmedText, []
    else
        let removedFirst, (id, typ) = parseIdentTypePair trimmedText <| closings @ [","]

        let nextParameterText =
            if removedFirst.StartsWith "," then
                removedFirst.Substring(",".Length)
            else
                removedFirst

        let removedRest, restPairs = parseParameters nextParameterText closings
        removedRest, [id, typ] @ restPairs 

//#endregion

//#region Char and String functions

let rec parseStringLiteral (text: string) closing =
    match text.ToCharArray() |> Array.toList with
    | [] ->
        raiseExp <| sprintf "Could not find closing %A" closing
    | '\\'::tail ->
        let current = 
            match tail with
            | 'n'::rest -> "\n"
            | _ ->
                raiseExp <| sprintf "Invalid escaped char at %A" text
        let remaining, parsed = parseStringLiteral (String.Concat tail) closing
        remaining, current + parsed
    | t::tail when text.StartsWith(closing) -> 
        t, ""
    | t::tail ->
        let remaining, parsed = parseStringLiteral (String.Concat tail) closing
        remaining, t.ToString() + parsed
        

let private parseSingleChar (text: string) =
    if text.Length = 0 then
        raise <| InvalidEntryText "Can not parse an empty character"

    if text.[0] = '\\' then
        match text.[1] with
        | 'n' -> '\n', 2
        | 'b' -> '\b', 2
        | 'r' -> '\r', 2
        | 't' -> '\t', 2
        | '\\' -> '\\', 2
        | '"' -> '\"', 2
        | '\'' -> '\'', 2
        | _ -> sprintf "Invalid escaped char at %A" text |> InvalidEntryText |> raise
    else
        text.[0], 1


//#endregion