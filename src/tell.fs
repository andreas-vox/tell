// "tell:" is a language for requirements capturing and simulation
// It can be described as Gherkin on steroids, where the steroids include "order sorted type lambda calculus", 
// "first order logic with equality", "top-down refinement", a build in parser generator and "state machines"
// The language is parsed in 4 stages:
//  *   Lexing returns a token list which might be modified by notation conventions
//  *   A recursive descent parser returns a structure of statements and phrases
//  *   The where statements are used as grammar rules to parse phrases into clauses and expressions
//  *   Step 3 might provide more than one interpretation for each phrase. In a final step, each interpretation
//      is typed and weighted by priority. The best interpretation is moved to the front of the list

open tell.Expressions
open tell.AST
open tell.Constants
open tell.Lexer

let res = lex "}story: alala 123h = aha := 12 
about :          hm{bohai{}}so\" { 123\" shorthand: soso
     burp\" 


with: type: user = tell: { intrinsic {{"

let ures = unlex res

open tell.RecursiveDescent


let x =  (lex "story: xy about: type:T 
about: T:agent lala 
about: X 
scenario: tz 
given: one or two 
when: (T:sth of type:T) (comes (from :myUser)) otherwise: alt with: :param=42 
where: one or two = 1) , (2" )

printfn "%s" (unlex x)
let test_story = parse x


open tell.ChartParser

let test_chart = ref (initChart (Rules.getRules "*" "*" test_story) (parsePattern (lex "one one or two two and: 1 or: 2")))

//printfn "%d %d" test_chart.byStart.Length test_chart.input.Length 
//printfn "%A" test_chart.byStart 
//printfn "%A" test_chart.rules

runChart test_chart

let mutable count = 0
let mutable result : Expression list = []
//for i in 0 .. (!test_chart).byStart.Length - 1 do
let i = 0
in  for entry in (!test_chart).completedByStart.[0] do
        if (!entry).start = 0 &&  (!entry).pos = (!test_chart).input.Length then 
            if (!entry).NT = "" 
            then 
                result <- [compileParseEntry (!test_chart).input entry]
                (*
                let cfs = (searchConflicts entry)
                printfn "Conflicts: %A" (List.map (fun pe -> List.map (listDerivation (!test_chart).input) (!pe).sppfPtr) cfs)
                for cf in cfs do
                    count <- count + 1
                    printfn "Conflict %d: %s" count (listParseEntry !cf) 
                    for altSppf in (!cf).sppfPtr do
                        let altEntry = ref {!cf with sppfPtr= [altSppf]} 
                        printfn "%A" (visitSPPF (Rules.getNth 1) (compile ((!test_chart).input)) altEntry)
                result <- visitSPPF (Rules.getNth 1) (compile ((!test_chart).input)) entry
                *)
            else 
                printfn " '%s' # %d" (!entry).NT (!entry).sppfPtr.Length; 

printfn "Found %d %s." count (if count > 1 then "conflicts" else "conflict") 
printfn "%A" result

if count > 0 then
    for i in 0 .. (!test_chart).byStart.Length - 1 do
        printfn "STATE %d" i
        for entry in (!test_chart).byStart.[i] do
            printfn "%s" (listParseEntry !entry)
        printfn "COMPLETED:"
        for entry in (!test_chart).completedByStart.[i] do
            printfn "%d - %d %s" (!entry).start (!entry).pos (!entry).NT
        printfn "BLOCKED:" 
        for entry in (!test_chart).blockedByPos.[i] do
            printfn "%s" (listParseEntry !entry)
        printfn "TODO:"
        for entry in (!test_chart).todoByPos.[i] do
            printfn "%d - %d %s" (!entry).start (!entry).pos (!entry).NT
        printfn "--------"
