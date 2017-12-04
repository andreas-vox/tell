module tell.AST

open tell.Expressions


// Provides the types for tell:'s abstract syntax tree.

type Token      = Word of string 
                | Number of string 
                | String of string * bool               // Only using double quotes: "abc" Boolean says if we've seen the closing quote
                | Text of string * int option           // A string enclosed in matched {} Int option counts the missing closing braces
                | Separator of string 
                | Whitespace of string 
                | BOL                                   // Beginning of line 
                | Error of string * string              // 1st string is the text that cause the error, 1nd string is a message
                | Keyword of string                     // All keywords end in a colon


and Kind        = Unknown | TypeKind | Typed of TypeExpr | NonTerm

and Var         = string * Kind                         // String is the name, obj is the value if bound

and Term        = Literal of Token 
                | Name of Var                            // Names come in three versions:  ":name" / "type: tname" / "tname: oname"

and Phrase      = Term list

and Statement   = Story of string * Statement list      // Cf. Gherkin, sometimes called feature
                | About of Var * Phrase                 // Introduces names to talk about
                | With of Phrase                        // For invariants and bindings
                | Comment of string
                | Scenario of string * Statement list   // Cf. Gherkin
                | Given of Phrase                       // Cf. Gherkin
                | WhenOtherwise of Phrase * InvokeWith option   // optional "otherwise:" part branches to alternate scenario
                | Then of Phrase                        // Cf. Gherkin
                | RunScenario of InvokeWith             // Includes a named scenario
                | IncludeStory of InvokeWith            // Includes another story
                | Notation of InvokeWith                // Support for changing notations, noop for now
                | AndAlso of Phrase                     // The "And" from Gherkin. Can be used with given:, when:, then:, and with:
                | Where of Refinement

and InvokeWith  = string * Phrase                       // The name of a story or scenario, and with: bindings
                
and Refinement  = Phrase * Phrase                       // Refinement: the 1st Phrase is a pattern which gets replaced by the 2nd Phrase

and Expression  = Expr<Token,Kind>

and TypeExpr    = Expr<string,int>



(*
let rec inferType (env: (Expression * Kind) list) exp =
    let (env2, t2) = lookup env exp
    in  if t2 <> Unknown then (env2, t2)
        else match exp with
            | Const (c)     -> if k <> Unknown then ((exp,k)::env, k) else (env, k)
            | Var (s)       -> if k <> Unknown then ((exp,k)::env, k) else (env, k)
            | Tuple es      -> let (env2, ts) = List.fold inferTypes es in (env2, Tuple ts)
            | App (f,es)    -> (FVintern f) @ (List.collect FVintern es)
            | Lambda (vs, e)-> let vars = FVintern e in removeVars vs vars

and inferTypes (p: (Expression * Kind) list, Kind list) Expression =
    let (env, t) = inferType 
    *)