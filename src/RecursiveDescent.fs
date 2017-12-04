module tell.RecursiveDescent

// Parses a Token list into a list of Statements.
// Statements are ar composed of Phrases and other Statements. 
// Phrases are flat sequences of Tokens and Names with balanced parantheses.
// The recursive descent parser does not look into the finer structure of Phrases.

open tell.Expressions
open tell.AST
open tell.Constants
open tell.Lexer

let expectToken tok tl = 
    match tl with
    | tok :: rest   ->  rest
    | _             ->  Error ("", unlexToken tok + " expected") :: tl

let expectEOL tl = 
    match tl with
    | BOL :: rest           ->  BOL :: rest
    | [] | [Whitespace _]   ->  []
    | _                     ->  Error ("", "EOL expected") :: tl

let rec parse (tl: Token list) : Statement list =
    match deb "parse" tl with
    | BOL::Keyword("story:")::rest  ->  let (title, rs) = parseEOL(rest) 
                                        let (story, rss) = parseStory (unlexTrim title) rs
                                        in story :: parse rss
    | BOL::Keyword("include")::rest ->  let ((title, withs), rs) = parseInvoke(rest)
                                        in IncludeStory (title, withs) :: parse rs
    | BOL::Keyword("where:")::rest  ->  let (where, rs) = parseWhere rest in where :: parse rs
    | []                            ->  []
    | _                             ->  let (comment, rs) = parseComment(tl) in comment::parse rs 

and parseComment (tl) = 
    match deb "parseComment" tl with
    | Whitespace _ :: Separator "(" :: rest ->  parseComment (Separator "(" :: rest)
    | Separator "(" :: rest                 ->  let (phrase, rss) = parsePhrase tl 1 []
                                                in  (Comment (literal phrase), expectToken (Separator ")") rss)
    | _                                     ->  let (comment, rs) = parseEOL(tl) 
                                                in (Comment (unlex comment), rs)

and parseInvoke tl : (string * Phrase) * Token list =
    match deb "parseInvoke" tl with
    | Whitespace w :: rest  -> parseInvoke rest
    | String (s,_) :: rest  -> parseInvokeOptWith s rest
    | Word s :: rest        -> parseInvokeOptWith s rest
    | _                     -> (("?", []), tl)

and parseInvokeOptWith title tl =
    match deb "parseInvoke2" tl with
    | Whitespace w :: rest      -> parseInvokeOptWith title rest
    | Keyword "with:" :: rest   -> let (clause, rs) = parsePhraseEOL rest in ((title, clause), rs)
    | _                         -> ((title, []), expectEOL tl)

and parseName tl =
    match deb "parseName" tl with
    | Whitespace w :: rest              -> parseName rest
    | Word ty :: Separator ":" :: rest  -> parseNameType (typeName ty) rest
    | Keyword "type:" :: rest           -> parseNameType TypeKind rest
    | Word n :: rest                    -> ((n, Unknown), rest)
    | String (n,_) :: rest              -> ((n, Unknown), rest)
    | _                                 -> (("?", Unknown), tl)

and parseNameType typ tl =
    match deb "parseNameType" tl with
    | Whitespace w :: rest              -> parseNameType typ rest
    | Word n :: rest                    -> ((n, typ), rest)
    | String (n,_) :: rest              -> ((n, typ), rest)
    | _                                 -> (("?", typ), tl)


and parseOptionalOtherwise tl =
    match deb "parseOtherwise" tl with
    | Keyword "otherwise:" :: rest  ->  let (invoke, rs) = parseInvoke rest in (Some invoke, rs)
    | _                             ->  (None, tl)                         

and parsePhrase tl (level: int) (forbiddenKW: string list): Phrase * Token list =
    match deb "parsePhrase" tl with
    | BOL :: rest when level = 0    ->  ([], BOL :: rest)
    | Separator "(" :: rest         ->  let (phrase, rs) = parsePhrase rest (level+1) forbiddenKW
                                        in  match rs with    
                                            | (Separator ")")::rs2 -> let (tail, rs3) = parsePhrase rs2 level forbiddenKW
                                                                      in (groupPhrase phrase tail, rs3)
                                            | _     -> (Literal (Separator "(") :: phrase @ [Literal (Error ("", "missing )"))], rs)
    | Separator ")" :: rest         ->  if level > 0 then ([], tl)
                                        else    let (phrase, rs) = parsePhrase rest level forbiddenKW
                                                in (Literal (Error (")", "unmatched )")) :: phrase, rs)
    | Keyword s :: rest  when List.contains s forbiddenKW 
                                    ->  ([], (if level = 0 then Keyword s else Error (s, "forbidden keyword")) :: rest)
    | Keyword "type:" :: rs         ->  let (v, rss) = parseNameType (TypeKind) rs 
                                        let (tail, rest) = parsePhrase rss level forbiddenKW in (Name v :: tail, rest)
    | Word s :: Separator ":" :: rs ->  let (v, rss) = parseNameType (typeName s) rs 
                                        let (tail, rest) = parsePhrase rss level forbiddenKW in (Name v :: tail, rest)
    | Separator ":" :: Word s :: rs ->  let (tail, rest) = parsePhrase rs level forbiddenKW in (Name (s, Unknown) :: tail, rest)
    | token :: rest                 ->  let (tail, rs) = parsePhrase rest level forbiddenKW in (Literal token :: tail, rs)
    | [token]                       ->  ([Literal token], [])
    | []                            ->  ([], [])

and groupPhrase inner more = Literal (Separator "(") :: inner @ Literal (Separator ")") :: more
                                                                      
and parsePhraseEOL tl : Phrase * Token list = let (clause, rest) = parsePhrase tl 0 [] in (clause, expectEOL rest)

and parsePredicate tl : Phrase * Token list = parsePhrase tl 0 predicateEndingKeywords
                                    
and parseScenario (title: string) (tl: Token list) : Statement * Token list =
    match deb "parseScenario" tl with
    | BOL::Keyword("where:")::rest      ->  let (where, rs) = parseWhere rest
                                            let (Scenario (_, stmts), rss) = parseScenario title (expectEOL rs)
                                            in  (Scenario (title, where :: stmts), rss)
                                        
    | BOL::Keyword("given:")::rest      ->  let (step, rs) = parsePhraseEOL rest
                                            let (Scenario (_, stmts), rss) = parseScenario title rs
                                            in  (Scenario (title, Given step :: stmts), rss)
                                        
    | BOL::Keyword("when:")::rest       ->  let (step, rs) = parsePhrase rest 0 ["otherwise:"]
                                            let (otherwise, rs2) = parseOptionalOtherwise rs
                                            let (Scenario (_, stmts), rs3) = parseScenario title (expectEOL rs2)
                                            in  (Scenario (title, WhenOtherwise (step, otherwise) :: stmts), rs3)
                                        
    | BOL::Keyword("then:")::rest       ->  let (step, rs) = parsePhraseEOL rest
                                            let (Scenario (_, stmts), rss) = parseScenario title rs
                                            in  (Scenario (title, Then step :: stmts), rss)

    | BOL::Keyword("and:")::rest        ->  let (step, rs) = parsePhraseEOL rest
                                            let (Scenario (_, stmts), rss) = parseScenario title rs
                                            in  (Scenario (title, AndAlso step :: stmts), rss)
                                        


    | BOL::Keyword("scenario:")::rest   ->  (Scenario (title, []), tl)

    | BOL::Keyword("story:")::rest      ->  (Scenario (title, []), tl)

    | [] | [BOL] | [Whitespace _]       ->  (Scenario (title, []), [])
    | BOL :: more                       ->  parseScenario title (trimBegin more)
    | _                                 ->  let (comment, rs) = parseComment(tl) 
                                            let (Scenario (_, stmts), rss) = parseScenario title rs
                                            in  (Scenario (title, comment :: stmts), rss)


and parseStory (title:string) (tl: Token list) : Statement * Token list = 
    match deb "parseStory" tl with
    | BOL::Keyword("about:")::rest      ->  let (name, rs) = parseName rest 
                                            let (phrase, rs2) = parsePhrase rs 0 []
                                            let (Story (_, stmts), rss) = parseStory title rs2 
                                            in  (Story (title, About (name, phrase) :: stmts), rss)

    | BOL::Keyword("with:")::rest       ->  let (clause, rs) = parsePhraseEOL(rest)
                                            let (Story (_, stmts), rss) = parseStory title rs
                                            in  (Story (title, With clause :: stmts), rss)
                                        
    | BOL::Keyword("include:")::rest    ->  let ((title, withs), rs) = parseInvoke(rest)
                                            let (Story (_, stmts), rss) = parseStory title rs
                                            in  (Story (title, IncludeStory (title, withs) :: stmts), rss)

    | BOL::Keyword("where:")::rest      ->  let (where, rs) = parseWhere rest
                                            let (Story (_, stmts), rss) = parseStory title rs
                                            in  (Story (title, where :: stmts), rss)
                                        
    | BOL::Keyword("scenario:")::rest   ->  let (title2, rs) = parseEOL(rest) 
                                            let (scene, rs2) = parseScenario (unlexTrim title2) rs
                                            let (Story (_, stmts), rss) = parseStory title rs2
                                            in  (Story (title, scene :: stmts), rss)

    | BOL::Keyword("story:")::rest      ->  (Story (title, []), tl)

    | [] | [BOL] | [Whitespace _]       ->  (Story (title, []), [])

    | BOL :: more                       ->  parseStory title (trimBegin more)
    | _                                 ->  let (comment, rs) = parseComment(tl) 
                                            let (Story (_, stmts), rss) = parseStory title rs
                                            in  (Story (title, comment :: stmts), rss)

and parseWhere tl =     let (pattern, rest) = parsePhrase (deb "parseWhere" (trimBegin tl)) 0 ("equals:" :: whereEndingKeywords)
                        let (replacement, rs) = parsePhrase (trimBegin (expectToken (Keyword "equals:") rest)) 0 whereEndingKeywords
                        in (Where (pattern, replacement), rs)

let rec parsePattern tl =
    match tl with
    | Separator ":" :: Word nt :: rest  ->  Name (nt, NonTerm) :: parsePattern rest
    | Separator "(" :: rest             ->  let (inner, rs) = parsePatternInner rest in groupPhrase inner (parsePattern (expectToken (Separator ")") rs))
    | lit :: rest                       ->  Literal lit :: parsePattern rest
    | []                                ->  []

and parsePatternInner tl =
    match tl with
    | Separator ")" :: rest             ->  ([], tl)
    | Separator ":" :: Word nt :: rest  ->  let (more, rs) = parsePatternInner rest in (Name (nt, NonTerm) :: more, rs)
    | Separator "(" :: rest             ->  let (inner, rs) = parsePatternInner rest 
                                            let (more, rss) = parsePatternInner (expectToken (Separator ")") rs)
                                            in  (groupPhrase inner more, rss)
    | lit :: rest                       ->  let (more, rs) = parsePatternInner rest in (Literal lit :: more, rs)
    | []                                ->  ([], [])
