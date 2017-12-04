module tell.Lexer

open tell.Expressions
open tell.AST

// Parses a string into a Token list.AST and applies notation

// Grammar for Tokens is:

// token        ::= word | number | keyword | string | text | separator | BOL | whitespace
// word         ::= {Letter}{LetterOrDigit}*
// number       ::= {Digit}+
// keywords     ::= {one of headKeywords or inlineKeywords} ':'
// string       ::= '"' {any char but "} '"'
// text         ::= '{' {any sequence of chars with balanced braces}  '}'
// BOL          ::= {crlf} | {cr} | {lf}
// whitespace   ::= {any sequence of spaces, tabs, etc} | {converted comment}
// separator    ::= {any char but whitespace, letter or number}

// Notation can introduce alternatives for keywords, e.g. BOL "And"  ->  "and:"
// The keywords "comment:" and "shorthand:" are interpreted early, converting following resp. preceding text into whitespace

let headKeywords = [
    "story" 
    "about"
    "scenario"
    "given"
    "when"
    "then"
    "where"
    "notation"          // reserved for notation changes
    "include"
    "run"
    "foreach"           // reserved for loops
    "repeat"            // reserved for loops
    "until"             // reserved for loops
    "loop"              // reserved for loops
    ]

let inlineKeywords = [
    "and"
    "with"
    "or"
    "not"
    "type"
    "otherwise"
    "comment"           // following text becomes whitespace
    "shorthand"         // preceding text becomes whitespace
    "tell"              // references other story
    "equals"            // =
    "becomes"           // :=
    "send"              // ->, send message
    ]

let notationalHeadKeywords = "and" :: "with" :: headKeywords     // colon optional at beggining of line

let whereEndingKeywords = List.map (fun s -> s + ":") headKeywords
let predicateEndingKeywords =  "and:" :: "or:" :: "not:" :: "otherwise:" :: whereEndingKeywords   


type CharClass = Newline | Digit  | Letter | Space | Quote | LBrace | RBrace | Other

let getCharClass (c:char) = if c = '\n' || c = '\r' then (Newline, c)
                            else if System.Char.IsDigit(c) then (Digit, c)
                            else if System.Char.IsLetter(c) then (Letter, c)
                            else if System.Char.IsWhiteSpace(c) then (Space, c)
                            else if c = '"' then (Quote, c)
                            else if c = '{' then (LBrace, c)
                            else if c = '}' then (RBrace, c)
                            else (Other, c)


let str (c:char) = c.ToString()

let rec trimBegin tl =
    match tl with
    | Whitespace w :: rest  ->  trimBegin rest
    | _                     ->  tl

let rec trimEnd tl =
    match tl with
    | []                    -> []
    | [Whitespace w]        -> []
    | tok :: rest           -> tok :: trimEnd rest

let trim tl = tl |> trimBegin |> trimEnd

let rec buildTokens (state : Token list) (c : CharClass * char) =
    match (state, c) with
    | (BOL::earlier, (Newline,c))           ->  BOL :: earlier       // gobble up newlines
    | (BOL::earlier, (Space,c))             ->  BOL :: earlier       // and spaces at beginning of line
    | ( [], (Newline, c))                   -> [BOL]
    | ( [], (Digit, c))                     -> [Number (str c)]
    | ( [], (Letter, c))                    -> [Word (str c)]
    | ( [], (Quote, c))                     -> [String ("", true)]
    | ( [], (LBrace, c))                    -> [Text ("", Some 1)]
    | ( [], (RBrace, c))                    -> [Error ("}", "mismatched }")]
    | ( [], (Space, c))                     -> [Whitespace (str c)]
    | ( [], (Other, c))                     -> [Separator (str c)]
    | (Word s :: earlier,   (Newline, c))   -> BOL :: Word s :: earlier
    | (Word s :: earlier,   (Digit, c))     -> Word (s + str c) :: earlier
    | (Word s :: earlier,   (Letter, c))    -> Word (s + str c) :: earlier
    | (Word s :: earlier,   (Quote, c))     -> String ("", true) :: Word s :: earlier
    | (Word s :: earlier,   (LBrace, c))    -> Text ("", Some 1) :: Word s :: earlier
    | (Word s :: earlier,   (RBrace, c) )   -> Error ("}", "mismatched }") :: Word s :: earlier
    | (Word s :: earlier,   (Space, c))     -> Whitespace (str c) :: Word s :: earlier
    | (Word s :: earlier,   (_, c))         -> Separator (str c) :: Word s :: earlier
    | (String (s, true) :: er, (Quote, c))  -> String (s, false) :: er
    | (String (s, true) :: er, (Newline, c))-> BOL :: Error ("\"" + s, "string exceeds line") :: er
    | (String (s, true) :: er, (_, c))      -> String (s + str c, true) :: er
    | (Text (s, Some l) :: er, (RBrace, c)) -> if l > 1 then Text (s + str c, Some (l-1)) :: er else Text (s, None) :: er
    | (Text (s, Some l) :: er, (LBrace, c)) -> Text (s + str c, Some (l+1)) :: er
    | (Text (s, Some l) :: er, (_, c) )     -> Text (s + str c, Some l) :: er
    | (Number s :: earlier, (Digit,c))      -> Number (s + str c) :: earlier
    | (Number s :: earlier, (x,c))          -> (buildTokens [] (x, c)) @  Number (s) :: earlier
    | (Whitespace s :: earlier,  (Space, c))  -> Whitespace (s + str c) :: earlier
    | (earlier, (x, c))                     -> (buildTokens [] (x, c)) @ earlier    // reset


let checkDelimiters (tl : Token list) =
    match tl with
    | (String (s, true)) :: rest        -> Error ("\"" + s, "unclosed string") :: rest
    | (Text (s, Some l))  :: rest       -> Error ("{" + s, l.ToString() + " unclosed {") :: rest
    | _                                 -> tl
    

let rec findKeywords (tl : Token list) =
    match tl with
    | [] -> []
    | (Word s) :: (Separator ":") :: rest -> if List.contains s headKeywords then BOL :: Keyword (s + ":") :: findKeywords(rest) 
                                             else if List.contains s inlineKeywords then Keyword (s + ":") :: findKeywords(rest)
                                             else (Word s) :: (Separator ":") :: findKeywords(rest) 
    | head :: tail -> head :: findKeywords tail

// not configurable for now
let rec applyNotation (tl: Token list)  = 
    match tl with
    | BOL :: Word s :: rest -> let lowerS = String.map System.Char.ToLowerInvariant s in
                                    if List.contains lowerS notationalHeadKeywords 
                                        then BOL :: Keyword (lowerS + ":") :: applyNotation rest 
                                        else BOL :: Word s :: applyNotation rest 
    | Whitespace w :: Separator ":" :: Separator "=" :: Whitespace ww :: rest 
                                        -> Whitespace w :: Keyword "becomes:" ::  Whitespace ww :: applyNotation rest
    | Whitespace w :: Separator "=" :: Whitespace ww ::rest                 
                                        -> Whitespace w :: Keyword "equals:" :: Whitespace ww :: applyNotation rest
    | x :: rest             -> x :: applyNotation rest
    | []                    -> []


let rec unlexToken (tok: Token) =
    match tok with
    | Word s            -> s 
    | String (s,_)      -> s 
    | Text (s,_)        ->  s 
    | Number s          ->  s 
    | BOL               -> "\n"
    | Separator s       ->  s
    | Whitespace s      ->  s
    | Keyword "becomes:"-> ":="
    | Keyword "equals:" -> "="
    | Keyword s         ->  s
    | Error (s, _)      ->  s 

let unlex (tl: Token list) = tl |> List.map unlexToken |> List.fold (+) ""

let unlexTrim tl = tl |> trim |> unlex


let deb s (tl: Token list) = tl // let _ = do printfn "_%s_ %d .. %s" s (List.length tl) (if List.isEmpty tl then "EOF" else (List.head tl).ToString() + ": " + unlexToken (List.head tl)) in tl

let rec parseComments (currentLine: Token list) (inp : Token list) =
    match inp with
    | Keyword "shorthand:" :: rest  ->  Whitespace ((unlex currentLine) + "shorthand:") :: parseComments [] rest
    | Keyword "comment:" :: rest    ->  let (comment, rs) = parseEOL rest 
                                        in currentLine @ Whitespace ("comment:" + unlex comment) :: parseComments [] rs
    | Keyword other :: rest         ->  currentLine @ (Keyword other :: parseComments [] rest)
    | BOL :: rest                   ->  currentLine @ (BOL :: parseComments [] rest)
    | other :: rest                 ->  parseComments (currentLine @ [other]) rest
    | []                            ->  currentLine 

and parseEOL tl = 
    match tl with
    | BOL :: rest   -> ([], BOL::rest)
    | x :: rest     -> let (line, rs) = parseEOL(rest) in (x::line, rs)
    | []            -> ([], [])

let rec lex (input: char seq) : Token list = 
    input |> Seq.map getCharClass 
          |> Seq.fold buildTokens [] |> checkDelimiters |> List.rev
          |> findKeywords
          |> applyNotation
          |> parseComments []
(*
let rec listType t : string =
    match t with
    | TVar (s, bound)   -> s
    | TFun (a,b)        -> listTypes " -> " a + " -> " + listType b
    | TProd (a,b)       -> "(" + listType a + " * " + listType b + ")"
    | TSum (a,b)        -> "(" + listType a + " + " + listType b + ")"
    | TUnion []         -> "Never"
    | TIntersect []     -> "Any"
    | TUnion ts         -> "[" + listTypes " | " ts + "]"
    | TIntersect ts     -> "[" + listTypes " & " ts + "]"

and listTypes sep ts =
    match ts with
    | [t]               -> listType t
    | first :: rest     -> listType first + sep + listTypes sep rest
    | []                -> "()"
*)

let rec listType (t: TypeExpr) =
    match t with
    | Const (n)         -> n
    | Var (n)           -> ":" + n
    | App (f, args)     -> listType f + "(" + listTypes "," args + ")"
    | Lambda (v,e)      -> "lambda " + listVars v + "." + listType e
    | Tuple es          -> "(" + listTypes "*" es + ")"

and listTypes sep ts =
    match ts with
    | [t]               -> listType t
    | t :: rest         -> listType t + sep + listTypes sep rest 
    | []                -> ""

and listVars vs =
    match vs with
    | (v) :: rest       -> ":" + v + " " + listVars rest 
    | []                -> ""

let rec literal (p: Phrase) =
    match p with
    | Literal tok :: rest       ->  unlexToken tok + literal rest
    | Name (nam, ty) :: rest    ->  (match ty with
                                    | Unknown    -> ":" + nam
                                    | TypeKind   -> "type: " + nam
                                    | Typed t     -> listType t + ": " + nam
                                    | NonTerm    -> "<" + nam + ">") + literal rest
    | []                        ->  ""

let rec selector (pattern: Phrase) =
    match pattern with
    | Literal (Separator "(") :: rest   -> selector (dropParenthesis 1 rest)
    | Literal (Separator s) :: rest     -> s + selector rest
    | Literal (Whitespace s) :: rest    -> "_" + selector rest 
    | Literal (Word s) :: rest          -> s + selector rest
    | Literal (Number s) :: rest        -> s  + selector rest
    | Literal (String (s,_)) :: rest    -> "\"" + s + "\"" + selector rest
    | Literal (Text (s,_)) :: rest      -> "{?}" + selector rest
    | Literal (Keyword s) :: rest       -> s + "?"  + selector rest
    | Name (n,k) :: rest                -> ":"  + selector rest
    | []                                -> ""
    | _                                 -> "??"

and dropParenthesis level ps =
    match ps with
    | Literal (Separator "(") :: rest   ->  dropParenthesis (level+1) rest
    | Literal (Separator ")") :: rest   ->  if level = 1 then rest
                                            else dropParenthesis (level-1) rest
    | _ :: rest                         ->  dropParenthesis level rest
    | []                                ->  []

