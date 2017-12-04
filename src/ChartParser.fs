module tell.ChartParser

open tell.Expressions
open tell.AST 
open tell.Constants
open tell.RecursiveDescent

// Implements an Early parser with Shared Packed Parse Forest (SPPF) pointers
// Rules are either generated from where:-Statememnts or provided as defaultRules.


let lex = tell.Lexer.lex
let literal = tell.Lexer.literal

module Rules =
    type Priority = Prio of int | LRPrio of (int*int) | DerivedPrio of int | NoPrio
    type ParseRule  = {NT: string; Pattern: Phrase; Prio: Priority; Action: Expression list -> Expression}


    let makeRule (nt: string, pattern: string, priority: Priority, action: Expression list -> Expression) = 
        let p = parsePattern (lex pattern) in {NT=nt; Pattern=p; Prio=priority; Action= action}

    let rec getNth (i: int) (lst: 'T list) :'T =
        if i > lst.Length then printfn "ERROR: entry %d does not exist in %A" i lst
        match lst with
        | hd :: _  when i = 1   -> hd
        | _ :: tl               -> getNth (i-1) tl

    let rec getOnly (lst: Expression list) : Expression =
        match lst with
        | [only]                -> only
        | _                     -> printfn "WARNING: no single elem in getOnly: %A" lst; App (tupleGenE, lst)


    let extendTupleR left right =
        match right with
        | App (op, args) when op = tupleGenE    -> App (op, left :: args)
        | _                                     -> App (tupleGenE, [left; right])


    let  defaultRules : ParseRule list = 
        List.map makeRule [
            ("clause", ":exprlist",                 Prio 0, getOnly)
            ("clause", ":exprlist =:exprlist",      Prio 4, fun args -> App (equalsGenE, [getNth 1 args; getNth 4 args]))
            ("clause", ":term=:exprlist",           Prio 4, fun args -> App (equalsGenE, [getNth 1 args; getNth 3 args]))
            ("clause", ":exprlist :=:exprlist",     Prio 4, fun args -> App (becomesGenE, [getNth 1 args; getNth 4 args]))
            ("clause", ":term:=:exprlist",          Prio 4, fun args -> App (becomesGenE, [getNth 1 args; getNth 3 args]))
            ("clause", "not: :clause",              Prio 1, fun args -> App (notE, [getNth 3 args]))
            ("clause", "not::term",                 Prio 1, fun args -> App (notE, [getNth 2 args]))
            ("clause", ":clause and::clause",       LRPrio (2,3), fun args -> App (andE, [getNth 1 args; getNth 4 args]))
            ("clause", ":term:and::clause",         LRPrio (2,3), fun args -> App (andE, [getNth 1 args; getNth 3 args]))
            ("clause", ":clause or::clause",        LRPrio (2,3), fun args -> App (orE, [getNth 1 args; getNth 4 args]))
            ("clause", ":term:or::clause",          LRPrio (2,3), fun args -> App (orE, [getNth 1 args; getNth 3 args]))

            ("primary", ":whitesp:primary",         NoPrio, getNth 2 )
    //        ("primary", ":operator:primary", 10)
            ("primary", ":literal",                 NoPrio, getOnly )
    //        ("primary", ":word",                    NoPrio, getOnly )
            ("primary", ":term",                    NoPrio, getOnly )

            ("term", ":name",                       NoPrio, getOnly )
            ("term", ":word",                       NoPrio, getOnly )
            ("term", ":what",                       NoPrio, getOnly )
            ("term", "(:clause)",                   Prio 100, getNth 2 )
    
            ("expr", ":primary",                    NoPrio, getOnly )
    //        ("expr", ":primary :operator:expr", 10)
    //        ("expr", ":term:operator:expr", 10)

    //        ("operator", "+", 19)    // TODO: move to Token and let notation handle it
    //        ("operator", "-", 19)
    //        ("operator", "*", 19)
    //        ("operator", "/", 19)
    //        ("operator", "^", 19)
    //        ("operator", "~", 19)
    //        ("operator", "&", 19)
    //        ("operator", "|", 19)
    //        ("operator", "_", 19)
    //        ("operator", "@", 19)
    //        ("operator", "#", 19)
    //        ("operator", "<", 19)
    //        ("operator", ">", 19)
    //        ("operator", "<=", 19)
    //        ("operator", ">=", 19)
    //        ("operator", "<-", 19)
    //        ("operator", "->", 19)

            ("exprlist", ":expr",                   Prio 8, getOnly )
            ("exprlist", ":expr:exprlist",          Prio 8, fun args -> extendTupleR (getNth 1 args) (getNth 2 args) )
    ]


    let mkWhat (refine: Refinement) (args: Expression list) : Expression =
        let (pattern, body ) = refine in 
        App (Const (Word (Lexer.selector pattern)), args)

    let makeStartRule s = {NT=""; Pattern=parsePattern(lex s); Prio=NoPrio; Action= getNth 1}
    
    let rec makeRefinementRule ((left, right): Refinement) : ParseRule =
        let pattern = replaceVarsWithNonTerms left
        in {NT="what"; Pattern=pattern; Prio=Prio 10; Action=(mkWhat (left, right)) }

    and replaceVarsWithNonTerms phrase =
        match phrase with
        | Name v :: rest    ->  Name ("what", NonTerm) :: replaceVarsWithNonTerms rest
        | term :: rest      ->  term :: replaceVarsWithNonTerms rest
        | []                ->  []

    let rec getRules story scene (stmts: Statement list) : ParseRule list =
        match stmts with
        | Story (s, stmts) :: rest      when s = story || story = "*"   -> getRules story scene stmts @ getRules story scene rest  
        | Scenario (s, stmts) :: rest   when s = scene || scene = "*"   -> getRules story scene stmts @ getRules story scene rest
        | Where refinement :: rest                                      -> makeRefinementRule refinement :: getRules story scene rest
        | IncludeStory stry :: rest                                     -> getRules story scene rest
        | other :: rest                                                 -> getRules story scene rest
        | []                                                            -> []


// end module Rules


// ParseEntries are the basic building block for charts. 
// Some differences to the known structure from literature:
//  * before is stored as reversed list
//  * when a ParseEntry is completed (after = []), its before list is also set to [], in order to allow sharing for nonterminals in the SPPF.
//  * the SPPF ptr is always stored as a list: [] for predicted entries, [sppfNode] for single derivations, longer list if there are conflicts

type ParseEntry = { start: int; pos: int; NT: string; 
                    before: Phrase; after: Phrase; 
                    rule: Rules.ParseRule; prio: int; mutable sppfPtr: SPPF list }

and 'T SPPFNode = SPPFPair of 'T * 'T SPPFNode2nd | SPPFNil
and 'T SPPFNode2nd = SPPFTerminal of int | SPPFNonTerm of ('T) 
and SPPF = (ParseEntry ref) SPPFNode


// we don't compare rule or sppf
let matchingEntry l r = l.start = r.start && l.pos = r.pos && l.NT = r.NT && l.before = r.before && l.after = r.after


let matchingSPPF lft rgt = 
    match (lft, rgt) with
    | (SPPFPair (l1, SPPFNonTerm r1), SPPFPair (l2, SPPFNonTerm r2))    -> matchingEntry !l1 !l2 && matchingEntry !r1 !r2
    | (SPPFPair (l1, SPPFTerminal i1), SPPFPair (l2, SPPFTerminal i2))  -> matchingEntry !l1 !l2 && i1 = i2
    | (SPPFNil, SPPFNil)                                                -> true
    | _                                                                 -> false


let listParseEntry e =  e.start.ToString() + " - " + e.pos.ToString() + 
                        "'" + e.NT + "' -> " + (literal (List.rev e.before)) + " . " + (literal e.after)


let rec insertUniqueSPPF (list: SPPF list) (entry: SPPF) : SPPF list = 
    match list with
    | hd :: tl      ->  if matchingSPPF hd entry then hd :: tl else hd :: insertUniqueSPPF tl entry
    | []            ->  [entry]

let rec insertUniqueEntry (list: ParseEntry ref list) (entry: ParseEntry ref) : ParseEntry ref list = 
    match list with
    | hd :: tl      ->  if matchingEntry !hd !entry then hd :: tl else hd :: insertUniqueEntry tl entry
    | []            ->  [entry]


// Aggregate the SPPF in a list of some type. Traverses all branches of the SPPF
let rec foldSPPF (f: 'T list SPPFNode -> 'T list) (sppf: SPPF list) : 'T list =
    match sppf with
    | SPPFPair (fst, SPPFNonTerm snd) :: rest    ->  let left = foldSPPF f (!fst).sppfPtr
                                                     let right = foldSPPF f (!snd).sppfPtr
                                                     in f (SPPFPair (left, SPPFNonTerm right)) @ foldSPPF f rest
    | SPPFPair (fst, SPPFTerminal i) :: rest     ->  let left = foldSPPF f (!fst).sppfPtr
                                                     in f (SPPFPair (left, SPPFTerminal i)) @ foldSPPF f rest
    | _                                          ->  []


let rec appendAll lst elm = List.map (fun ls -> ls @ [elm]) lst

let rec compileParseEntry (inp: array<Term>) (pe: ParseEntry ref) : Expression =
    compileConflict (List.map (compileSPPF inp (!pe).rule.Action []) (!pe).sppfPtr)

     
and compileSPPF inp action args (sppf : SPPF) : Expression =
    match sppf with
    | SPPFPair (left, SPPFNonTerm right)   -> compileSPPF inp (!left).rule.Action ((compileParseEntry inp right) :: args) (uniqueSPPF left)
    | SPPFPair (left, SPPFTerminal i)      -> compileSPPF inp (!left).rule.Action ((compileTerminal (inp.[i])) :: args) (uniqueSPPF left)
    | SPPFNil                              -> action args

and uniqueSPPF pe =
    match (!pe).sppfPtr with
    | [uniq]    -> uniq
    | hd :: tl  -> printfn "%A" tl; hd
    | []        -> SPPFNil

and compileConflict alternatives = 
    match alternatives with
    | [one] -> one
    | _     -> App (Const (Keyword "Conflict"), alternatives)

and compileTerminal term : Expression =
    match term with
    | Name (n,t)    -> Var (n)
    | Literal tok   -> Const (tok)


// Aggregate one path in the SPPF. Uses the pick function to choose between alternates
let rec visitSPPF (pick: SPPF list -> SPPF) (f: (ParseEntry ref) -> SPPF -> 'T SPPFNode -> 'T) pe : 'T =
    if List.isEmpty (!pe).sppfPtr 
    then f pe SPPFNil SPPFNil
    else 
        let node = pick (!pe).sppfPtr in
        match node with
        | SPPFPair (fst, SPPFNonTerm snd)   ->  let left = visitSPPF pick f fst
                                                let right = visitSPPF pick f snd
                                                in f pe node (SPPFPair (left, SPPFNonTerm right))
        | SPPFPair (fst, SPPFTerminal i)    ->  let left = visitSPPF pick f fst
                                                in f pe node (SPPFPair (left, SPPFTerminal i))
        | SPPFNil                           ->  f pe node SPPFNil


// Aggregate function for building Clauses and Expressions.
// First collects the left branch for a list of AnythingTs and then applies the rule's semantic action on it 
let rec compile (inp: array<Term>) (pe: ParseEntry ref) (node: SPPF) (inner: Expression list SPPFNode) : Expression list =
    let args = 
        match inner with
        | SPPFPair (left, SPPFNonTerm right)    ->  left @ right
        | SPPFPair (left, SPPFTerminal i)       ->  match inp.[i] with
                                                    | Literal s         -> left @ [Const (s)]
                                                    | Name (s,Unknown)  -> left @ [Var (s)]
                                                    | Name (s,t)        -> left @ [TypeCast (t, Var (s))]
        | SPPFNil                               ->  []
    in
        if (!pe).after = [] then 
//            printfn "COMPILE %s: %A" (!pe).NT args;
            [(!pe).rule.Action args] else args



// Chart for Early parser. Each ParseEntry is stored in both byStart and byPos. New entries are stored in todos.
type ParseChart = { 
    mutable byStart: array<ParseEntry ref list>; 
    mutable todoByPos: array<ParseEntry ref list>;
    mutable blockedByPos: array<ParseEntry ref list>;
    mutable completedByStart: array<ParseEntry ref list>;
    rules: Rules.ParseRule list; 
    input: array<Term> 
    }

let rec maxPrio sppfList =
    match sppfList with
    | SPPFPair (pe, snd) :: rest    -> max (!pe).prio (maxPrio rest)
    | _                             -> -1

let updatePrio entry =
    match (entry.rule.Prio) with
    | Rules.Prio p          -> {entry with prio=p}
    | Rules.LRPrio (l,r)    -> {entry with prio=l}
    | Rules.NoPrio          -> entry
    | Rules.DerivedPrio i   -> if i = entry.pos then {entry with prio= (maxPrio entry.sppfPtr)} else entry

let predictedEntry (initPos: int) (rule: Rules.ParseRule) = 
    updatePrio {start=initPos; pos=initPos; NT=rule.NT; before=[]; after=rule.Pattern; rule=rule; prio=0; sppfPtr=[]}


let derivedEntry entry newPos sppf = 
    let matched :: newAfter = (!entry).after
    let newBefore = matched :: (!entry).before
    in  updatePrio {!entry with pos= newPos; before= newBefore; after=newAfter; sppfPtr=[SPPFPair (entry, sppf)] }


let ruleInfo entry = let e = !entry in e.start.ToString() + "-" + e.pos.ToString() + " " + e.NT


let rec listDerivations entry = foldSPPF derivationFold (!entry).sppfPtr 
//listDerivationsForList [] (ruleInfo entry) (!entry).sppfPtr

and derivationFold inner =
    match inner with
    | SPPFPair (left, SPPFNonTerm right)   -> (prependAll "Nonterminal" left) @ right
    | SPPFPair (left, SPPFTerminal i)      -> prependAll ("Terminal " + i.ToString()) left

//and listAllDerivations entrylist = 
//    match entrylist with
//    | hd :: tl          -> (listDerivations hd) :: (listAllDerivations tl)
//    | []                -> []

//and listDerivationsForNode (soFar: string list) (rule: string) (sppf: ParseEntry ref SPPFNode) : string list list = 
//    match sppf with
//    | SPPFPair (pe, SPPFTerminal i)        ->    listDerivationsForList soFar (ruleInfo pe) (!pe).sppfPtr @[["Terminal " + i.ToString()]]
//    | SPPFPair (pe, SPPFNonTerm nt)        ->    let left = listDerivationsForList soFar (ruleInfo pe) (!pe).sppfPtr
//                                                 in prependAll ("Combine " + rule) (listDerivationsForList (("NonTerminal " + rule) :: soFar) (ruleInfo nt) (!nt).sppfPtr)
////    | Derivation (pe, nt)   ->  let left = listDerivationsForList soFar (ruleInfo pe) (!pe).sppfPtr
////                                let right = List.fold (fun rs deriv -> rs @ listDerivationsForList deriv "" [nt]) [] left
////                                in prependAll ("Combine " + rule) right

//and listDerivationsForList soFar rule sppfList =
//    match sppfList with
//    | hd :: tl              -> (listDerivationsForNode soFar rule hd) @ (listDerivationsForList soFar rule tl)
//    | []                    -> []

and prependAll (hd: string) (tails: string list list) : string list list =
    match tails with
    | front :: rest         -> (hd :: front) :: (prependAll hd rest)
    | []                    -> []


let initChartParser (rules: Rules.ParseRule list) (rootNonTerm: string) (input: Phrase) = 
    let inp = Seq.toArray input 
    let start = [ref (predictedEntry 0 (Rules.makeStartRule rootNonTerm)) ]
    let cht1 = Array.init (inp.Length + 1) (fun _ -> ([]: ParseEntry ref list))
    let cht2 = Array.init (inp.Length + 1) (fun _ -> ([]: ParseEntry ref list))
    let cht3 = Array.init (inp.Length + 1) (fun _ -> ([]: ParseEntry ref list))
    let cht4 = Array.init (inp.Length + 1) (fun _ -> ([]: ParseEntry ref list))
    in  cht1.[0] <- start;
        cht2.[0] <- start;
        cht4.[0] <- start;
        { byStart=cht1; blockedByPos=cht2; todoByPos=cht4; completedByStart=cht3; rules= rules; input=inp}


let initChart rules input = initChartParser (rules @ Rules.defaultRules) ":clause" input


// Adds a ParseEntry to the chart. 
// If there already exists a matching ParseEntry, merge both entries and keep the old one.
// Otherwise create a new ParseEntry cell and link iot from 'byStart' and 'byPos'
// and put it into todos.
let rec addEntry (pcr: ParseChart ref) (entry: ParseEntry) = 
    let pc = !pcr
    let completed = List.isEmpty entry.after
    let newEntry = { entry with before=[] }
    if mergeEntry pc.byStart.[entry.start] entry 
    then
        if completed then do mergeEntry pc.completedByStart.[newEntry.start] newEntry |> ignore; 
        false
    else 
        let entryCell = ref entry
        pc.byStart.[entry.start] <- entryCell :: pc.byStart.[entry.start]
        pc.todoByPos.[entry.pos] <- entryCell :: pc.todoByPos.[entry.pos]
        if completed then
            if not (mergeEntry pc.completedByStart.[newEntry.start] newEntry) then
                pc.completedByStart.[newEntry.start] <- (ref newEntry) :: pc.completedByStart.[newEntry.start]
        printfn "%d - %d %s @%d -> %A . %A" entry.start entry.pos entry.NT entry.prio (List.rev entry.before) entry.after; 
        true


// Checks if a matching entry is already in the list and if yes, merges sppfPtrs
and mergeEntry (entryList: ParseEntry ref list) (entry: ParseEntry) =
    match entryList with
    | old :: rest   ->  if matchingEntry !old entry 
                        then 
                            match entry.sppfPtr with
                            | hd :: tl     ->  (!old).sppfPtr <- insertUniqueSPPF (!old).sppfPtr hd;
                            | []           ->  ();
                            true
                        else 
                            mergeEntry rest entry
    | []            ->  false


//and findEntry (entryList: ParseEntry ref list) (entry: ParseEntry)  =
//    match entryList with
//    | old :: rest   ->  if matchingEntry !old entry then (old, true)
//                        else findEntry rest entry
//    | []            ->  (ref entry, false)


// Predictor step: if position is at a nonterminal, add ParseEntries for all rules that have the same nonterminal
let predict (pc: ParseChart ref) (entry: ParseEntry) =
    match entry.after with
    | Name (nt, NonTerm) :: _       ->  let mutable changes = false in
                                        for r in (!pc).rules do
                                            if r.NT = nt then 
                                                if addEntry pc (predictedEntry entry.pos r) then
                                                     changes <- true;
                                        changes
    | _                             ->  false


// Completer step: if entry.pos is at a nonterminal and other is a completed ParseEntry for 
// this nonterminal at that position, combine both into a new ParseEntry
let complete (pc:ParseChart ref) (entry: ParseEntry ref) (other: ParseEntry ref) =
    match (!entry).after with
    | Name (nt, NonTerm) :: more       ->   if (!other).NT = nt && (!other).after = [] then
                                                addEntry pc (derivedEntry entry (!other).pos (SPPFNonTerm (other)))
                                            else false
    | _                                ->   false

let completeDBG pc entry other = (complete pc entry other) || ((!other).after <> []) || (printfn "no complete %A %A" !entry !other ; false)

// We have some preterminals which can be matched against Terms, and matching a Name always succeeds as it can be bound.
let literalMatch pat inp =
    match (pat, inp) with
    | (Literal s1, Literal s2)                            ->  s1 = s2
    | (Name ("literal", NonTerm), Literal (Whitespace s)) ->  false
    | (Name ("literal", NonTerm), Literal (Separator "EOF"))  ->  false
    | (Name ("literal", NonTerm), Literal (Word s))       ->  false
    | (Name ("literal", NonTerm), Literal (Keyword s))    ->  false
    | (Name ("literal", NonTerm), Literal s2)             ->  true
    | (Name ("whitesp", NonTerm), Literal (Whitespace s)) ->  true
    | (Name ("string", NonTerm), Literal (String (s,_)))  ->  true
    | (Name ("string", NonTerm), Literal (Text (s,_)))    ->  true
    | (Name ("number", NonTerm), Literal (Number s))      ->  true
    | (Name ("word", NonTerm), Literal (Word s))          ->  true
    | (Name ("name", NonTerm), Name (_,t2))               ->  t2 <> NonTerm               // true, since inputs don't have NTs
    | (Name (s1,t1), Name (s2,_))                         ->  t1 <> NonTerm
    | _                                                   ->  false


let moveBlocked (pc: ParseChart ref) (entry: ParseEntry ref) = 
    let pos = (!entry).pos in 
        (!pc).blockedByPos.[pos] <- insertUniqueEntry (!pc).blockedByPos.[pos] entry

// Scanner step: if the position is at a terminal and the input matches, create a new ParseEntry combining both.
let scan (pc: ParseChart ref) (entry: ParseEntry ref) =
    match (!entry).after with
    | next :: more                  ->  let inp = (!pc).input
                                        in  if literalMatch next (inp.[(!entry).pos]) then
                                                addEntry pc (derivedEntry entry ((!entry).pos+1) (SPPFTerminal (!entry).pos))
                                            else
                                                match next with
                                                | Name (_, NonTerm)     -> moveBlocked pc entry; true
                                                | _                     -> false
    | _                             ->  false


// Early parser: for each input position, predict, scan and complete until no new entries are generated, 
// then go to next input position. 
let runChart (pc: ParseChart ref) =
    for stage in 0 .. (!pc).input.Length-1 do
        printfn ""
        printfn "STAGE %d:" stage
        while (!pc).todoByPos.[stage].Length > 0 do
            let entry :: rest = (!pc).todoByPos.[stage]
            do 
                (!pc).todoByPos.[stage] <- rest
                
                if (!entry).pos < (!pc).input.Length then
                    printfn "CHECK %s" (listParseEntry !entry)
                    printfn "PREDICT..."; 
                    //printfn ".......... %A" 
                    (predict pc !entry)  |> ignore
                    printfn "SCAN......"; 
                    //printfn ".......... %A" 
                    (scan pc entry)     |> ignore
//                if (!entry).after = [] then
//                    let cand = (!pc).byPos.[(!entry).start]
//                    for left in cand do
//                        printfn "... %s" (listParseEntry !left)
//                        (complete pc left entry)  |> ignore

                if List.isEmpty rest then
                    printfn "COMPLETE.."; 
                    let mutable changes = true
                    while changes do
                        changes <- false
                        for i in 0 .. stage do
                            for right in (!pc).completedByStart.[i] do
                                for left in (!pc).blockedByPos.[i] do
                                    if complete pc left right then changes <- true

                    // for start in 0 .. (!pc).byStart.Length - 1 do
                    //     for left in (!pc).byStart.[start] do
                    //         if (!left).pos < (!pc).input.Length then
                    //             for right in (!pc).byStart.[(!left).pos] do
                    //                 complete pc left right  |> ignore


// Conflicts can be resolved by rule priority or typing, otherwise it's an error
let rec getPriority sppf =
    match sppf with
    | SPPFPair (pe, snd) -> match (!pe).rule.Prio with
                            | Rules.Prio i          ->  i
                            | Rules.NoPrio          ->  -1
                            | Rules.LRPrio (l,r)    ->  r
                            | Rules.DerivedPrio nth ->  let i = (!pe).pos - nth in
                                                        if i > 0 then derivePriority pe i
                                                        else -1

and derivePriority pe nth = -1

// If there is more than one derivation, make sure there's only one with highest priority
let rec searchConflicts (pe: ParseEntry ref) : ParseEntry ref list =
    match (!pe).sppfPtr |> List.sortByDescending getPriority with
    | one :: two :: rest when getPriority one = getPriority two
                                    -> pe :: searchConflictsForList ((!pe).sppfPtr)
    | one :: _                      -> searchConflictsForNode (one)
    | []                            -> []

and searchConflictsForNode (nd : (ParseEntry ref) SPPFNode) : ParseEntry ref list =
    match nd with
    | SPPFPair (pe, SPPFTerminal _)  -> searchConflicts pe
    | SPPFPair (pe, SPPFNonTerm snd) -> (searchConflicts pe) @ (searchConflicts snd)
and searchConflictsForList (list: (ParseEntry ref) SPPFNode list) : ParseEntry ref list =
    match list with 
    | hd :: tl              -> (searchConflictsForNode hd) @ (searchConflictsForList tl)
    | []                    -> []

    
let listSPPF (sppf: (ParseEntry ref) SPPFNode) =
    let listSPPFLeft (pe: ParseEntry) = "shift " + (listParseEntry pe) + " over " in
    match sppf with
    | SPPFPair (lft, SPPFTerminal i)        -> (listSPPFLeft !lft) + "terminal at " + i.ToString()
    | SPPFPair (lft, SPPFNonTerm nt)        -> (listSPPFLeft !lft) + "nonterminal " + (!nt).NT


let listConflict (pe: ParseEntry ref) = ((!pe).NT + ": ") :: List.map listSPPF (!pe).sppfPtr

let rec listDerivation (inp: array<Term>) sppf =
    match sppf with
    | SPPFPair (left, SPPFTerminal i)    -> listDerivationOf inp left +  " '" + literal [inp.[i]] + "'"
    | SPPFPair (left, SPPFNonTerm pe)    -> listDerivationOf inp left + listDerivationOf inp pe + "}"
//    | Derivation (pe,s) -> listDerivationOf inp pe +  listDerivation inp s
and listDerivationOf inp pe = 
    match (!pe).sppfPtr with
    | first :: _    ->  listDerivation inp (first)
    | []            ->  "{" + (!pe).NT + ":"
