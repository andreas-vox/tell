module tell.Expressions


type Expr<'T,'K>    = Const of 'T
                    | Var of string 
                    | TypeCast of ('K * Expr<'T, 'K>)
                    | Tuple of Expr<'T,'K> list
                    | Lambda of (string list * Expr<'T,'K>)
                    | App of (Expr<'T,'K> * Expr<'T,'K> list)
                    | Let of ( (string * Expr<'T,'K>) list * Expr<'T,'K>)

type Env<'T,'K>     = (string * Expr<'T,'K>) list


let rec occurs s expr =
    match expr with
    | Var s2            ->  s = s2
    | Tuple es          ->  occursAny s es
    | App (f,es)        ->  (occurs s f) || occursAny s es
    | Lambda (vs, e)    ->  if List.contains s vs then false 
                            else occurs s e
    | TypeCast (_, e)   ->  occurs s e
    | Let (bs, e)       ->  if List.contains s (List.map fst bs) then false
                            else occursAny s (e :: (List.map snd bs))
    | _                 ->  false

and occursAny s es = List.fold (||) false (List.map (occurs s) es) 

let rec substitute v term expr =
    match expr with
    | Var s             ->  if s = v then term else expr
    | Tuple es          ->  Tuple (List.map (substitute v term) es)
    | App (f,es)        ->  App ((substitute v term f), (List.map (substitute v term) es))
    | Lambda (vs, e)    ->  if List.contains v vs then Lambda (vs, e) 
                            else Lambda (vs, substitute v term e)
    | TypeCast (k, e)   ->  TypeCast (k, substitute v term e)
    | Let (bs, e)       ->  if List.contains v (List.map fst bs) then Let (bs,e)
                            else Let (substBindings v term bs, substitute v term e)
    | other             ->  other

and substBindings v term bs =
    match bs with 
    | (s,e) :: rest     -> (s, substitute v term e) :: substBindings v term rest
    | _                 -> []

let rec FVintern e =
    match e with
    | Const _           ->  []
    | Var s             ->  [s]
    | Tuple es          ->  List.collect FVintern es
    | App (f,es)        ->  (FVintern f) @ (List.collect FVintern es)
    | Lambda (vs, e)    ->  let vars = FVintern e in removeVars vs vars
    | TypeCast (_, e)   ->  FVintern e
    | Let (bs, e)       ->  let vars = (FVintern e) @ (List.collect FVintern (List.map snd bs))
                            in removeVars (List.map fst bs) vars

and removeVars togo vars =
    match togo with
    | v :: rest     -> removeVars rest (removeVar v vars)
    | []            -> vars

and removeVar togo vars =
    match vars with
    | v :: rest     ->  if v = togo then removeVar togo vars
                        else v :: (removeVar togo vars)
    | []            ->  vars

and uniqueVars vars =
    match vars with
    | v :: rest     ->  v :: (uniqueVars (removeVar v rest))
    | []            ->  []

let FV e = uniqueVars (FVintern e)

let rec unifyAll (subst: (string * Expr<'T,'K>) list) (pairs: (Expr<'T,'K> * Expr<'T,'K>) list) =
    match pairs with
    | []                                        ->  Some subst
    | (t1, t2) :: more when t1 = t2             ->  unifyAll subst more 
    | (Const t1, Const t2) :: more              ->  None 
    | (App (e1,args1), App (e2,args2)) :: more  ->  (* broken *) unifyAll subst more
    | (Tuple e1, Tuple e2) :: more              ->  (* broken *) unifyAll subst more
    | (term, Var s) :: more                
    | (Var s, term) :: more                     ->  if occurs s term then None
                                                    else let subst2 = substituteSubst s term subst
                                                         let pairs2 = substitutePairs s term more
                                                         in unifyAll subst2 pairs2
    | (TypeCast (k1, e1), TypeCast (k2,e2))::m  ->  if k1 <> k2 then None
                                                    else (* broken *) None  
    | (Lambda (args1,b1), Lambda (args2,b2))::m ->  None
    | (_,_) :: more                             ->  None

and substitutePairs v term pairs =
    List.map (fun (e1, e2) -> (substitute v term e1, substitute v term e2)) pairs

and substituteSubst v term subst =
    List.map (fun (s,e) -> (s, substitute v term e)) subst


let xunify e1 e2 = unifyAll [] [(e1,e2)]



