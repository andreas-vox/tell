module tell.Constants

open tell.Expressions
open tell.AST

// Type functor constants
let unionT = Const ("|")
let intersectT = Const ("&")
let tupleT = Const ("*")

let funT = Const ("->")

// Type constants
let anyT = App (intersectT, [])
let neverT = App (unionT, [])

let boolT = Const ("bool")
let stringT = Const ("string")
let numberT = Const ("number")

let typeName s = Typed (Var (s))

let funType (d: TypeExpr) (r: TypeExpr) : TypeExpr = App (funT, [d; r])
let prodType (a: TypeExpr) (b: TypeExpr) : TypeExpr = App (tupleT, [a; b])

let tupleType (ts: TypeExpr list) : TypeExpr = App (tupleT, ts)

(*let rec tupleT ts =
    match ts with
    | [u]       -> u
    | []        -> anyT
    | l :: rest -> prodType l (tupleT rest)
*)

// Expression functions

let andE = Const (Keyword "and:")//, Typed (funType boolT (funType boolT boolT)) )
let orE = Const (Keyword "or:")//, Typed (funType boolT (funType boolT boolT)) )
let notE = Const (Keyword "not:")//, Typed (funType boolT boolT) )

let tupleGenE = Const (Keyword ",")
let equalsGenE = Const (Keyword "=")
let becomesGenE = Const (Keyword ":=")

let tupleE ts = Const(Keyword ",")//, Typed (tupleType ts) )

let equalsE t = Const (Keyword "=")//, Typed (prodType t t))
let becomesE l r = Const (Keyword ":=")//, Typed (prodType l r) )

let rec lookup env expr =
    match env with
    | (e,t) :: rest     ->  if e = expr then (env, t) else 
                            let (env2, t2) = lookup rest expr 
                            in ((e,t)::env2, t2)
    | []                ->  (env, Unknown)