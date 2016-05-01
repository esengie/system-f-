module SystemF_omega where

import Prelude hiding (succ)
import Control.Applicative
import Control.Monad

-- Rewrite using MonadError?
type ErrOr a = Either String a

right :: a -> ErrOr a
right = Right

err :: String-> ErrOr a
err = Left

get :: ErrOr a -> a
get (Right x) = x
get (Left e)  = error e

-------------------- data types -------------------------------------

data Primitive 
    = Number Integer
    | Boolean Bool
    | Succ 
    deriving (Show, Eq)

infixl 2 :@

data Term
    = Prim Primitive
    | Abs Type (Term -> Term)
    | Term :@ Term
    | TAbs Kind (Type -> Term)
    | TApp Term Type
    | Var Char

infixr 3 :->

data Type 
    = NumType
    | BoolType
    | Type :-> Type
    | UnivTy Kind (Type -> Type)
    | OpAbs Kind (Type -> Type)
    | OpApp Type Type
    | TyVar Char

infixr 3 :=>

data Kind
    = Star
    | Kind :=> Kind

instance Eq Kind where
    Star == Star = True
    (dom :=> rng) == (dom' :=> rng') = dom == dom' && rng == rng'
    _ == _ = False

instance Eq Type where
    a == b = eqType ['A'..'z'] (nf a) (nf b)

nf :: Type -> Type
nf (a :-> b) = nf a :-> nf b
nf (UnivTy k f)   = UnivTy k (nf . f)
nf (OpAbs k f)   = OpAbs k (nf . f)
nf (OpApp f a) = case nf f of { UnivTy k g -> g; OpAbs k g -> g; g -> OpApp g } $ nf a
nf x         = x

eqType :: String -> Type -> Type -> Bool
eqType _ NumType NumType = True
eqType _ BoolType BoolType = True
eqType cs (dom :-> rng) (dom' :-> rng') = eqType cs dom dom' && eqType cs rng rng'
eqType (c:cs) (UnivTy k f) (UnivTy k' f') = k == k' && eqType cs (f (TyVar c)) (f' (TyVar c))
eqType (c:cs) (OpAbs k f) (OpAbs k' f') = k == k' && eqType cs (f (TyVar c)) (f' (TyVar c))
eqType (c:cs) (OpApp t1 t2) (OpApp t1' t2') = eqType cs t1 t1' && eqType cs t2 t2'
eqType [] _ _ = error "You've used up all of the characters."
eqType _ (TyVar c) (TyVar c') = c == c'
eqType _ _ _ = False 

instance Show Kind where
    show Star = "*"
    show (dom :=> rng) = "(" ++ show dom ++ " -> " ++ show rng ++ ")"

instance Show Type where
    show a = showType ("XYZVW" ++ ['A' .. 'U']) a

showType :: String -> Type -> String
showType _ NumType = "Numeric"
showType _ BoolType = "Bool"
showType cs (dom :-> rng) = "(" ++ showType cs dom ++ " -> " ++ showType cs rng ++ ")"
showType (c:cs) (UnivTy k f) = "(∀ " ++ [c] ++ ":" ++ show k ++ "." ++ showType cs (f (TyVar c)) ++ ")"
showType (c:cs) (OpAbs k f) = "(λ" ++ [c] ++ ":" ++ show k ++ "." ++ showType cs (f (TyVar c)) ++ ")"
showType cs (OpApp l r) = "(" ++ showType cs l ++ " " ++ showType cs r ++ ")"
showType [] _  = error "You've used up all of the characters."
showType _ (TyVar t) = [t]


instance Show Term where
  show t = let v = get $ eval t
               ty = typeOf t
           in show v ++ " : " ++ show ty

-------------------------- evaluation -------------------------------

eval' :: Term -> Term
eval' (Prim p)   = Prim p
eval' (Abs t f)  = Abs t f
eval' (TAbs k f)   = TAbs k f
eval' (f :@ x)  = eval' res
    where f' = eval' f
          res = runApp f' (eval' x)
eval' (TApp f x) = eval' res
    where f' = eval' f
          res = (runTApp f') x
  

eval :: Term -> ErrOr Primitive
eval t = valueOf $ eval' t

-------------------------------------------------------------------

valueOf :: Term -> ErrOr Primitive
valueOf (Prim n) = right n
valueOf _ = err "Not a primitive"

runApp :: Term -> (Term -> Term)
runApp (Abs t f) = f
runApp (Prim p) = runAppPrim p

runAppPrim :: Primitive -> (Term -> Term)
runAppPrim Succ = \(Prim (Number n)) -> num (n + 1)

runTApp :: Term -> (Type -> Term)
runTApp (TAbs k f) = f

------------------------ checking -------------------------------------

checkKind :: Type -> Kind -> ErrOr ()
checkKind t ki = do 
    k <- kindOf t
    if k == ki 
        then right ()
        else err $ "Kind of term abstraction type must be *, not " ++ show t

typeOf :: Term -> ErrOr Type
typeOf (Prim p)  = right $ primType p
typeOf (Abs t f) = do
    checkKind t Star
    (:->) t <$> typeOf (f (genType t))
typeOf (TAbs k f)  = right $ UnivTy k (\x -> get $ typeOf (f x)) -- potential error
typeOf (f :@ x) = do  
    fTy <- typeOf f
    (:->) dom rng <- matchFun fTy
    t   <- typeOf x
    if (t == dom)
        then right rng
        else err $ "Function domain does not match App input, expected " ++ show dom ++ " but got: " ++ show t
            where matchFun x@(dom :-> rng) = right x
                  matchFun x = err $ "Not a FunType in app " ++ show x
typeOf (TApp t ty) = do
    vTy <- typeOf t
    UnivTy k f' <- matchUni vTy
    checkKind ty k
    right (f' ty)
        where matchUni x@(UnivTy dom rng) = right x
              matchUni x = err $ "Not a UnivType in TApp " ++ show x

typeOf (Var c) = right $ TyVar c

kindOf :: Type -> ErrOr Kind
kindOf NumType = right Star
kindOf BoolType = right Star
kindOf (a :-> b) = do
    checkKind a Star
    checkKind b Star
    right Star
kindOf (TyVar _) = right Star
kindOf (UnivTy k t) = do
    checkKind (t (genKind k)) Star
    right Star
kindOf (OpAbs k fun) = (:=>) k <$> kindOf (fun (genKind k))
kindOf (OpApp f x) = do
    funKi <- kindOf f
    dom :=> rng <- matchFun funKi
    k     <- kindOf x
    if (k == dom)
        then right rng
        else err $ "Type function domain does not match OpApp input, expected: " 
                    ++ show dom ++ " but got: " ++ show k
            where matchFun x@(dom :=> rng) = right x
                  matchFun x = err $ "Not a FunKind " ++ show x

genKind :: Kind -> Type
genKind Star = NumType
genKind (dom :=> rng) = OpAbs dom (\_ -> genKind rng)


primType :: Primitive -> Type
primType Number{} = NumType
primType Boolean{} = BoolType
primType Succ  = NumType :-> NumType


genType :: Type -> Term
genType (NumType) = num 0
genType (BoolType) = bool False
genType (dom :-> rng) = lam dom (\_ -> genType rng)
genType (UnivTy k f) = TAbs k (\x -> genType (f x))
genType (TyVar c) = Var c

----------------- language primitives -------------------------------

bool = Prim . Boolean
num = Prim . Number
succ = Prim Succ

tlam = TAbs Star
tlam2 = TAbs (Star :=> Star)
lam = Abs

tapp = TApp

univTy = UnivTy Star
opAbs = OpAbs Star

-------------------- basic library functions-------------------------

id' = tlam (\t -> lam t (\x -> x))
const' = tlam (\t1 -> tlam (\t2 -> lam t1 (\x -> lam t2 (\_ -> x))))
succ' = lam NumType (\x -> succ :@ x)

-- λX:* λf:X→X. λy:X. f(f(y))
double = tlam (\t -> lam (t :-> t) (\f -> lam t (\y -> f :@ (f :@ y))))
quadruple = tlam (\t -> tapp double (t :-> t) :@ tapp double t)

doubleNat = tapp quadruple NumType

self = lam (univTy $ \t -> t :-> t) (\x -> tapp x (univTy $ \t -> t :-> t) :@ x)

--pair = λX. λY. λx:X. λy:Y.λR. λp:X→Y→R. p x y,
pair = tlam (\xt -> tlam (\yt -> lam xt (\x -> lam yt (\y -> tlam (\rt -> lam (xt :-> yt :-> rt) (\p -> p :@ x :@ y))))))


tyPair = univTy (\xt -> univTy (\yt -> xt :->  yt :-> pairApp xt yt))

pairType = opAbs (\x -> opAbs (\y -> univTy (\r -> (x :-> y :-> r) :-> r)))
pairApp x y = OpApp (OpApp pairType x) y


