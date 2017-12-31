module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Add  = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)
primOpType Sub  = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)
primOpType Mul  = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)
primOpType Quot = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'
--------------------------------------------------------------------- unquantify ----------------------------------------------------------------
unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)
--------------------------------------------------------------------- unify ----------------------------------------------------------------
unify :: Type -> Type -> TC Subst

unify (Base Int) (Base Int) = return emptySubst

unify (Base Bool) (Base Bool) = return emptySubst

unify (Base Unit) (Base Unit) = return emptySubst

unify (TypeVar x) (TypeVar y) 
    | x == y = return emptySubst
    | otherwise = return $ x=:(TypeVar y)

unify (TypeVar x) t
    | not (x `elem` tv t) = return $ x=:t
    | otherwise = error ("can't unify var " ++ x)
unify t1 t2@(TypeVar x) = unify t2 t1

unify (Arrow t1 t2) (Arrow t1' t2') = do
    subst1 <- unify t1 t1'
    subst2 <- unify (substitute subst1 t2) (substitute subst1 t2')
    let subst3 = subst1 `mappend` subst2
    return subst3

unify (Sum t1 t2) (Sum t1' t2') = do
    subst1 <- unify t1 t1'
    subst2 <- unify (substitute subst1 t2) (substitute subst1 t2')
    let subst3 = subst1 `mappend` subst2
    return subst3

unify (Prod t1 t2) (Prod t1' t2') = do
    subst1 <- unify t1 t1'
    subst2 <- unify (substitute subst1 t2) (substitute subst1 t2')
    let subst3 = subst1 `mappend` subst2
    return subst3

unify t1 t2 = error ("can't unify types " ++ pprT t1 ++ " and " ++pprT t2)

--------------------------------------------------------------------- pprT ----------------------------------------------------------------
pprT :: Type -> String 
pprT (Base Int) = "Int" 
pprT (Base Bool) = "Bool" 
pprT (TypeVar x) = x 
pprT (Arrow t1 t2)  
  = "(" ++ pprT t1 ++ " -> " ++ pprT t2 ++ ")" 
pprT (Sum t1 t2)  
 = "(" ++ pprT t1 ++ " + " ++ pprT t2 ++")" 
pprT (Prod t1 t2)  
  = "(" ++ pprT t1 ++ " * " ++ pprT t2  ++ ")" 

--------------------------------------------------------------------- generalise ----------------------------------------------------------------
generalise :: Gamma -> Type -> QType
generalise g t = res
    where
        freeVars = filter (\x -> not $ x `elem` tvGamma g) (tv t)
        helper :: [String] -> Type -> QType
        helper [] t = Ty t
        helper (v:vs) t = Forall v (helper vs t) 
        res = helper freeVars t

--------------------------------------------------------------------- inferProgram ----------------------------------------------------------------
inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env [Bind name _ [] exp] = do
    (newExp, t, subst) <- inferExp env exp
    let qt = generalise env t
    let newExp' = allTypes (substQType subst) newExp
    return ([Bind name (Just qt) [] newExp'], t, subst)

----------------------------------------------------------------- Constants and Variables ----------------------------------------------------------
inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp g exp@(Num _) = do
    return (exp, Base Int, emptySubst)

inferExp g exp@(Var v_name) = do
    case E.lookup g v_name of
        Just qt -> do
            t <- unquantify qt
            return (exp, t, emptySubst)
        Nothing -> typeError $ NoSuchVariable v_name

------------------------------------------------------------- Primops and Constructors -------------------------------------------------------------
inferExp g exp@(Prim op) = do
    let qt = primOpType op
    t <- unquantify qt
    return (exp, t, emptySubst)   

inferExp g exp@(Con c) = do
    let Just qt = constType c
    t <- unquantify qt
    return (exp, t, emptySubst)

--------------------------------------------------------------------- Application ----------------------------------------------------------------
inferExp g (App e1 e2) = do
    (e1', t1, subst1) <- inferExp g e1

    let subst1_g = substGamma subst1 g
    (e2', t2, subst2) <- inferExp subst1_g e2

    let t1' = substitute subst2 t1
    alpha <- fresh
    u <- unify t1' (Arrow t2 alpha)

    let final_subst = u `mappend` subst1 `mappend` subst2
    let t = substitute u alpha

    let newExp = App e1' e2'

    return (newExp, t, final_subst)
 

--------------------------------------------------------------------- If-Then-Else ----------------------------------------------------------------
inferExp g exp@(If e e1 e2) = do
    (e', t, substT) <- inferExp g e
    u <- unify t (Base Bool)

    let u_substT_g = substGamma u $ substGamma substT g
    (e1', t1, substT1) <- inferExp u_substT_g e1

    let substT1_u_substT_g = substGamma substT1 $ substGamma u $ substGamma substT g
    (e2', t2, substT2) <- inferExp substT1_u_substT_g e2

    u' <- unify (substitute substT2 t1) t2

    let final_subst = u' `mappend` substT2 `mappend` substT1 `mappend` u `mappend` substT
    let res_t = substitute u' t2

    let newExp = (If e' e1' e2')

    return (newExp, res_t, final_subst)

--------------------------------------------------------------------- Case ----------------------------------------------------------------
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do
    (e', t, substT) <- inferExp g e

    alphaL <- fresh
    let gL = E.add g (x, Ty alphaL)
    let substT_gL = substGamma substT gL

    (e1', tL, substT1) <- inferExp substT_gL e1

    alphaR <- fresh
    let gR = E.add g (y, Ty alphaR)
    let substT1_substT_gR = substGamma substT1 $ substGamma substT gR

    (e2', tR, substT2) <- inferExp substT1_substT_gR e2

    let substT2_substT1_substT = substT2 `mappend` substT1 `mappend` substT
    let substT2_substT1 = substT2 `mappend` substT1

    u <- unify (substitute substT2_substT1_substT (Sum alphaL alphaR)) (substitute substT2_substT1 t)

    let u_substT2 = u `mappend` substT2

    u' <- unify (substitute u_substT2 tL) (substitute u tR)

    let final_subst = u' `mappend` u `mappend` substT2 `mappend` substT1 `mappend` substT
    let newExp = (Case e' [Alt "Inl" [x] e1', Alt "Inr" [y] e2'])
    let res_t = substitute (u' `mappend` u) tR

    return (newExp, res_t, final_subst)

inferExp g (Case e _) = typeError MalformedAlternatives



--------------------------------------------------------------------- Recursive Functions ----------------------------------------------------------
inferExp g exp@(Letfun (Bind f_name _ params f_body)) = do
    names_and_types <- freshes (params ++ [f_name])
    let names_and_Qtypes = addQ names_and_types

    let g' = E.addAll g names_and_Qtypes
    (f_body', t, subst) <- inferExp g' f_body

    let types = extractType names_and_types
    let left  = last types
    let right = nestedArrows (take ((length types) - 1) types) t

    u <- unify (substitute subst left) (substitute subst right)

    let final_subst = u `mappend` subst
    let res_t = substitute final_subst right
    let newExp = Letfun (Bind f_name (Just $ Ty res_t) params f_body')

    return (newExp, res_t, final_subst)

--------------------------------------------------------------------- Let Bindings ----------------------------------------------------------------
inferExp g (Let bindings e2) = do
    all_exp_type_subst <- multiInfer g bindings
    let all_subst = combineSubst all_exp_type_subst

    let substT_g = substGamma all_subst g
    let g' = E.addAll substT_g (multiGeneralise substT_g all_exp_type_subst)

    (e2', t', substT') <- inferExp g' e2

    let final_subst = substT' `mappend` all_subst
    let newExp = Let (newBindings g' all_exp_type_subst) e2'
 

    return (newExp, t', final_subst)

--------------------------------------------------------------------- Recursive Bindings ----------------------------------------------------------------
inferExp g (Letrec bindings e) = do    
    g' <- unifyAll g bindings
    (e', t', subst) <- inferExp g' e
    let newExp = Letrec (newRecBindings g' bindings) e
    return (newExp, t', subst)

inferExp g _ = error "Implement me!"




---------------------------------------------------------------- Helper Functions ----------------------------------------------------------------
freshes :: [Id] -> TC [(Id, Type)]
freshes [] = do 
    return []
freshes (i:is) = do
    t <- fresh
    fnames <- freshes is
    return ((i, t) : fnames)

addQ :: [(Id, Type)] -> [(Id, QType)]
addQ [] = []
addQ (tv@(x, t):tvs) = (x, Ty t) : addQ tvs

extractType :: [(Id, Type)] -> [Type]
extractType [] = []
extractType (tv:tvs) = (snd tv) : extractType tvs

nestedArrows :: [Type] -> Type -> Type
nestedArrows [tv] t = Arrow tv t
nestedArrows (tv:tvs) t = Arrow tv $ nestedArrows tvs t

multiInfer :: Gamma -> [Bind] -> TC [(Id, Exp, Type, Subst)]
multiInfer g [] = do
    return []
multiInfer g (b@(Bind v_name _ [] e):bs) = do
    (e', t, subst) <- inferExp g e
    others <- multiInfer g bs
    return ((v_name, e', t, subst) : others)

combineSubst :: [(Id, Exp, Type, Subst)] -> Subst
combineSubst [] = emptySubst
combineSubst (b@(_, _, _, subst):bs) = subst `mappend` combineSubst bs

multiGeneralise :: Gamma -> [(Id, Exp, Type, Subst)] -> [(Id, QType)]
multiGeneralise substT_g [] = []
multiGeneralise substT_g (b@(i, _, t, _):bs) = [(i, (generalise substT_g t))] ++ (multiGeneralise substT_g bs)

newBindings :: Gamma -> [(Id, Exp, Type, Subst)] -> [Bind]
newBindings g [] = []
newBindings g (b@(i, e, t, s):bs) = [Bind i (E.lookup g i) [] e] ++ (newBindings g bs)


unifyAll :: Gamma -> [Bind] -> TC Gamma
unifyAll g [Bind v_name _ [] e] = do
    (e', t, subst) <- inferExp g e
    let g' = E.add g (v_name, Ty t)
    return g'
unifyAll g (b@(Bind v_name _ [] e):bs) = do
    g' <- unifyAll g bs
    (e', t, subst) <- inferExp g' e
    let g'' = E.add g' (v_name, Ty t)
    return g''

newRecBindings :: Gamma -> [Bind] -> [Bind]
newRecBindings g [] = []
newRecBindings g (b@(Bind v_name _ [] e):bs) = [Bind v_name (E.lookup g v_name) [] e] ++ (newRecBindings g bs)









