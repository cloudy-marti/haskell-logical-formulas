module Data.Logic.Combinator (
-- * Type
-- * Utils
  multOr
, multAnd
-- , allOf
-- , noneOf
-- , atLeast
-- , atLeastOne
-- , atMost
-- , atMostOne
-- , exactly
-- , exactlyOne
) where
    import qualified Data.Logic.Var as Var
    import qualified Data.Logic.Fml as Fml
    import Data.List

    -- |’multOr’ @fs@ returns the disjunction of the formulas in @fs.
    -- It returns @Nothing@ if @fs@ is the empty list.
    --
    -- >>> Combinator.multOr []
    -- Nothing
    -- >>> multOr [Fml.Final (Var.mk i) | i <- [1..4]]
    -- Just (Or (Final 1) (Or (Final 2) (Or (Final 3) (Final 4))))
    multOr :: [Fml.Fml a] -> Maybe (Fml.Fml a)
    multOr []       = Nothing
    multOr [p]      = Just p
    multOr (p:qs)   = Just $ foldr Fml.Or p qs

    -- |’multAnd’ @fs@ returns the conjunction of the formulas in @fs.
    -- It returns @Nothing@ if @fs@ is the empty list.
    --
    -- >>> Combinator.multAnd []
    -- Nothing
    -- multAnd [Fml.Final (Var.mk i) | i <- [1..4]]
    -- Just (And (Final 1) (And (Final 2) (And (Final 3) (Final 4))))
    multAnd :: [Fml.Fml a] -> Maybe (Fml.Fml a)
    multAnd []      = Nothing
    multAnd [p]     = Just p
    multAnd (p:qs)  = Just $ foldr Fml.And p qs

    -- |’allOf’ @vs@ returns a formula that is satisfiable iff all variables
    -- in @vs@ are true. The function returns @Nothing@ if @vs@ is the empty list.
    allOf :: [Var.Var a] -> Maybe (Fml.Fml a)
    allOf []        = Nothing
    allOf [p]       = Just $ Fml.Final p
    allOf (p:qs)    = Just $ foldr Fml.And (Fml.Final p) (allOf qs)

    -- |’noneOf’ @vs@ returns a formula that is satisfiable iff no variable
    -- in @vs@ is true. The function returns @Nothing@ if @vs@ is the empty list.
    noneOf :: [Var.Var a] -> Maybe (Fml.Fml a)
    noneOf []       = Nothing 
    noneOf [p]      = Just $ Fml.Not $ Fml.Final p
    noneOf (p:qs)   = Just $ foldr Fml.And (Fml.Not $ Fml.Final p) (noneOf qs)

    -- |’getSubListOfSize’ @n@ @lst@ returns a list of sublists of size n where each
    -- sublist is different (like finding the permutations of size n of a list).
    getSubListOfSize n lst = nub . map sort $ concatMap permutations $ getSubListOfSize' lst []
      where
        getSubListOfSize' [] l = [l | length l == n]
        getSubListOfSize' (x:xs) l
          | length l == n = [l]
          | otherwise     = getSubListOfSize' xs (x:l)
                            ++ getSubListOfSize' xs l

    -- |’atLeast’ @vs@ @k@ returns a formula that is satisfied iff at least @k@
    -- variables in @vs@ are true. The function returns @Nothing@ if @vs@ is the
    -- empty list or @k@ is non-positive or @k@ is larger than the number of
    -- variables in @vs@.
    -- atLeast :: [Var.Var a] -> Int -> Maybe (Fml.Fml a)

    -- |’atLeastOne’ @vs@ returns a formula that is satisfiable iff at least one
    -- variable in @vs@ is true. The function returns @Nothing@ if @vs@ is the
    -- empty list.
    -- atLeastOne :: [Var.Var a] -> Maybe (Fml.Fml a)

    -- |’atMost’ @vs@ @k@ returns a formula that is satisfiable iff at most @k@
    -- variables in @vs@ are true. The function returns @Nothing@ if @vs@ is the
    -- empty list or @k@ is non-positive or @k@ is larger than the number of
    -- variables in @vs@.
    -- atMost :: [Var.Var a] -> Int -> Maybe (Fml.Fml a)

    -- |’atMostOne’ @vs@ returns a formula that is satisfiable iff at most one
    -- variable in @vs@ is true. The function returns @Nothing@ if @vs@ is the
    -- empty list.
    -- atMostOne :: [Var.Var a] -> Maybe (Fml.Fml a)

    -- |’exactly’ @vs@ @k@ returns a formula that is satisfiable iff exactly @k@
    -- variables in @vs@ are true. The function returns @Nothing@ if @vs@ is the
    -- empty list or @k@ is non-positive or @k@ is larger than the number of
    -- variables in @vs@.
    -- exactly :: [Var.Var a] -> Int -> Maybe (Fml.Fml a)

    -- |’exactlyOne’ @vs@ returns a formula that is satisfiable iff exactly one
    -- variable in @vs@ is true. The function returns @Nothing@ if @vs@ is the
    -- empty list.
    -- exactlyOne :: [Var.Var a] -> Maybe (Fml.Fml a)
