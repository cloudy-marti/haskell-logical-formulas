module Data.Logic.Combinator (
-- * Type
-- * Utils
  multOr
, multAnd
, allOf
, noneOf
, atLeast
, atLeastOne
, atMost
, atMostOne
-- , exactly
-- , exactlyOne
, getSubListOfSize
) where
    import qualified Data.Logic.Var as Var
    import qualified Data.Logic.Fml as Fml
    import Data.List ( nub, permutations, sort )
    import Data.Maybe ( fromJust )

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
    getSubListOfSize :: Ord a => Int -> [Var.Var a] -> [[Var.Var a]]
    getSubListOfSize n lst  = nub . map sort $ concatMap permutations $ getSubListOfSize' lst []
      where
        getSubListOfSize' [] l = [l | length l == n]
        getSubListOfSize' (x:xs) l
          | length l == n   = [l]
          | otherwise       = getSubListOfSize' xs (x:l)
                              ++ getSubListOfSize' xs l

    -- |’atLeast’ @vs@ @k@ returns a formula that is satisfied iff at least @k@
    -- variables in @vs@ are true. The function returns @Nothing@ if @vs@ is the
    -- empty list or @k@ is non-positive or @k@ is larger than the number of
    -- variables in @vs@.
    atLeast :: Ord a => [Var.Var a] -> Int -> Maybe (Fml.Fml a)
    atLeast [] _                  = Nothing
    atLeast lst k
      | k <= 0 || k > length lst  = Nothing
      | k == 1                    = multOr $ map Fml.Final lst
      | otherwise                 = multOr $ map ((fromJust . multAnd) . map Fml.Final) (getSubListOfSize k lst)

    -- |’atLeastOne’ @vs@ returns a formula that is satisfiable iff at least one
    -- variable in @vs@ is true. The function returns @Nothing@ if @vs@ is the
    -- empty list.
    atLeastOne :: Ord a => [Var.Var a] -> Maybe (Fml.Fml a)
    atLeastOne lst = atLeast lst 1

    -- |’atMost’ @vs@ @k@ returns a formula that is satisfiable iff at most @k@
    -- variables in @vs@ are true. The function returns @Nothing@ if @vs@ is the
    -- empty list or @k@ is non-positive or @k@ is larger than the number of
    -- variables in @vs@.
    atMost :: Ord a => [Var.Var a] -> Int -> Maybe (Fml.Fml a)
    atMost [] _                   = Nothing
    atMost lst k
      | k <= 0 || k > length lst  = Nothing
      | k == length lst           = multOr $ map (Fml.Not . Fml.Final) lst
      | otherwise                 = multOr $ map ((fromJust . multAnd) . map not) (getSubListOfSize (l-k) lst)
          where
            l = length lst
            not = Fml.Not . Fml.Final

    -- |’atMostOne’ @vs@ returns a formula that is satisfiable iff at most one
    -- variable in @vs@ is true. The function returns @Nothing@ if @vs@ is the
    -- empty list.
    atMostOne :: Ord a => [Var.Var a] -> Maybe (Fml.Fml a)
    atMostOne lst = atMost lst 1

    -- |’exactly’ @vs@ @k@ returns a formula that is satisfiable iff exactly @k@
    -- variables in @vs@ are true. The function returns @Nothing@ if @vs@ is the
    -- empty list or @k@ is non-positive or @k@ is larger than the number of
    -- variables in @vs@.
    -- exactly :: [Var.Var a] -> Int -> Maybe (Fml.Fml a)

    -- |’exactlyOne’ @vs@ returns a formula that is satisfiable iff exactly one
    -- variable in @vs@ is true. The function returns @Nothing@ if @vs@ is the
    -- empty list.
    -- exactlyOne :: [Var.Var a] -> Maybe (Fml.Fml a)
