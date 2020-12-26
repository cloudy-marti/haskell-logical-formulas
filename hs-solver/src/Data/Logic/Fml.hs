module Data.Logic.Fml (
-- * Type
Fml (..)
-- * Querying
, depth
, vars
-- * Formatting
, prettyFormat
-- * Transforming
, toNNF
, toCNF
-- , toCCNF
, toDNF
, toUniversalNAnd
-- * Testing
, isNNF
, isCNF
-- , isCCNF
, isDNF
) where
  import qualified Data.Logic.Var as Var
  import qualified Data.List      as L
  
  data Fml a = 
      And   (Fml a) (Fml a)
    | NAnd  (Fml a) (Fml a)
    | Or    (Fml a) (Fml a)
    | NOr   (Fml a) (Fml a)
    | XOr   (Fml a) (Fml a)
    | XNOr  (Fml a) (Fml a)
    | Imply (Fml a) (Fml a)
    | Equiv (Fml a) (Fml a)
    | Not   (Fml a)
    | Final (Var.Var a)
    deriving (Eq, Show)

  -- |’prettyFormat’ @p@ return a sting representation of the formula @p@.
  -- and : .
  -- nand: ~.
  -- or: +
  -- nor: ~+
  -- xor: x+
  -- xnor: x~+
  -- imply: =>
  -- equivalence: <=>
  -- not: -
  prettyFormat :: (Show a) => Fml a -> String
  prettyFormat (And p q)   = "(" ++ prettyFormat p ++ " . " ++ prettyFormat q ++ ")"
  prettyFormat (NAnd p q)  = "(" ++ prettyFormat p ++ " ~. " ++ prettyFormat q ++ ")"
  prettyFormat (Or p q)    = "(" ++ prettyFormat p ++ " + " ++ prettyFormat q ++ ")"
  prettyFormat (NOr p q)   = "(" ++ prettyFormat p ++ " ~+ " ++ prettyFormat q ++ ")"
  prettyFormat (XOr p q)   = "(" ++ prettyFormat p ++ " x+ " ++ prettyFormat q ++ ")"
  prettyFormat (XNOr p q)  = "(" ++ prettyFormat p ++ " x~+ " ++ prettyFormat q ++ ")"
  prettyFormat (Imply p q) = "(" ++ prettyFormat p ++ " => " ++ prettyFormat q ++ ")"
  prettyFormat (Equiv p q) = "(" ++ prettyFormat p ++ " <=> " ++ prettyFormat q ++ ")"
  prettyFormat (Not p)     = "-" ++ prettyFormat p
  prettyFormat (Final v)   = show v

  -- |’getFmls’ @p@ returns formula into a list of formula @p@.
  getFmls :: (Eq a) => Fml a -> [Fml a]
  getFmls (And p q)   = getFmls p ++ getFmls q
  getFmls (NAnd p q)  = getFmls p ++ getFmls q
  getFmls (Or p q)    = getFmls p ++ getFmls q
  getFmls (NOr p q)   = getFmls p ++ getFmls q
  getFmls (XOr p q)   = getFmls p ++ getFmls q
  getFmls (XNOr p q)  = getFmls p ++ getFmls q
  getFmls (Imply p q) = getFmls p ++ getFmls q
  getFmls (Equiv p q) = getFmls p ++ getFmls q
  getFmls (Not p)     = getFmls p
  getFmls final       = [final]

  isFinal :: (Eq a) => Fml a -> Bool
  isFinal (Final _)  = True

  toVar:: Fml a -> Var.Var a
  toVar (Final a) = a

  -- |’vars’ @p@ returns all variables that occur in formula @p@. Duplicate
  -- occurrences are removed.
  vars :: (Eq a) => Fml a -> [Var.Var a]
  vars = L.nub . L.map toVar . L.filter isFinal . getFmls

  -- |’depth’ @p@ return the depth of fomula @p@.
  depth :: (Eq a) => Fml a -> Int
  depth (Final _)   = 0
  depth (Not p)     = 1 + depth p
  depth (And p q)   = 1 + max (depth p) (depth q)
  depth (NAnd p q)  = 1 + max (depth p) (depth q)
  depth (Or p q)    = 1 + max (depth p) (depth q)
  depth (NOr p q)   = 1 + max (depth p) (depth q)
  depth (XOr p q)   = 1 + max (depth p) (depth q)
  depth (XNOr p q)  = 1 + max (depth p) (depth q)
  depth (Imply p q) = 1 + max (depth p) (depth q)
  depth (Equiv p q) = 1 + max (depth p) (depth q)
  
  -- |’toNNF’ @f@ converts the formula @f@ to NNF.
  toNNF :: Fml a -> Fml a
  toNNF (And p q)         = And (toNNF p) (toNNF q)
  toNNF (Or p q)          = Or  (toNNF p) (toNNF q)
  
  toNNF (Equiv p q)       = And (toNNF (Imply p q)) (toNNF (Imply q p))
  toNNF (Not(Equiv p q))  = Or  (And (toNNF p) (toNNF (Not q))) (And (toNNF (Not p)) (toNNF q))

  toNNF (Imply p q)       = Or  (toNNF (Not p)) (toNNF q)
  toNNF (Not(Imply p q))  = And  (toNNF p) (toNNF (Not q))

  toNNF (XOr p q)         = And (Or  (toNNF p) (toNNF q)) (Not (And (toNNF p) (toNNF q)))
  toNNF (XNOr p q)        = Or  (And (toNNF p) (toNNF q)) (And (toNNF (Not p)) (toNNF (Not q)))

  toNNF (NAnd p q)        = Or  (toNNF (Not p)) (toNNF (Not q))
  toNNF (NOr p q)         = And (toNNF (Not p)) (toNNF (Not q))
  toNNF (Not (Or p q))    = toNNF (NOr p q)
  toNNF (Not (And p q))   = toNNF (NAnd p q)

  toNNF (Not (Not p))     = toNNF p
  toNNF (Not p)           = Not (toNNF p)
  toNNF (Final p)         = Final p

  -- |’toCNF’ @f@ converts the formula @f@ to CNF.
  toCNF :: Fml a -> Fml a
  toCNF = toCNF' . toNNF
      where 
            toCNF' :: Fml a -> Fml a
            toCNF' fml = case fml of
                  Or p (And q r) -> And (toCNF' (Or p q)) (toCNF' (Or p r))
                  Or (And p q) r -> And (toCNF' (Or p r)) (toCNF' (Or q r))
                  Or p q         -> Or  (toCNF' p) (toCNF' q)
                  And p q        -> And (toCNF' p) (toCNF' q)
                  Not p          -> Not p
                  Final p        -> Final p


  -- |’toDNF’ @f@ converts the formula @f@ to DNF.
  toDNF :: Fml a -> Fml a
  toDNF = toDNF' . toNNF
      where 
            toDNF' :: Fml a -> Fml a
            toDNF' fml = case fml of
                  And p (Or q r) -> Or (toDNF' (And p q)) (toDNF' (And p r))
                  And (Or p q) r -> Or (toDNF' (And p r)) (toDNF' (And q r))
                  Or p q         -> Or  (toDNF' p) (toDNF' q)
                  And p q        -> And (toDNF' p) (toDNF' q)
                  Not p          -> Not p
                  Final p        -> Final p

  -- |’isNNF’ @f@ returns true if formula @f@ is NNF.
  isNNF :: Fml a -> Bool
  isNNF (Not p)   = isNNF p
  isNNF (Or p q)  = isNNF p && isNNF q
  isNNF (And p q) = isNNF p && isNNF q
  isNNF (Final _) = True
  isNNF _         = False

  -- |’isCNF’ @f@ returns true if formula @f@ is CNF.
  isCNF :: Fml a -> Bool
  isCNF (Not p)                   = isCNF p
  isCNF (And (Final _) (Final _)) = False
  isCNF (And p q)                 = isCNF p && isCNF q
  isCNF (Or (Final _) (Final _))  = True
  isCNF (Or _ _)                  = False
  isCNF (Final _)                 = True
  isCNF _                         = False

  -- |’isDNF’ @f@ returns true if formula @f@ is DNF.
  isDNF :: Fml a -> Bool
  isDNF (Not p)                   = isCNF p
  isDNF (Or (Final _) (Final _))  = False
  isDNF (Or p q)                  = isDNF p && isDNF q
  isDNF (And (Final _) (Final _)) = True
  isDNF (And _ _)                 = False
  isDNF (Final _)                 = True
  isDNF _                         = False

  -- |’toUniversalNAnd’ @p@ returns a NAND-formula that is equivalent
  -- to formula @p@.
  toUniversalNAnd :: Fml a -> Fml a
  toUniversalNAnd (Final p) = Final p
  toUniversalNAnd (Not p)   = NAnd (toUniversalNAnd p) (toUniversalNAnd p)
  toUniversalNAnd (Or p q)  = NAnd
                              (NAnd (toUniversalNAnd p) (toUniversalNAnd p))
                              (NAnd (toUniversalNAnd q) (toUniversalNAnd q))
  toUniversalNAnd (And p q) = NAnd
                              (NAnd (toUniversalNAnd p) (toUniversalNAnd q))
                              (NAnd (toUniversalNAnd p) (toUniversalNAnd q))

  -- |’toUniversalNOr’ @p@ returns a NOR-formula that is equivalent
  -- to formula @p@.
  toUniversalNOr :: Fml a -> Fml a
  toUniversalNOr (Final p)  = Final p
  toUniversalNOr (Not p)    = NOr (toUniversalNOr p) (toUniversalNOr p)
  toUniversalNOr (Or p q)   = NOr
                              (NOr (toUniversalNOr p) (toUniversalNAnd q))
                              (NOr (toUniversalNOr p) (toUniversalNAnd q))
  toUniversalNOr (And p q)  = NOr
                              (NOr (toUniversalNOr p) (toUniversalNAnd p))
                              (NOr (toUniversalNOr q) (toUniversalNAnd q))

  -- |’isUniversalNAnd’ @p@ returns true iff formula @p@ uses only NAND
  -- and variables.
  isUniversalNAnd :: Fml a -> Bool
  isUniversalNAnd (Final _)   = True
  isUniversalNAnd (NAnd p q)  = isUniversalNAnd p && isUniversalNAnd q
  isUniversalNAnd _           = False

  -- |’isUniversalNOr’ @p@ returns true iff formula @p@ uses only NOR
  -- and variables.
  isUniversalNOr :: Fml a -> Bool
  isUniversalNOr (Final _)    = True
  isUniversalNOr (NOr p q)    = isUniversalNOr p && isUniversalNOr q
  isUniversalNOr _            = False

  -- |’toCCNF’ @f@ converts the formula @f@ to CCNF.
  -- toCCNF :: Fml a -> Fml a

  -- |’isCCNF’ @f@ returns true iff formula @f@ is CCNF.
  -- isCCNF :: Fml a -> Bool