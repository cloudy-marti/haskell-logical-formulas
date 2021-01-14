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
, toCCNF
, toDNF
, toUniversalNAnd
, toUniversalNOr
-- * Testing
, isNNF
, isCNF
, isUniversalNAnd
, isUniversalNOr
, isCCNF
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
  toNNF fml
      | isNNF fml         = fml
  toNNF (Not (Not p))     = toNNF p
  toNNF (NAnd p q)        = Or  (toNNF (Not p)) (toNNF (Not q))
  toNNF (NOr p q)         = And (toNNF (Not p)) (toNNF (Not q))
  toNNF (Not (Or p q))    = toNNF (NOr p q)
  toNNF (Not (And p q))   = toNNF (NAnd p q)
  toNNF (Not(Equiv p q))  = Or  (And (toNNF p) (toNNF (Not q))) (And (toNNF (Not p)) (toNNF q))
  toNNF (Not(Imply p q))  = And  (toNNF p) (toNNF (Not q))
  toNNF (And p q)         = And (toNNF p) (toNNF q)
  toNNF (Or p q)          = Or  (toNNF p) (toNNF q)
  toNNF (Equiv p q)       = And (toNNF (Imply p q)) (toNNF (Imply q p))
  toNNF (Imply p q)       = Or  (toNNF (Not p)) (toNNF q)
  toNNF (XOr p q)         = And (Or  (toNNF p) (toNNF q)) (Not (And (toNNF p) (toNNF q)))
  toNNF (XNOr p q)        = Or  (And (toNNF p) (toNNF q)) (And (toNNF (Not p)) (toNNF (Not q)))
  -- XNor can also be implemented this way:
  -- toNNF (XNOr p q)        = And  (Or (toNNF (Not p)) (toNNF q)) (Or (toNNF p) (toNNF (Not q))) 
  toNNF (Not p)           = Not p
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
  isNNF (Not (Final _)) = True
  isNNF (Not _)         = False
  isNNF (Or p q)        = isNNF p && isNNF q
  isNNF (And p q)       = isNNF p && isNNF q
  isNNF (Final _)       = True
  isNNF _               = False

  -- |’isCNF’ @f@ returns true if formula @f@ is CNF.
  isCNF :: Fml a -> Bool
  isCNF (Not (Final _))           = True
  isCNF (Not _)                   = False
  isCNF (And (Final _) (Final _)) = False
  isCNF (And p q)                 = isCNF p && isCNF q
  isCNF (Or (Final _) (Final _))  = True
  isCNF (Or p q)                  = isCNF p && isCNF q
  isCNF (Final _)                 = True
  isCNF _                         = False

  -- |’isDNF’ @f@ returns true if formula @f@ is DNF.
  isDNF :: Fml a -> Bool
  isDNF (Not (Final _))           = True
  isDNF (Not _)                   = False
  isDNF (And (Final _) (Final _)) = True
  isDNF (And p q)                 = isDNF p && isDNF q
  isDNF (Or (Final _) (Final _))  = False
  isDNF (Or p q)                  = isDNF p && isDNF q
  isDNF (Final _)                 = True
  isDNF _                         = False

  -- |’toUniversalNAnd’ @p@ returns a NAND-formula that is equivalent
  -- to formula @p@.
  toUniversalNAnd :: Fml a -> Fml a
  toUniversalNAnd = toUniversalNAnd' . toNNF
      where 
            toUniversalNAnd' :: Fml a -> Fml a
            toUniversalNAnd' fml = case fml of
                  Or p q         -> NAnd
                                     (NAnd (toUniversalNAnd' p) (toUniversalNAnd' p))
                                     (NAnd (toUniversalNAnd' q) (toUniversalNAnd' q))
                  And p q        -> NAnd
                                     (NAnd (toUniversalNAnd' p) (toUniversalNAnd' q))
                                     (NAnd (toUniversalNAnd' p) (toUniversalNAnd' q))
                  Not p          -> NAnd p p
                  Final p        -> Final p

  -- |’toUniversalNOr’ @p@ returns a NOR-formula that is equivalent
  -- to formula @p@.
  toUniversalNOr :: Fml a -> Fml a
  toUniversalNOr = toUniversalNOr' . toNNF
      where 
            toUniversalNOr' :: Fml a -> Fml a
            toUniversalNOr' fml = case fml of
                  Or p q    -> NOr
                                 (NOr (toUniversalNOr' p) (toUniversalNOr' q))
                                 (NOr (toUniversalNOr' p) (toUniversalNOr' q))
                  And p q   -> NOr
                                 (NOr (toUniversalNOr' p) (toUniversalNOr' p))
                                 (NOr (toUniversalNOr' q) (toUniversalNOr' q))
                  Not p     -> NOr p p
                  Final p   -> Final p

--   reduceUnivervalNandFormula :: Fml a -> Fml a
--   reduceUnivervalNandFormula fml = case fml of
--           NAnd (NAnd p q) (NAnd r s)            -> NAnd (reduceUnivervalNandFormula p) (reduceUnivervalNandFormula q)
--           -- NAnd (Final _) q                  -> reduceUnivervalNandFormula q
--           -- NAnd  p (Final _)                 -> reduceUnivervalNandFormula p
--           NAnd p q                          -> NAnd p q
--           Final a                           -> Final a

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
  toCCNF :: Fml a -> Fml a
  toCCNF = toCCNF' . toCNF
      where 
            toCCNF' :: Fml a -> Fml a
            toCCNF' fml = case fml of
                  And (And p q) (Or r s)  -> And (Or r s) (And (toCCNF' p) (toCCNF' q))
                  And (Or p q) (And r s)  -> And (Or p q) (And (toCCNF' r) (toCCNF' s))
                  And (And p q) (And r s) -> And (toCCNF' p) (And (toCCNF' q) (And (toCCNF' r) (toCCNF' s)))
                  And p q                 -> And (toCCNF' p) (toCCNF' q)
                  Or p q                  -> Or p q
                  Not p                   -> Not (toCCNF' p)
                  Final p                 -> Final p

  -- |’isCCNF’ @f@ returns true iff formula @f@ is CCNF.
  isCCNF :: Fml a -> Bool
  isCCNF (Final _)                        = True
  isCCNF (Not (Final _))                  = True
  isCCNF (Or (Final _) (Or p q))          = isCCNF p && isCCNF q
  isCCNF (Or (Not (Final _)) (Or p q))    = isCCNF p && isCCNF q
  isCCNF (Or p q)                         = isCCNF p && isCCNF q
  isCCNF (And (Final _) _)                = False
  isCCNF (And (Not (Final _)) _)          = False
  isCCNF (And (And _ _) _)                = False
  isCCNF (And p q)                        = isCCNF p && isCCNF q