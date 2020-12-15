module Data.Logic.Fml (
-- * Type
Fml (..)
-- * Querying
, depth
, vars
-- * Formatting
, prettyFormat
-- * Transforming
-- , toNNF
-- , toCNF
-- , toCCNF
-- , toDNF
-- , toUniversalNAnd
-- * Testing
-- , isNNF
-- , isCNF
-- , isCCNF
-- , isDNF
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
    deriving (Show)

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

  -- |'reduceFormula' Delete all operators but Not, Or, And
  reduceFormula :: Fml a -> Fml a
  reduceFormula (Final a)   = Final a
  reduceFormula (Not p)     = Not p
  reduceFormula (And p q)   = And (reduceFormula p) (reduceFormula q)
  reduceFormula (NAnd p q)  = Not $ And (reduceFormula p) (reduceFormula q)
  reduceFormula (Or p q)    = Or (reduceFormula p) (reduceFormula q)
  reduceFormula (NOr p q)   = Not $ Or (reduceFormula p) (reduceFormula q)
  reduceFormula (XOr p q)   = And
                              (Not $ And (reduceFormula p) (reduceFormula q))
                              (Not $ And (Not (reduceFormula p)) (Not (reduceFormula q)))
  reduceFormula (XNOr p q)  = Not $ And
                              (Not $ And (reduceFormula p) (reduceFormula q))
                              (Not $ And (Not (reduceFormula p)) (Not (reduceFormula q)))
  reduceFormula (Imply p q) = Or
                              (Not (reduceFormula p))
                              (And (reduceFormula p) (reduceFormula q))
  reduceFormula (Equiv p q) = reduceFormula $ XNOr p q

  -- |'morganLaw' Apply Not operator to formula
  morganLaw :: Fml a -> Fml a
  morganLaw (Final a) = Not $ Final a
  morganLaw (Not p)   = p
  morganLaw (And p q) = Or (Not p) (Not q)
  morganLaw (Or p q)  = And (Not p) (Not q)
  
  -- |’toNNF’ @f@ converts the formula @f@ to NNF.
  toNNF :: Fml a -> Fml a
  toNNF = morganLaw . reduceFormula

  -- |’toCNF’ @f@ converts the formula @f@ to CNF.
  -- toCNF :: Fml a -> Fml a

  -- |’toDNF’ @f@ converts the formula @f@ to DNF.
  -- toDNF :: Fml a -> Fml a

  -- |’isNNF’ @f@ returns true if formula @f@ is NNF.
  -- isNNF :: Fml a -> Bool

  -- |’isCNF’ @f@ returns true if formula @f@ is CNF.
  -- isCNF :: Fml a -> Bool

  -- |’isDNF’ @f@ returns true if formula @f@ is DNF.
  -- isDNF :: Fml a -> Bool

  -- |’toUniversalNAnd’ @p@ returns a NAND-formula that is equivalent
  -- to formula @p@.
  -- toUniversalNAnd :: Fml a -> Fml a

  -- |’toUniversalNOr’ @p@ returns a NOR-formula that is equivalent
  -- to formula @p@.
  -- toUniversalNOr :: Fml a -> Fml a

  -- |’isUniversalNAnd’ @p@ returns true iff formula @p@ uses only NAND
  -- and variables.
  -- isUniversalNAnd :: Fml a -> Bool

  -- |’isUniversalNOr’ @p@ returns true iff formula @p@ uses only NOR
  -- and variables.
  -- isUniversalNOr :: Fml a -> Bool

  -- |’toCCNF’ @f@ converts the formula @f@ to CCNF.
  -- toCCNF :: Fml a -> Fml a

  -- |’isCCNF’ @f@ returns true iff formula @f@ is CCNF.
  -- isCCNF :: Fml a -> Bool