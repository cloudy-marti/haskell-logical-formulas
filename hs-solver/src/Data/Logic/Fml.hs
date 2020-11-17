module Data.Logic.Fml (
-- * Type
Fml (..)
-- * Querying
-- , depth
-- , vars
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
  data Fml a = And (Fml a) (Fml a)
    | NAnd (Fml a) (Fml a)
    | Or (Fml a) (Fml a)
    | NOr (Fml a) (Fml a)
    | XOr (Fml a) (Fml a)
    | XNOr (Fml a) (Fml a)
    | Imply (Fml a) (Fml a)
    | Equiv (Fml a) (Fml a)
    | Not (Fml a)
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
  prettyFormat (And p q) = "(" ++ prettyFormat p ++ " . " ++ prettyFormat q ++ ")"
  prettyFormat (NAnd p q) = "(" ++ prettyFormat p ++ " ~. " ++ prettyFormat q ++ ")"
  prettyFormat (Or p q) = "(" ++ prettyFormat p ++ " + " ++ prettyFormat q ++ ")"
  prettyFormat (NOr p q) = "(" ++ prettyFormat p ++ " ~+ " ++ prettyFormat q ++ ")"
  prettyFormat (XOr p q) = "(" ++ prettyFormat p ++ " x+ " ++ prettyFormat q ++ ")"
  prettyFormat (XNOr p q) = "(" ++ prettyFormat p ++ " x~+ " ++ prettyFormat q ++ ")"
  prettyFormat (Imply p q) = "(" ++ prettyFormat p ++ " => " ++ prettyFormat q ++ ")"
  prettyFormat (Equiv p q) = "(" ++ prettyFormat p ++ " <=> " ++ prettyFormat q ++ ")"
  prettyFormat (Not p) = "-" ++ prettyFormat p
  prettyFormat (Final v) = show v
  -- to be completed...

  -- |’vars’ @p@ returns all variables that occur in formula @p@. Duplicate
  -- occurrences are removes.
  -- vars :: (Eq a) => Fml a -> [Var.Var a]

  -- |’depth’ @p@ return the depth of fomula @p@.
  -- depth :: (Num b, Ord b) => Fml a -> b

  -- |’toNNF’ @f@ converts the formula @f@ to NNF.
  -- toNNF :: Fml a -> Fml a

  -- |’toCNF’ @f@ converts the formula @f@ to CNF.
  -- toCNF :: Fml a -> Fml a

  -- |’toDNF’ @f@ converts the formula @f@ to DNF.
  -- toDNF :: Fml a -> Fml a

  -- |’isNNF’ @f@ returns true iff formula @f@ is NNF.
  -- isNNF :: Fml a -> Fml a

  -- |’isCNF’ @f@ returns true iff formula @f@ is CNF.
  -- isCNF :: Fml a -> Fml a

  -- |’isDNF’ @f@ returns true iff formula @f@ is DNF.
  -- isDNF :: Fml a -> Fml a

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