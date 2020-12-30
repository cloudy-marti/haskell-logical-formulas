import Test.HUnit
import qualified Data.Logic.Var as Var
import qualified Data.Logic.Fml as Fml
import qualified Data.Logic.Combinator as Comb
import Data.Maybe (fromJust)

----------------------------------------- var declaration ---------------------------------------------------- 

v1 = Fml.Final $ Var.mk 1
v2 = Fml.Final $ Var.mk 2
v3 = Fml.Final $ Var.mk 3
v4 = Fml.Final $ Var.mk 4

va = Fml.Final $ Var.mk "a"
vb = Fml.Final $ Var.mk "b"
vc = Fml.Final $ Var.mk "c"

vz = Fml.Final $ Var.mk "z"
vy = Fml.Final $ Var.mk "y"
vx = Fml.Final $ Var.mk "x"

------------------------------------------- vars TEST -------------------------------------------------------
testFmlGetVarFromFormula :: Test
testFmlGetVarFromFormula = 
    TestCase $ assertEqual "Should return ['z'] for Fml.Not vz" [Var.mk "z"] (Fml.vars c)
                           where 
                               c = Fml.Not vz

testFmlGetVarFromFormula2 :: Test
testFmlGetVarFromFormula2 = 
    TestCase $ assertEqual "Should return ['z'] from formula" [Var.mk "z"] (Fml.vars c)
                           where 
                               c = Fml.Not $ Fml.Not vz

testFmlUniqueVarsFromFormula :: Test
testFmlUniqueVarsFromFormula = 
    TestCase $ assertEqual "Should return ['z'] for from formula" [Var.mk "z"] (Fml.vars c)
                           where 
                               c = Fml.And vz vz

testFmlGetAllVarsFromFormula :: Test
testFmlGetAllVarsFromFormula = 
    TestCase $ assertEqual "Should return ['x', 'b', 'a', 'z', 'c'] for Fml.And vz vz" [Var.mk "x", Var.mk "b", Var.mk "a", Var.mk "z", Var.mk "c"] (Fml.vars c)
                           where 
                               c = Fml.And vx $ Fml.NAnd vb $ Fml.Or va $ Fml.NOr vb $ Fml.And vx $ Fml.Imply vz $ Fml.Equiv vc $ Fml.Not vx

------------------------------------------- depth TEST -------------------------------------------------------

testFmlDephOfFormula :: Test
testFmlDephOfFormula = TestCase $ assertEqual "Should return 0 for formula" 0 (Fml.depth vx)

testFmlDephNotfFormula :: Test
testFmlDephNotfFormula = 
    TestCase $ assertEqual "Should return 1 for negation of formula" 1 (Fml.depth c)
                           where 
                               c = Fml.Not vx
 
testFmlDephNotNotOfFormula :: Test
testFmlDephNotNotOfFormula = 
    TestCase $ assertEqual "Should return 2 for negation of negation of formula" 2 (Fml.depth c)
                           where 
                               c = Fml.Not $ Fml.Not vx   

testFmlMaxDephFormula :: Test
testFmlMaxDephFormula = 
    TestCase $ assertEqual "Should return 2, the max depht of a formula" 2 (Fml.depth c)
                           where 
                               c = Fml.Or vx $ Fml.Not vy   

-------------------------------------------- toNNF TEST ------------------------------------------------------- 
testConvertImplyFormulaToNNF :: Test
testConvertImplyFormulaToNNF = 
    TestCase $ assertEqual "A => B formula should return !A V B" (Fml.Or (Fml.Not va) vb) (Fml.toNNF c)
                           where 
                               c = Fml.Imply va vb  

testConvertNotImplyFormulaToNNF :: Test
testConvertNotImplyFormulaToNNF = 
    TestCase $ assertEqual "!(A -> B) formula should return A ∧ !B" (Fml.And va (Fml.Not vb)) (Fml.toNNF c)
                           where 
                               c = Fml.Not $ Fml.Imply va vb

testConvertNOrFormulaToNNF :: Test
testConvertNOrFormulaToNNF = 
    TestCase $ assertEqual "!(A ∨ B) formula should return !A ∧ !B " (Fml.And (Fml.Not va) (Fml.Not vb)) (Fml.toNNF c)
                           where 
                               c = Fml.NOr va vb

testConvertNAndFormulaToNNF :: Test
testConvertNAndFormulaToNNF = 
    TestCase $ assertEqual "!(A ∧ B) formula should return !A ∨ !B " (Fml.Or (Fml.Not va) (Fml.Not vb)) (Fml.toNNF c)
                           where 
                               c = Fml.NAnd va vb

testConvertNotNotFormulaToNNF :: Test
testConvertNotNotFormulaToNNF = 
    TestCase $ assertEqual "!!A formula should return A" va (Fml.toNNF c)
                           where 
                               c = Fml.Not $ Fml.Not va                                

testConvertEqFormulaToNNF :: Test
testConvertEqFormulaToNNF = 
    TestCase $ assertEqual "A <--> B should return (!A V B) ∧ (A V !B) " (Fml.And (Fml.Or (Fml.Not va) vb) (Fml.Or (Fml.Not vb) va)) (Fml.toNNF c)
                           where 
                               c = Fml.Equiv va vb 

testConvertComplexFormulaToNNF :: Test
testConvertComplexFormulaToNNF = 
    TestCase $ assertEqual "!(!A ∨ B) ∨ (X -> !Y) should return (A ∧ !B) ∨ (!X ∨ !Y)" (Fml.Or (Fml.And va (Fml.Not vb)) (Fml.Or (Fml.Not vx) (Fml.Not vy)))  (Fml.toNNF c)
                           where 
                               c = Fml.Or (Fml.Not (Fml.Or (Fml.Not va) vb)) (Fml.Imply vx (Fml.Not vy))


testConvertComplexFormulaToNNF2 :: Test
testConvertComplexFormulaToNNF2 = 
    TestCase $ assertEqual "(!A -> B) -> (B -> !X) should return (!A ∧ !B) ∨ (!B ∨ !X)" (Fml.Or (Fml.And (Fml.Not va) (Fml.Not vb)) (Fml.Or (Fml.Not vb) (Fml.Not vx))) (Fml.toNNF c)
                           where 
                               c = Fml.Imply (Fml.Imply (Fml.Not va) vb) (Fml.Imply vb (Fml.Not vx))

testConvertComplexFormulaToNNF3 :: Test
testConvertComplexFormulaToNNF3 = 
    TestCase $ assertEqual "(A ⊙ B) -> !(C ∨ (A ∧ B)) should return NNF ?????" 
                                   (Fml.Or 
                                     (
                                        Fml.And 
                                         (Fml.Or va vb)
                                         (Fml.Or (Fml.Not va) (Fml.Not vb))
                                     )
                                     (
                                         Fml.Or
                                         (Fml.Not vc)
                                         (Fml.And (Fml.Not va) (Fml.Not vb))
                                     )
                                   )
                                    (Fml.toNNF c)
                           where 
                               c = Fml.Imply (Fml.XNOr va vb) (Fml.Not (Fml.Or vc (Fml.And va vb))) 

-------------------------------------------- toCNF TEST ------------------------------------------------------- 
testConvertImplyFormulaToCNF :: Test
testConvertImplyFormulaToCNF = 
    TestCase $ assertEqual "A -> (B ∧ X) should return (!A ∨ B) ∧ (!A ∨ X)" (Fml.And (Fml.Or (Fml.Not va) vb) (Fml.Or (Fml.Not va) vx)) (Fml.toCNF c)
                           where 
                               c = Fml.Imply va (Fml.And vb vx)

testConvertImplyFormulaToCNF2 :: Test
testConvertImplyFormulaToCNF2 = 
    TestCase $ assertEqual "(A ∧ B) -> X should return (!A ∨ !B) ∨ X " (Fml.Or (Fml.Or (Fml.Not va) (Fml.Not vb)) vx) (Fml.toCNF c)
                           where 
                               c = Fml.Imply (Fml.And va vb) vx

testConvertComplexFormulaToCNF :: Test
testConvertComplexFormulaToCNF = 
    TestCase $ assertEqual "!(!A ∨ B) ∨ (X -> !Y) should return ( A ∨ !X ∨ !Y) ∧ (!B ∨ !X ∨ !Y)" (Fml.And (Fml.Or va $ Fml.Or (Fml.Not vx) (Fml.Not vy)) (Fml.Or (Fml.Not vb) $ Fml.Or (Fml.Not vx) (Fml.Not vy)))(Fml.toCNF c)
                           where 
                               c = Fml.Or (Fml.Not (Fml.Or (Fml.Not va) vb)) (Fml.Imply vx (Fml.Not vy))


testConvertComplexFormulaToCNF2 :: Test
testConvertComplexFormulaToCNF2 = 
    TestCase $ assertEqual "(!A -> B) -> (B -> !X) should return (!A ∨ !B ∨ !X) ∧ (!B ∨ !X)" (Fml.And (Fml.Or (Fml.Not va) $ Fml.Or (Fml.Not vb) (Fml.Not vx)) (Fml.Or (Fml.Not vb) (Fml.Not vx))) (Fml.toCNF c)
                           where 
                               c = Fml.Imply (Fml.Imply (Fml.Not va) vb) (Fml.Imply vb (Fml.Not vx))

testConvertComplexFormulaToCNF3 :: Test
testConvertComplexFormulaToCNF3 = 
    TestCase $ assertEqual "(A ⊙ B) -> !(C ∨ (A ∧ B)) should return ????" 
                                   (Fml.And 
                                     (Fml.Or va $ Fml.Or vb $ Fml.Or (Fml.Not vc) (Fml.Not va)) $
                                    Fml.And
                                     (Fml.Or va $ Fml.Or vb $ Fml.Or (Fml.Not vc) (Fml.Not vb)) $
                                    Fml.And 
                                     (Fml.Or (Fml.Not va) $ Fml.Or (Fml.Not vb) $ Fml.Or (Fml.Not vc) (Fml.Not va)) 
                                     (Fml.Or (Fml.Not va) $ Fml.Or (Fml.Not vb) $ Fml.Or (Fml.Not vc) (Fml.Not vb))) 
                                    (Fml.toCNF c)
                           where 
                               c = Fml.Imply (Fml.XNOr va vb) (Fml.NOr vc (Fml.And va vb)) 

-------------------------------------------- toDNF TEST ------------------------------------------------------- 
-- TODO ADD OTHER TEST

testDNF :: Test
testDNF = 
    TestCase $ assertEqual "((A -> (B ∧ X)) ∨ !(A ∨ !(X ∨ Y)) ) should return (!A ∨ ( B ∧ X)) ∨ ((!A ∧ X) ∨ (!A ∧ Y))" (Fml.Or (Fml.Or (Fml.Not va) (Fml.And vb vx)) (Fml.Or (Fml.And (Fml.Not va) vx) (Fml.And (Fml.Not va) vy))) (Fml.toDNF c)
                           where 
                               c = Fml.Or (Fml.Imply va (Fml.And vb vx)) (Fml.Not (Fml.Or va (Fml.Not (Fml.Or vx vy))))  

-------------------------------------------- isNNF TEST -------------------------------------------------------    

testIsNNF :: Test
testIsNNF = 
    TestCase $ assertEqual "A ∧ (B ∨ !X) should return True " True (Fml.isNNF c)
                           where 
                               c = Fml.And va (Fml.Or vb (Fml.Not vx))

testIsNNF2 :: Test
testIsNNF2 = 
    TestCase $ assertEqual "(A ∧ B) ∨ (A ∧ !X)  should return True " True (Fml.isNNF c)
                           where 
                               c = Fml.Or (Fml.And va vb) (Fml.And va (Fml.Not vx))

testIsNNF3 :: Test
testIsNNF3 = 
    TestCase $ assertEqual "(A ∨ B) ∧ X  should return True " True (Fml.isNNF c)
                           where 
                               c = Fml.And (Fml.Or va vb) vx
testIsNNF4 :: Test
testIsNNF4 = 
    TestCase $ assertEqual "(A ∧ (!B ∨ X) ∧ !X) ∨ Y  should return True " True (Fml.isNNF c)
                           where 
                               c = Fml.Or (Fml.And va $ Fml.And (Fml.Or (Fml.Not vb) vx) (Fml.Not vx)) vy
testIsNNF5 :: Test
testIsNNF5 = 
    TestCase $ assertEqual "A ∨ !B  should return True " True (Fml.isNNF c)
                           where 
                               c = Fml.Or va (Fml.Not vb)    
testIsNNF6 :: Test
testIsNNF6 = 
    TestCase $ assertEqual "A ∧ !B  should return True " True (Fml.isNNF c)
                           where 
                               c = Fml.And va (Fml.Not vb) 
testIsNNF7 :: Test
testIsNNF7 = 
    TestCase $ assertEqual "A -> B  should return False " False (Fml.isNNF c)
                           where 
                               c = Fml.Imply va vb
testIsNNF8 :: Test
testIsNNF8 = 
    TestCase $ assertEqual "A <-> B  should return False " False (Fml.isNNF c)
                           where 
                               c = Fml.Equiv va vb
testIsNNF9 :: Test
testIsNNF9 = 
    TestCase $ assertEqual "!(A ∧ B)  should return False " False (Fml.isNNF c)
                           where 
                               c = Fml.NAnd va vb
testIsNNF10 :: Test
testIsNNF10 = 
    TestCase $ assertEqual "!(A ∨ B)  should return False " False (Fml.isNNF c)
                           where 
                               c = Fml.NOr va vb
testIsNNF11 :: Test
testIsNNF11 = 
    TestCase $ assertEqual "!(A ∨ B)  should return False " False (Fml.isNNF c)
                           where 
                               c = Fml.NOr va (Fml.Not vb) 
testIsNNF12 :: Test
testIsNNF12 = 
    TestCase $ assertEqual "!(A ∧ B)  should return False " False (Fml.isNNF c)
                           where 
                               c = Fml.Not (Fml.And va vb)
testIsNNF13 :: Test
testIsNNF13 = 
    TestCase $ assertEqual "!(A ∨ B)  should return False " False (Fml.isNNF c)
                           where 
                               c = Fml.Not (Fml.Or va vb)  
testIsNNF14 :: Test
testIsNNF14 = 
    TestCase $ assertEqual "!A ∧ B  should return True " True (Fml.isNNF c)
                           where 
                               c = Fml.And (Fml.Not va) vb
testIsNNF15 :: Test
testIsNNF15 = 
    TestCase $ assertEqual "!A ∨ !B  should return True " True (Fml.isNNF c)
                           where 
                               c = Fml.Or (Fml.Not va) (Fml.Not vb)

-------------------------------------------- isCNF TEST ------------------------------------------------------- 
testIsCNF :: Test
testIsCNF = 
    TestCase $ assertEqual " A should return True " True (Fml.isCNF c)
                           where 
                               c = va
testIsCNF2 :: Test
testIsCNF2 = 
    TestCase $ assertEqual " (A ∨ B) ∧ (!A ∨ C) should return True " True (Fml.isCNF c)
                           where 
                               c = Fml.And (Fml.Or va vb) (Fml.Or (Fml.Not va) vc)
testIsCNF3 :: Test
testIsCNF3 = 
    TestCase $ assertEqual " (A ∨ B) should return True " True (Fml.isCNF c)
                           where 
                               c = Fml.Or va vb
testIsCNF4 :: Test
testIsCNF4 = 
    TestCase $ assertEqual " A ∧ (B ∨ C) should return True " True (Fml.isCNF c)
                           where 
                               c = Fml.And va $ Fml.Or vb vc
testIsCNF5 :: Test
testIsCNF5 = 
    TestCase $ assertEqual " (A ∨ !B) ∧ ( A ∨ X ∨ Y) ∧ ( !A ∨ !X) should return True " True (Fml.isCNF c)
                           where 
                               c = Fml.And (Fml.Or va (Fml.Not vb)) $ Fml.And (Fml.Or va $ Fml.Or vx vy) (Fml.Or (Fml.Not va) (Fml.Not vx))
testIsCNF6 :: Test
testIsCNF6 = 
    TestCase $ assertEqual " (!A -> B) -> (B -> !X) converted to CNF : (!A ∨ !B ∨ !X) ∧ (!B ∨ !X) should return True " True (Fml.isCNF $ Fml.toCNF c)
                           where 
                               c = Fml.Imply (Fml.Imply (Fml.Not va) vb) (Fml.Imply vb (Fml.Not vx))
testIsNotCNF :: Test
testIsNotCNF = 
    TestCase $ assertEqual " !(A ∧ B) should return False " False (Fml.isCNF c)
                           where 
                               c = Fml.NAnd va vb
testIsNotCNF2 :: Test
testIsNotCNF2 = 
    TestCase $ assertEqual " !(A ∧ B) should return False " False (Fml.isCNF c)
                           where 
                               c = Fml.Not (Fml.And va vb)
testIsNotCNF3 :: Test
testIsNotCNF3 = 
    TestCase $ assertEqual " !(A ∨ B) should return False " False (Fml.isCNF c)
                           where 
                               c = Fml.NOr va vb
testIsNotCNF4 :: Test
testIsNotCNF4 = 
    TestCase $ assertEqual " !(A ∨ B) should return False " False (Fml.isCNF c)
                           where 
                               c = Fml.Not $ Fml.Or va vb
testIsNotCNF5 :: Test
testIsNotCNF5 = 
    TestCase $ assertEqual " (A ∧ B) ∨ C  should return False " False (Fml.isCNF c)
                           where 
                               c = Fml.Or (Fml.And va vb) vc

testIsNotCNF6 :: Test
testIsNotCNF6 = 
    TestCase $ assertEqual " A ∧ (B ∨ ( X ∧ Y )) should return False " False (Fml.isCNF c)
                           where 
                               c = Fml.And va (Fml.Or vb (Fml.And vx vy))

-------------------------------------------- isDNF TEST ------------------------------------------------------- 
testIsDNF :: Test
testIsDNF = 
    TestCase $ assertEqual " A should return True " True (Fml.isDNF c)
                           where 
                               c = va
testIsDNF2 :: Test
testIsDNF2 = 
    TestCase $ assertEqual " (A ∧ B) should return True " True (Fml.isDNF c)
                           where 
                               c = Fml.And va vb
testIsDNF3 :: Test
testIsDNF3 = 
    TestCase $ assertEqual "(A ∧ B) ∨ C should return True " True (Fml.isDNF c)
                           where 
                               c = Fml.Or (Fml.And va vb) vc
testIsDNF4 :: Test
testIsDNF4 = 
    TestCase $ assertEqual " (A ∧ !B ∧ !C) ∨ (!X ∧ Y ∧ Z) should return True " True (Fml.isDNF c)
                           where 
                               c = Fml.Or (Fml.And va $ Fml.And (Fml.Not vb) (Fml.Not vc)) (Fml.And (Fml.Not vx) $ Fml.And vy vz)
testIsDNF5 :: Test
testIsDNF5 = 
    TestCase $ assertEqual " (A ∧ !B) ∨ (A ∧ C ∧ X) ∨ (!A ∧ !C) should return True " True (Fml.isDNF c)
                           where 
                               c = Fml.Or (Fml.And va (Fml.Not vb)) $ Fml.Or (Fml.And va $ Fml.And vc vx) (Fml.And (Fml.Not va) (Fml.Not vc))
testIsDNF6 :: Test
testIsDNF6 = 
    TestCase $ assertEqual "((A -> (B ∧ X)) ∨ !(A ∨ !(X ∨ Y)) ) convert to DNF = (!A ∨ ( B ∧ X)) ∨ ((!A ∧ X) ∨ (!A ∧ Y)) should return True" True (Fml.isDNF $ Fml.toDNF c)
                           where 
                               c = Fml.Or (Fml.Imply va (Fml.And vb vx)) (Fml.Not (Fml.Or va (Fml.Not (Fml.Or vx vy)))) 
testIsNotDNF :: Test
testIsNotDNF = 
    TestCase $ assertEqual " !(A ∧ B) should return False " False (Fml.isDNF c)
                           where 
                               c = Fml.NAnd va vb
testIsNotDNF2 :: Test
testIsNotDNF2 = 
    TestCase $ assertEqual " !(A ∧ B) should return False " False (Fml.isDNF c)
                           where 
                               c = Fml.Not (Fml.And va vb)
testIsNotDNF3 :: Test
testIsNotDNF3 = 
    TestCase $ assertEqual " !(A ∨ B) should return False " False (Fml.isDNF c)
                           where 
                               c = Fml.NOr va vb
testIsNotDNF4 :: Test
testIsNotDNF4 = 
    TestCase $ assertEqual " !(A ∨ B) should return False " False (Fml.isDNF c)
                           where 
                               c = Fml.Not $ Fml.Or va vb
testIsNotDNF5 :: Test
testIsNotDNF5 = 
    TestCase $ assertEqual " A ∨ (B ∧ ( X ∨ Y )) should return False " False (Fml.isDNF c)
                           where 
                               c = Fml.Or va (Fml.And vb (Fml.Or vx vy))
testIsNotDNF6 :: Test
testIsNotDNF6 = 
    TestCase $ assertEqual " !(A ∧ B) ∨ C  should return False " False (Fml.isDNF c)
                           where 
                               c = Fml.Or (Fml.Not (Fml.And va vb)) vc

-------------------------------------------- toUniversalNAnd TEST -------------------------------------------------------
testConvertFinalToUniversalNAnd :: Test
testConvertFinalToUniversalNAnd = 
    TestCase $ assertEqual " A  should return A " va (Fml.toUniversalNAnd c)
                           where 
                               c = va

testConvertNotFinalToUniversalNAnd :: Test
testConvertNotFinalToUniversalNAnd = 
    TestCase $ assertEqual " !A  should return A NAnd A" (Fml.NAnd va va) (Fml.toUniversalNAnd c)
                           where 
                               c = Fml.Not va

testConvertAndToUniversalNAnd :: Test
testConvertAndToUniversalNAnd = 
    TestCase $ assertEqual " (A ∧ B) should return ( A NAND B ) NAND ( A NAND B ) " (Fml.NAnd (Fml.NAnd va vb) (Fml.NAnd va vb)) (Fml.toUniversalNAnd c)
                           where 
                               c = Fml.And va vb

testConvertOrToUniversalNAnd :: Test
testConvertOrToUniversalNAnd = 
    TestCase $ assertEqual " (A ∨ B) should return ( A NAND A ) NAND ( B NAND B ) " (Fml.NAnd (Fml.NAnd va va) (Fml.NAnd vb vb)) (Fml.toUniversalNAnd c)
                           where 
                               c = Fml.Or va vb

testConvertNOrToUniversalNAnd :: Test
testConvertNOrToUniversalNAnd = 
    TestCase $ assertEqual " (A Nor B) should return (( A NAND A ) NAND ( B NAND B )) NAND (( A NAND A ) NAND ( B NAND B )) " 
                             (Fml.NAnd (Fml.NAnd (Fml.NAnd va va) (Fml.NAnd vb vb)) (Fml.NAnd (Fml.NAnd va va) (Fml.NAnd vb vb))) (Fml.toUniversalNAnd c)
                           where 
                               c = Fml.NOr va vb

testConvertXOrToUniversalNAnd :: Test
testConvertXOrToUniversalNAnd = 
    TestCase $ assertEqual " (A Xor B) should return (A NAND ( A NAND B )) NAND (B NAND ( A NAND B ))" 
                             (Fml.NAnd (Fml.NAnd va (Fml.NAnd va vb)) (Fml.NAnd vb (Fml.NAnd va vb))) (Fml.toUniversalNAnd c)
                           where 
                               c = Fml.XOr va vb

testConvertXNOrToUniversalNAnd :: Test
testConvertXNOrToUniversalNAnd = 
    TestCase $ assertEqual " (A XNor B) should return (( A NAND A ) NAND ( B NAND B )) NAND ( A NAND B ) " 
                             (Fml.NAnd (Fml.NAnd (Fml.NAnd va va) (Fml.NAnd vb vb)) (Fml.NAnd va vb)) (Fml.toUniversalNAnd c)
                           where 
                               c = Fml.XNOr va vb

testConvertImplyToUniversalNAnd :: Test
testConvertImplyToUniversalNAnd = 
    TestCase $ assertEqual " (A -> B) should return (a NAND ( B NAND B ))" (Fml.NAnd va (Fml.NAnd vb vb)) (Fml.toUniversalNAnd c)
                           where 
                               c = Fml.Imply va vb

testConvertEquivToUniversalNAnd :: Test
testConvertEquivToUniversalNAnd = 
    TestCase $ assertEqual " (A <-> B) should return (a NAND ( B NAND B ))" (Fml.NAnd va (Fml.NAnd vb vb)) (Fml.toUniversalNAnd c)
                           where 
                               c = Fml.Equiv va vb
                               



-------------------------------------------- toUniversalNOr TEST -------------------------------------------------------
testConvertFinalToUniversalNOr :: Test
testConvertFinalToUniversalNOr = 
    TestCase $ assertEqual " A  should return A " va (Fml.toUniversalNOr c)
                           where 
                               c = va

testConvertNotFinalToUniversalNOr :: Test
testConvertNotFinalToUniversalNOr = 
    TestCase $ assertEqual " !A  should return A NOr A" (Fml.NOr va va) (Fml.toUniversalNOr c)
                           where 
                               c = Fml.Not va

testConvertAndToUniversalNOr :: Test
testConvertAndToUniversalNOr = 
    TestCase $ assertEqual " (A ∧ B) should return ( A NOR A ) NOR ( B NOR B ) " (Fml.NOr (Fml.NOr va va) (Fml.NOr vb vb)) (Fml.toUniversalNOr c)
                           where 
                               c = Fml.And va vb

testConvertOrToUniversalNOr :: Test
testConvertOrToUniversalNOr = 
    TestCase $ assertEqual " (A ∨ B) should return ( A NOR B ) NOR ( A NOR B ) " (Fml.NOr (Fml.NOr va vb) (Fml.NOr va vb)) (Fml.toUniversalNOr c)
                           where 
                               c = Fml.Or va vb

testConvertNAndToUniversalNOr :: Test
testConvertNAndToUniversalNOr = 
    TestCase $ assertEqual " (A NOr B) should return  (( A NOR A ) NOR ( B NOR B )) NOR (( A NOR A ) NOR ( B NOR B ))  " 
                             (Fml.NOr (Fml.NOr (Fml.NOr va va) (Fml.NOr vb vb)) (Fml.NOr (Fml.NOr va va) (Fml.NOr vb vb))) (Fml.toUniversalNOr c)
                           where 
                               c = Fml.NAnd va vb

testConvertXNOrToUniversalNOr :: Test
testConvertXNOrToUniversalNOr = 
    TestCase $ assertEqual " (A XOr B) should return (A NOR ( A NOR B )) NOR (B NOR ( A NOR B ))" 
                             (Fml.NOr (Fml.NOr va (Fml.NOr va vb)) (Fml.NOr vb (Fml.NOr va vb))) (Fml.toUniversalNOr c)
                           where 
                               c = Fml.XNOr va vb

testConvertXOrToUniversalNOr :: Test
testConvertXOrToUniversalNOr = 
    TestCase $ assertEqual " (A XNor B) should return (( A NOR A ) NOR ( B NOR B )) NOR ( A NOR B ) " 
                             (Fml.NOr (Fml.NOr (Fml.NOr va va) (Fml.NOr vb vb)) (Fml.NOr va vb)) (Fml.toUniversalNOr c)
                           where 
                               c = Fml.XOr va vb

testConvertImplyToUniversalNOr :: Test
testConvertImplyToUniversalNOr = 
    TestCase $ assertEqual " (A -> B) should return (( A NOR A ) NOR B) NOR ( A NOR A ) NOR B))" (Fml.NOr (Fml.NOr (Fml.NOr va va) vb) (Fml.NOr (Fml.NOr va va) vb)) (Fml.toUniversalNOr c)
                           where 
                               c = Fml.Imply va vb

testConvertEquivToUniversalNOr :: Test
testConvertEquivToUniversalNOr = 
    TestCase $ assertEqual " (A <-> B) should return TODO" (Fml.NOr va vb) (Fml.toUniversalNOr c)
                           where 
                               c = Fml.Equiv va vb

-------------------------------------------- isUniversalNAnd TEST -------------------------------------------------------
testIsUniversalNAnd :: Test
testIsUniversalNAnd = 
    TestCase $ assertEqual " A should return True " True (Fml.isUniversalNAnd c)
                           where 
                               c = va

testIsUniversalNAnd2 :: Test
testIsUniversalNAnd2 = 
    TestCase $ assertEqual " (A NAND B) should return True " True (Fml.isUniversalNAnd c)
                           where 
                               c = Fml.NAnd va vb

testIsUniversalNAnd3 :: Test
testIsUniversalNAnd3 = 
    TestCase $ assertEqual " ( (A NAND A) NAND (B NAND B)) should return True " True (Fml.isUniversalNAnd c)
                           where 
                               c = Fml.NAnd (Fml.NAnd va va) (Fml.NAnd vb vb)

testIsUniversalNAnd4 :: Test
testIsUniversalNAnd4 = 
    TestCase $ assertEqual " (A NAND ( A NAND B )) NAND (B NAND ( A NAND B )) should return True " True (Fml.isUniversalNAnd c)
                           where 
                               c = Fml.NAnd (Fml.NAnd va (Fml.NAnd va vb)) (Fml.NAnd vb (Fml.NAnd va vb))

testIsUniversalNAnd5 :: Test
testIsUniversalNAnd5 = 
    TestCase $ assertEqual " !(!A ∨ B) ∨ (X -> !Y) converted to universal NAnd should return True " True (Fml.isUniversalNAnd $ Fml.toUniversalNAnd c)
                           where 
                               c = Fml.Or (Fml.Not (Fml.Or (Fml.Not va) vb)) (Fml.Imply vx (Fml.Not vy))

testIsNotUniversalNAnd :: Test
testIsNotUniversalNAnd = 
    TestCase $ assertEqual " !A should return False " False (Fml.isUniversalNAnd c)
                           where 
                               c = Fml.Not va

testIsNotUniversalNAnd2 :: Test
testIsNotUniversalNAnd2 = 
    TestCase $ assertEqual " A ∧ B should return False " False (Fml.isUniversalNAnd c)
                           where 
                               c = Fml.And va vb

testIsNotUniversalNAnd3 :: Test
testIsNotUniversalNAnd3 = 
    TestCase $ assertEqual " A ∨ B should return False " False (Fml.isUniversalNAnd c)
                           where 
                               c = Fml.Or va vb

testIsNotUniversalNAnd4 :: Test
testIsNotUniversalNAnd4 = 
    TestCase $ assertEqual " A Nor B should return False " False (Fml.isUniversalNAnd c)
                           where 
                               c = Fml.NOr va vb
testIsNotUniversalNAnd5 :: Test
testIsNotUniversalNAnd5 = 
    TestCase $ assertEqual " A XOr B should return False " False (Fml.isUniversalNAnd c)
                           where 
                               c = Fml.XOr va vb

testIsNotUniversalNAnd6 :: Test
testIsNotUniversalNAnd6 = 
    TestCase $ assertEqual " A XNOr B should return False " False (Fml.isUniversalNAnd c)
                           where 
                               c = Fml.XNOr va vb

testIsNotUniversalNAnd7 :: Test
testIsNotUniversalNAnd7 = 
    TestCase $ assertEqual " A -> B should return False " False (Fml.isUniversalNAnd c)
                           where 
                               c = Fml.Imply va vb

testIsNotUniversalNAnd8 :: Test
testIsNotUniversalNAnd8 = 
    TestCase $ assertEqual " A <-> B should return False " False (Fml.isUniversalNAnd c)
                           where 
                               c = Fml.Equiv va vb

-------------------------------------------- isUniversalNOr TEST -------------------------------------------------------
testIsUniversalNOr :: Test
testIsUniversalNOr = 
    TestCase $ assertEqual " A should return True " True (Fml.isUniversalNOr c)
                           where 
                               c = va

testIsUniversalNOr2 :: Test
testIsUniversalNOr2 = 
    TestCase $ assertEqual " (A NOR B) should return True " True (Fml.isUniversalNOr c)
                           where 
                               c = Fml.NOr va vb

testIsUniversalNOr3 :: Test
testIsUniversalNOr3 = 
    TestCase $ assertEqual " ( (A NOR A) NOR (B NOR B)) should return True " True (Fml.isUniversalNOr c)
                           where 
                               c = Fml.NOr (Fml.NOr va va) (Fml.NOr vb vb)

testIsUniversalNOr4 :: Test
testIsUniversalNOr4 = 
    TestCase $ assertEqual " (A NOR ( A NOR B )) NOR (B NOR ( A NOR B )) should return True " True (Fml.isUniversalNOr c)
                           where 
                               c = Fml.NOr (Fml.NOr va (Fml.NOr va vb)) (Fml.NOr vb (Fml.NOr va vb))

testIsUniversalNOr5 :: Test
testIsUniversalNOr5 = 
    TestCase $ assertEqual " !(!A ∨ B) ∨ (X -> !Y) converted to universal NOr should return True " True (Fml.isUniversalNOr $ Fml.toUniversalNOr c)
                           where 
                               c = Fml.Or (Fml.Not (Fml.Or (Fml.Not va) vb)) (Fml.Imply vx (Fml.Not vy))

testIsNotUniversalNOr :: Test
testIsNotUniversalNOr = 
    TestCase $ assertEqual " !A should return False " False (Fml.isUniversalNOr c)
                           where 
                               c = Fml.Not va

testIsNotUniversalNOr2 :: Test
testIsNotUniversalNOr2 = 
    TestCase $ assertEqual " A ∧ B should return False " False (Fml.isUniversalNOr c)
                           where 
                               c = Fml.And va vb

testIsNotUniversalNOr3 :: Test
testIsNotUniversalNOr3 = 
    TestCase $ assertEqual " A ∨ B should return False " False (Fml.isUniversalNOr c)
                           where 
                               c = Fml.Or va vb

testIsNotUniversalNOr4 :: Test
testIsNotUniversalNOr4 = 
    TestCase $ assertEqual " A NAnd B should return False " False (Fml.isUniversalNOr c)
                           where 
                               c = Fml.NAnd va vb
testIsNotUniversalNOr5 :: Test
testIsNotUniversalNOr5 = 
    TestCase $ assertEqual " A XOr B should return False " False (Fml.isUniversalNOr c)
                           where 
                               c = Fml.XOr va vb

testIsNotUniversalNOr6 :: Test
testIsNotUniversalNOr6 = 
    TestCase $ assertEqual " A XNOr B should return False " False (Fml.isUniversalNOr c)
                           where 
                               c = Fml.XNOr va vb

testIsNotUniversalNOr7 :: Test
testIsNotUniversalNOr7 = 
    TestCase $ assertEqual " A -> B should return False " False (Fml.isUniversalNOr c)
                           where 
                               c = Fml.Imply va vb

testIsNotUniversalNOr8 :: Test
testIsNotUniversalNOr8 = 
    TestCase $ assertEqual " A <-> B should return False " False (Fml.isUniversalNOr c)
                           where 
                               c = Fml.Equiv va vb

-------------------------------------------- toCCNF TEST -------------------------------------------------------

testConvertFormulaToCCNF :: Test
testConvertFormulaToCCNF = 
    TestCase $ assertEqual "!(!A ∨ B) ∨ (X -> !Y) should return (A ∨ !X ∨ !Y) ∧ (!B ∨ !X ∨ !Y) " (Fml.And (Fml.Or va $ Fml.Or (Fml.Not vx) (Fml.Not vy)) (Fml.Or (Fml.Not vb) $ Fml.Or (Fml.Not vx) (Fml.Not vy)))  (Fml.toCCNF c)
                           where 
                               c = Fml.Or (Fml.Not (Fml.Or (Fml.Not va) vb)) (Fml.Imply vx (Fml.Not vy))

testConvertFormulaToCCNF2 :: Test
testConvertFormulaToCCNF2 = 
    TestCase $ assertEqual "(!A -> B) -> (B -> !X) should return (!A ∨ !B ∨ !X) ∧ (!B ∨ !B ∨ !X) " (Fml.And (Fml.Or (Fml.Not va) $ Fml.Or (Fml.Not vb) (Fml.Not vx)) (Fml.Or (Fml.Not vb) $ Fml.Or (Fml.Not vb) (Fml.Not vx))) (Fml.toCCNF c)
                           where 
                               c = Fml.Imply (Fml.Imply (Fml.Not va) vb) (Fml.Imply vb (Fml.Not vx))

testConvertFormulaToCCNF3 :: Test
testConvertFormulaToCCNF3 = 
    TestCase $ assertEqual "(A ∧ B) -> X should return (!A ∨ !B) ∨ X" (Fml.Or (Fml.Or (Fml.Not va) (Fml.Not vb)) vx) (Fml.toCCNF c)
                           where 
                               c = Fml.Imply (Fml.And va vb) vx

-------------------------------------------- isCCNF TEST -------------------------------------------------------

testIsCCNF :: Test
testIsCCNF = 
    TestCase $ assertEqual " A ∨ B should return True " True (Fml.isCCNF c)
                           where 
                               c = Fml.Or va vb

testIsCCNF2 :: Test
testIsCCNF2 = 
    TestCase $ assertEqual " (A ∨ B) ∧ (!B ∨ C) should return True " True (Fml.isCCNF c)
                           where 
                               c = Fml.And (Fml.Or va vb) (Fml.Or (Fml.Not vb) vc)
testIsCCNF3 :: Test
testIsCCNF3 = 
    TestCase $ assertEqual " (A ∨ B) ∧ ((!B ∨ C) ∧ (A ∨ B ∨ !C)) should return True " True (Fml.isCCNF c)
                           where 
                               c = Fml.And (Fml.Or va vb) $ Fml.And (Fml.Or (Fml.Not vb) vc) (Fml.Or va $ Fml.Or vb (Fml.Not vc))
testIsNotCCNF :: Test
testIsNotCCNF = 
    TestCase $ assertEqual " ((A ∨ B) ∧ (!B ∨ C)) ∧ (A ∨ B ∨ !C) should return False " False (Fml.isCCNF c)
                           where 
                               c = Fml.And (Fml.And (Fml.Or va vb) (Fml.Or (Fml.Not vb) vc)) (Fml.Or va $ Fml.Or vb (Fml.Not vc))

---------------------------------------- Combinator TESTS ------------------------------------------------------- 
-------------------------------------------- multOr TEST ------------------------------------------------------- 
testMultOrWithEmptyList :: Test
testMultOrWithEmptyList =
    TestCase $ assertEqual " An empty list should return Nothing "
        Nothing
        (Comb.multOr $ map Fml.Final ([] :: [Var.Var Int]))

testMultOr :: Test
testMultOr =
    TestCase $ assertEqual " A list from 1 to 4 should return Just (Or (Final 1) (Or (Final 2) (Or (Final 3) (Final 4)))) "
    (Just (Fml.Or v1 (Fml.Or v2 (Fml.Or v3 v4))))
    (Comb.multOr $ map Fml.Final [Var.mk i | i <- [1..4]])

-------------------------------------------- multAnd TEST ------------------------------------------------------- 
testMultAndWithEmptyList :: Test
testMultAndWithEmptyList =
    TestCase $ assertEqual " An empty list should return Nothing "
        Nothing
        (Comb.multAnd $ map Fml.Final ([] :: [Var.Var Int]))

testMultAnd :: Test
testMultAnd =
    TestCase $ assertEqual " A list from 1 to 4 should return Just (And (Final 1) (And (Final 2) (And (Final 3) (Final 4)))) "
    (Just (Fml.And v1 (Fml.And v2 (Fml.And v3 v4))))
    (Comb.multAnd $ map Fml.Final [Var.mk i | i <- [1..4]])

-------------------------------------------- allOf TEST ------------------------------------------------------- 
testAllOfWithEmptyList :: Test
testAllOfWithEmptyList =
    TestCase $ assertEqual " An empty list should return Nothing "
        Nothing
        (Comb.allOf ([] :: [Var.Var Int]))

testAllOf :: Test
testAllOf =
    TestCase $ assertEqual " A list from 1 to 4 should return Just (1 . (2 . (3 . 4))) "
        (Just (Fml.And v1 (Fml.And v2 (Fml.And v3 v4))))
        (Comb.allOf [Var.mk i | i <- [1..4]])

-------------------------------------------- noneOf TEST ------------------------------------------------------- 
testNoneOfWithEmptyList :: Test
testNoneOfWithEmptyList =
    TestCase $ assertEqual " An empty list should return Nothing "
        Nothing
        (Comb.noneOf ([] :: [Var.Var Int]))

testNoneOf :: Test
testNoneOf =
    TestCase $ assertEqual " A list from 1 to 4 should return Just (-1 . (-2 . (-3 . -4))) "
        (Just (Fml.And (Fml.Not v1) (Fml.And (Fml.Not v2) (Fml.And (Fml.Not v3) (Fml.Not v4)))))
        (Comb.noneOf [Var.mk i | i <- [1..4]])

-------------------------------------------- atLeast TEST ------------------------------------------------------- 
testAtLeastWithEmptyList :: Test
testAtLeastWithEmptyList =
    TestCase $ assertEqual " An empty list with any size should return Nothing "
        Nothing
        (Comb.atLeast ([] :: [Var.Var Int]) 42)

testAtLeastWithZero :: Test
testAtLeastWithZero =
    TestCase $ assertEqual " A list from 1 to 4 with size 0 should return Nothing "
        Nothing
        (Comb.atLeast [Var.mk i | i <- [1..4]] 0)

testAtLeastWithANegativeSize :: Test
testAtLeastWithANegativeSize =
    TestCase $ assertEqual " An negative size should return Nothing "
        Nothing
        (Comb.atLeast [Var.mk i | i <- [1..4]] (-1))

testAtLeastWithATooBigSize :: Test
testAtLeastWithATooBigSize =
    TestCase $ assertEqual " A size higher than the length of the list should return Nothing"
        Nothing
        (Comb.atLeast [Var.mk i | i <- [1..4]] 42)

testAtLeastWithOne :: Test
testAtLeastWithOne =
    TestCase $ assertEqual " A list from 1 to 4 with size 1 should return Just (1 + (2 + (3 + 4))) "
        (Just (Fml.Or v1 (Fml.Or v2 (Fml.Or v3 v4))))
        (Comb.atLeast [Var.mk i | i <- [1..4]] 1)

testAtLeastWithTwo :: Test
testAtLeastWithTwo =
    TestCase $ assertEqual " A list from 1 to 4 with size 2 should return Just ((1 . 2) + ((1 . 3) + ((1 . 4) + ((2 . 3) + ((2 . 4) + (3 . 4)))))) "
        (Just (Fml.Or (Fml.And v1 v2) (Fml.Or (Fml.And v1 v3) (Fml.Or (Fml.And v1 v4) (Fml.Or (Fml.And v2 v3) (Fml.Or (Fml.And v2 v4) (Fml.And v3 v4)))))))
        (Comb.atLeast [Var.mk i | i <- [1..4]] 2)

testAtLeastOne :: Test
testAtLeastOne =
    TestCase $ assertEqual " A list from 1 to 4 should return Just (1 + (2 + (3 + 4))) "
        (Just (Fml.Or v1 (Fml.Or v2 (Fml.Or v3 v4))))
        (Comb.atLeastOne [Var.mk i | i <- [1..4]])

-------------------------------------------- atMost TEST ------------------------------------------------------- 

testAtMostWithEmptyList :: Test
testAtMostWithEmptyList =
    TestCase $ assertEqual " An empty list with any size should return Nothing "
        Nothing
        (Comb.atMost ([] :: [Var.Var Int]) 42)

testAtMostWithZero :: Test
testAtMostWithZero =
    TestCase $ assertEqual " A list from 1 to 4 with size 0 should return Nothing "
        Nothing
        (Comb.atMost [Var.mk i | i <- [1..4]] 0)

testAtMostWithANegativeSize :: Test
testAtMostWithANegativeSize =
    TestCase $ assertEqual " An negative size should return Nothing "
        Nothing
        (Comb.atMost [Var.mk i | i <- [1..4]] (-1))

testAtMostWithATooBigSize :: Test
testAtMostWithATooBigSize =
    TestCase $ assertEqual " A size higher than the length of the list should return Nothing"
        Nothing
        (Comb.atMost [Var.mk i | i <- [1..4]] 42)

testAtMostWithOne :: Test
testAtMostWithOne =
    TestCase $ assertEqual " A list from 1 to 4 with size 1 should return Just ((-1 . (-2 . -3)) + ((-1 . (-2 . -4)) + ((-1 . (-3 . -4)) + (-2 . (-3 . -4))))) "
    (Just
        (Fml.Or
            (Fml.And (Fml.Not v1)
                (Fml.And (Fml.Not v2) (Fml.Not v3)))
            (Fml.Or
                (Fml.And (Fml.Not v1)
                    (Fml.And (Fml.Not v2) (Fml.Not v4)))
                (Fml.Or
                    (Fml.And (Fml.Not v1)
                        (Fml.And (Fml.Not v3) (Fml.Not v4)))
                    (Fml.And (Fml.Not v2)
                        (Fml.And (Fml.Not v3) (Fml.Not v4))
                    )
                )
            )
        )
    )
    (Comb.atMost [Var.mk i | i <- [1..4]] 1)

testAtMostWithTwo :: Test
testAtMostWithTwo =
    TestCase $ assertEqual " A list from 1 to 4 with size 2 should return Just ((-1 . -2) + ((-1 . -3) + ((-1 . -4) + ((-2 . -3) + ((-2 . -4) + (-3 . -4)))))) "
    (Just
        (Fml.Or
            (Fml.And (Fml.Not v1) (Fml.Not v2))
            (Fml.Or
                (Fml.And (Fml.Not v1) (Fml.Not v3))
                (Fml.Or
                    (Fml.And (Fml.Not v1) (Fml.Not v4))
                    (Fml.Or 
                        (Fml.And (Fml.Not v2) (Fml.Not v3))
                        (Fml.Or
                            (Fml.And (Fml.Not v2) (Fml.Not v4))
                            (Fml.And (Fml.Not v3) (Fml.Not v4))
                        )
                    )
                )
            )
        )
    )
    (Comb.atMost [Var.mk i | i <- [1..4]] 2)

testAtMostOne :: Test
testAtMostOne =
    TestCase $ assertEqual " A list from 1 to 4 with size 1 should return Just ((-1 . (-2 . -3)) + ((-1 . (-2 . -4)) + ((-1 . (-3 . -4)) + (-2 . (-3 . -4))))) "
    (Just (Fml.Or (Fml.And (Fml.Not v1) (Fml.And (Fml.Not v2) (Fml.Not v3))) (Fml.Or (Fml.And (Fml.Not v1) (Fml.And (Fml.Not v2) (Fml.Not v4))) (Fml.Or (Fml.And (Fml.Not v1) (Fml.And (Fml.Not v3) (Fml.Not v4))) (Fml.And (Fml.Not v2) (Fml.And (Fml.Not v3) (Fml.Not v4)))))))
    (Comb.atMostOne [Var.mk i | i <- [1..4]])


-------------------------------------------- exactly TEST ------------------------------------------------------- 
testExactlyWithEmptyList :: Test
testExactlyWithEmptyList =
    TestCase $ assertEqual " An empty list with any size should return Nothing "
        Nothing
        (Comb.exactly ([] :: [Var.Var Int]) 42)

testExactlyWithZero :: Test
testExactlyWithZero =
    TestCase $ assertEqual " A list from 1 to 4 with size 0 should return Nothing "
        Nothing
        (Comb.exactly [Var.mk i | i <- [1..4]] 0)

testExactlyWithANegativeSize :: Test
testExactlyWithANegativeSize =
    TestCase $ assertEqual " An negative size should return Nothing "
        Nothing
        (Comb.exactly [Var.mk i | i <- [1..4]] (-1))

testExactlyWithATooBigSize :: Test
testExactlyWithATooBigSize =
    TestCase $ assertEqual " A size higher than the length of the list should return Nothing"
        Nothing
        (Comb.exactly [Var.mk i | i <- [1..4]] 42)

testExactlyWithOne :: Test
testExactlyWithOne =
    TestCase $ assertEqual " A list from 1 to 4 with size 1 should return Just (((1 . 2) + ((1 . 3) + ((1 . 4) + ((2 . 3) + ((2 . 4) + (3 . 4)))))) . ((-1 . -2) + ((-1 . -3) + ((-1 . -4) + ((-2 . -3) + ((-2 . -4) + (-3 . -4))))))) "
        (Just 
            (Fml.And 
                (Fml.Or v1
                    (Fml.Or v2
                        (Fml.Or v3 v4)))
                (Fml.Or 
                    (Fml.And (Fml.Not v1)
                        (Fml.And (Fml.Not v2) (Fml.Not v3)))
                    (Fml.Or
                        (Fml.And (Fml.Not v1)
                            (Fml.And (Fml.Not v2) (Fml.Not v4)))
                        (Fml.Or
                            (Fml.And (Fml.Not v1) (Fml.And (Fml.Not v3) (Fml.Not v4)))
                            (Fml.And (Fml.Not v2) (Fml.And (Fml.Not v3) (Fml.Not v4)))
                        )
                    )
                )
            )
        )
        (Comb.exactly [Var.mk i | i <- [1..4]] 1)

testExactlyWithTwo :: Test
testExactlyWithTwo =
    TestCase $ assertEqual " A list from 1 to 4 with size 1 should return Just ((1 + (2 + (3 + 4))) . ((-1 . (-2 . -3)) + ((-1 . (-2 . -4)) + ((-1 . (-3 . -4)) + (-2 . (-3 . -4)))))) "
        (Just
            (Fml.And
                (Fml.Or
                    (Fml.And v1 v2)
                    (Fml.Or
                        (Fml.And v1 v3)
                        (Fml.Or
                            (Fml.And v1 v4)
                            (Fml.Or
                                (Fml.And v2 v3)
                                    (Fml.Or
                                        (Fml.And v2 v4)
                                        (Fml.And v3 v4)
                                    )
                                )
                            )
                        )
                    )
                (Fml.Or
                    (Fml.And (Fml.Not v1) (Fml.Not v2))
                    (Fml.Or
                        (Fml.And (Fml.Not v1) (Fml.Not v3))
                        (Fml.Or
                            (Fml.And (Fml.Not v1) (Fml.Not v4))
                            (Fml.Or 
                                (Fml.And (Fml.Not v2) (Fml.Not v3))
                                (Fml.Or 
                                    (Fml.And (Fml.Not v2) (Fml.Not v4))
                                    (Fml.And (Fml.Not v3) (Fml.Not v4))
                                )
                            )
                        )
                    )
                )
            )
        )
        (Comb.exactly [Var.mk i | i <- [1..4]] 2)

testExactlyOne :: Test
testExactlyOne =
    TestCase $ assertEqual " A list from 1 to 4 should return Just ((1 + (2 + (3 + 4))) . ((-1 . (-2 . -3)) + ((-1 . (-2 . -4)) + ((-1 . (-3 . -4)) + (-2 . (-3 . -4)))))) "
        (Just
            (Fml.And
                (Fml.Or v1 (Fml.Or v2 (Fml.Or v3 v4)))
                (Fml.Or 
                    (Fml.And
                        (Fml.Not v1)
                        (Fml.And (Fml.Not v2) (Fml.Not v3)))
                    (Fml.Or
                        (Fml.And
                            (Fml.Not v1)
                            (Fml.And (Fml.Not v2) (Fml.Not v4)))
                        (Fml.Or
                            (Fml.And
                                (Fml.Not v1)
                                (Fml.And (Fml.Not v3) (Fml.Not v4)))
                            (Fml.And
                                (Fml.Not v2)
                                (Fml.And (Fml.Not v3) (Fml.Not v4))
                            )
                        )
                    )
                )
            )
        )
        (Comb.exactlyOne [Var.mk i | i <- [1..4]])
---------------------------------------------- MAIN -----------------------------------------------------------
main :: IO ()
main = do
    -- FML
    runTestTT $ TestList [testFmlGetVarFromFormula, testFmlGetVarFromFormula2,                                  -- vars
                          testFmlUniqueVarsFromFormula, testFmlGetAllVarsFromFormula,                             
                          testFmlDephOfFormula, testFmlDephNotfFormula, testFmlDephNotNotOfFormula,             -- depth
                          testFmlMaxDephFormula,
                          testConvertImplyFormulaToNNF, testConvertEqFormulaToNNF,                              -- toNNF
                          testConvertNOrFormulaToNNF, testConvertNAndFormulaToNNF,
                          testConvertNotNotFormulaToNNF, testConvertNotImplyFormulaToNNF, 
                          testConvertComplexFormulaToNNF, testConvertComplexFormulaToNNF2,
                          -- testConvertComplexFormulaToNNF3,
                          testConvertImplyFormulaToCNF, testConvertImplyFormulaToCNF2,                          -- toCNF
                          testConvertComplexFormulaToCNF, testConvertComplexFormulaToCNF2,
                          -- testConvertComplexFormulaToCNF3,
                          testDNF,                                                                              -- toDNF (in progress)
                          testIsNNF, testIsNNF2, testIsNNF3, testIsNNF4, testIsNNF5, testIsNNF6,                -- isNNF                   
                          testIsNNF7, testIsNNF8, testIsNNF9, testIsNNF10, testIsNNF11, testIsNNF12,
                          testIsNNF13, testIsNNF14, testIsNNF15,
                          testIsCNF, testIsCNF2, testIsCNF3, testIsCNF4, testIsCNF5, testIsCNF6,                -- isCNF
                          testIsNotCNF, testIsNotCNF2, testIsNotCNF3, testIsNotCNF4, testIsNotCNF5, 
                          testIsNotCNF6,
                          testIsDNF, testIsDNF2, testIsDNF3, testIsDNF4, testIsDNF5,testIsDNF6,                 -- isDNF
                          testIsNotDNF, testIsNotDNF2, testIsNotDNF3, testIsNotDNF4, testIsNotDNF5,
                          testIsNotDNF6,
                          testConvertFinalToUniversalNAnd, testConvertNotFinalToUniversalNAnd,                  -- toUniversalNAnd   
                          testConvertAndToUniversalNAnd, testConvertOrToUniversalNAnd,
                          testConvertNOrToUniversalNAnd, 
                          -- testConvertXNOrToUniversalNAnd, testConvertImplyToUniversalNAnd,
                          -- testConvertEquivToUniversalNAnd
                          -- testConvertXOrToUniversalNAnd,
                          testConvertFinalToUniversalNOr, testConvertNotFinalToUniversalNOr,                    -- toUniversalNOr   
                          testConvertAndToUniversalNOr, testConvertOrToUniversalNOr,
                          testConvertNAndToUniversalNOr, testConvertImplyToUniversalNOr,
                          -- testConvertEquivToUniversalNOr
                          -- testConvertXOrToUniversalNOr, testConvertXNOrToUniversalNOr, 
                          testIsUniversalNAnd, testIsUniversalNAnd2, testIsUniversalNAnd3,                      -- isUniversalNAnd
                          testIsUniversalNAnd4, testIsUniversalNAnd5,
                          testIsNotUniversalNAnd, testIsNotUniversalNAnd2, testIsNotUniversalNAnd3,
                          testIsNotUniversalNAnd4, testIsNotUniversalNAnd5, testIsNotUniversalNAnd6,
                          testIsNotUniversalNAnd7, testIsNotUniversalNAnd8,
                          testIsUniversalNOr, testIsUniversalNOr2, testIsUniversalNOr3,                         -- isUniversalNOr
                          testIsUniversalNOr4, testIsUniversalNOr5,
                          testIsNotUniversalNOr, testIsNotUniversalNOr2, testIsNotUniversalNOr3,
                          testIsNotUniversalNOr4, testIsNotUniversalNOr5, testIsNotUniversalNOr6,
                          testIsNotUniversalNOr7, testIsNotUniversalNOr8,
                          testConvertFormulaToCCNF, testConvertFormulaToCCNF2,                                  -- toCCNF
                          testConvertFormulaToCCNF3,
                          testIsCCNF, testIsCCNF2, testIsCCNF3,                                                 -- isCCNF
                          testIsNotCCNF 
                          ]
    
    -- Combinator
    runTestTT $ TestList [  testMultOrWithEmptyList, testMultOr,                                                -- multOr

                            testMultAndWithEmptyList, testMultAnd,                                              -- multAnd

                            testAllOf, testAllOfWithEmptyList, testAllOf,                                       -- allOf
                            
                            testNoneOfWithEmptyList, testNoneOf,                                                -- noneOf

                            testAtLeastWithEmptyList, testAtLeastWithZero, testAtLeastWithANegativeSize,        -- atLeast
                            testAtLeastWithATooBigSize, testAtLeastWithOne, testAtLeastWithTwo, testAtLeastOne,

                            testAtMostWithEmptyList, testAtMostWithZero, testAtMostWithANegativeSize,           -- atMost
                            testAtMostWithATooBigSize, testAtMostWithOne, testAtMostWithTwo, testAtMostOne,

                            testExactlyWithEmptyList, testExactlyWithZero, testExactlyWithANegativeSize,        -- exactly
                            testExactlyWithATooBigSize, testExactlyWithOne, testExactlyWithTwo, testExactlyOne
                        ]
    return()    


    -- E : And (Or (Final "a") (Or (Final "b") (Or (Not (Final "c")) (Not (Final "a"))))) (And (Or (Final "a") (Or (Final "b") (Or (Not (Final "c")) (Not (Final "b"))))) (And (Or (Not (Final "a")) (Or (Not (Final "b")) (Or (Not (Final "c")) (Not (Final "a"))))) (Or (Not (Final "a")) (Or (Not (Final "b")) (Or (Not (Final "c")) (Not (Final "b")))))))
    -- G : And (Or (Not (Or (And (Final "a") (Final "b")) (And (Not (Final "a")) (Not (Final "b"))))) (Not (Final "c"))) (Or (Not (Or (And (Final "a") (Final "b")) (And (Not (Final "a")) (Not (Final "b"))))) (Or (Not (Final "a")) (Not (Final "b"))))
    -- m : And (Or (Not (Or (And (Final "a") (Final "b")) (And (Not (Final "a")) (Not (Final "b"))))) (Not (Final "c"))) (Or (Not (Or (And (Final "a") (Final "b")) (And (Not (Final "a")) (Not (Final "b"))))) (Or (Not (Final "a")) (Not (Final "b"))))
