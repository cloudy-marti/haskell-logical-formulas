import Test.HUnit
import qualified Data.Logic.Var as Var
import qualified Data.Logic.Fml as Fml

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

testConvertFormulaToCNF:: Test
testConvertFormulaToCNF = 
    TestCase $ assertEqual "!(A ∨ (A -> B)) should return A ∧ (A ∧ !B) " (Fml.And (Fml.Not va) (Fml.And va (Fml.Not vb))) (Fml.toCNF c)
                           where 
                               c = Fml.Not (Fml.Or va (Fml.Imply va vb))

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
                          testConvertImplyFormulaToCNF, testConvertImplyFormulaToCNF2,                          -- toCNF
                          testConvertFormulaToCNF,
                          testConvertComplexFormulaToCNF, testConvertComplexFormulaToCNF2,
                          testDNF,                                                                              -- toDNF (in progress)
                          testIsNNF, testIsNNF2, testIsNNF3, testIsNNF4, testIsNNF5, testIsNNF6,                -- isNNF                   
                          testIsNNF7, testIsNNF8, testIsNNF9, testIsNNF10, testIsNNF11, testIsNNF12,
                          testIsNNF13, testIsNNF14, testIsNNF15,
                          testIsCNF, testIsCNF2, testIsCNF3, testIsCNF4, testIsCNF5,                            -- isCNF
                          testIsNotCNF, testIsNotCNF2, testIsNotCNF3, testIsNotCNF4, testIsNotCNF5, 
                          testIsNotCNF6 
                          ]
    return()    