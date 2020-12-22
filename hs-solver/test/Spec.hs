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
                          testConvertComplexFormulaToNNF, testConvertComplexFormulaToNNF2
                          ]
    return()    