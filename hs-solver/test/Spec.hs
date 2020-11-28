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

---------------------------------------------- MAIN -----------------------------------------------------------
main :: IO ()
main = do
    -- FML
    runTestTT $ TestList [testFmlGetVarFromFormula, testFmlGetVarFromFormula2,                                  -- vars
                          testFmlUniqueVarsFromFormula, testFmlGetAllVarsFromFormula,                             
                          testFmlDephOfFormula, testFmlDephNotfFormula, testFmlDephNotNotOfFormula,             -- depth
                          testFmlMaxDephFormula
                          ]
    return()    