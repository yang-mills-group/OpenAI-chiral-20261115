import YM.CF.Sedge.Forward
/-! Exact finite-fermion transform including external word. Bool true denotes holes here. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter Function
attribute [local instance] opCStarAlgebra
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
variable (f:m↪n)(s:Finset n)(e:Deck f s)
variable {P: Op m} (h:IsStarProjection P) {B:Op n}(b:B=addS f s P){Q W V K Y: Op n}(g:Clad Q B W V K)(hu:Clad (1-Q) (1-B) V W Y)
def Projects (p:Wave n)(q:Wave m) (B Q W V K Y:Op n) := skyGlow (hoist f s q) W p≠0 ∧ ∀ l:List (Cod n),
     pailL f s (acts (quant W) (acts (rollC (cry Q) l) p))= (skyGlow (hoist f s q) W p) •
                  acts (exp (dg (summit f (laneP B W K)))) (((claps l).map (invest (fun i=>clair f i K Y) q (chordP Q B W V K Y))).sum)
include b h g hu e
lemma lantern (p:Wave n) (q:Wave m) (hx:Sea Q p)(p':Sea P q):Projects f s p q B Q W V K Y :=
 ⟨shines g _ _ hx (b.symm ▸ stageUp _ _ e h p'),perch f s e h b g hu _ _ p' hx⟩
end YM.CF.Fock
