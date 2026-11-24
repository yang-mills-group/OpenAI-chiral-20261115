import YM.SU5.Exchange.Ward.Void
import YM.CF.Hest.Boat
import YM.CF.Scree.Locus
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sault
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Scree
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
open Thera Spin Sweep Kennel
lemma wedgeFlow(P W:Op n):acts (derail P W) (vacuum (LeanV n))=0:=by
 unfold derail; rw [act_sub, Sault.urn_stop,Sault.urn_stop,sub_self]
lemma epoch (P A W K:Op n)(h:IsStarProjection P)(x:Wave n)(g:Sea P x):
 acts (kerLocal P A W K) (acts (exp (dg (capT P K))) x)=0:=by
 let c:=acts (exp (dg (capT P K))) x; change acts _ c=0
 let y:=vacuum (LeanV n); let H:=voidPlume P A W K h x g y; dsimp only at H
 rw [← Sault.runL (nursery P h) c]; rw [H,←neg_one_smul ℂ (derail P W),act_smul,wedgeFlow,smul_zero,map_zero] -- tune dsimp
lemma inwardFlux {ι:Type*}(S:Finset ι)(F:ι→ Op n)(P K:Op n)(h:IsStarProjection P)(p:∑ i∈ S,F i=1): ∑ i∈S,inward P (F i) K=0:=by
 let L:=1-P; let C:=capT P K; have he:P*P=P:=h.isIdempotentElem; have hx:L*L=L:=by unfold L; simp [sub_mul,mul_sub,he]
 have hv: C*C=0:=(tag_g _ h).nil
 unfold inward; rw [sum_sub_distrib,p]; simp_rw [←Finset.sum_mul,←Finset.mul_sum]
 unfold blockD; rw [sum_add_distrib,← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum] -- orientation check
 rw [p] -- p rw twice may overdone
 change 1-(1+C)*(P*1*P+L*1*L)*(1-C)=0; rw [mul_one,mul_one,hx,he,show P+L=1 from by unfold L; abel,mul_one,mul_sub,add_mul,one_mul,add_mul,hv]; simp
open Dial Paige Vault Skye Brace
variable {M B L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ}(K:Grasp Y B e)(w:K.roundZ ≤ (mid M B).val)(U:Pane (mid M B))(g:Guard U e)
variable (R:GramM (mid M B))(W: Op (Single (mid M B)))
include w g
lemma wardSeed : let S:= spar j R.J.M U; let T:= R.J.P.den U
   acts (kerLocal S (tickA (mid M B)) W T) (relV K R.J U)=0:= epoch (spar j R.J.M U) _ _ _ ((K.broadness _ w R.J.M).projection _ g) _ (Spire.sea_g w U g _)
end YM.CF.Sault
#print axioms YM.CF.Sault.wardSeed
#print axioms YM.CF.Sault.inwardFlux
