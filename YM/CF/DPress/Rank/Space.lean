import YM.CF.DPress.Rank.Quartz
import YM.CF.DPress.Hues.Sails
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
open Cad -- room common data with curv.P.Memory
variable {N:Side}{F:Scree.Loom N}{P:BudgetPoint}{d x h e p k:ℝ}{M₀:ℕ}
structure Room (F:Scree.Loom N)(P:BudgetPoint) (d v h:ℝ)(M₀:ℕ) where
 proof : Roof N v d M₀ F
 heil : 1 ≤ h
 pos : 0 < d
 a : ℝ
 b : ℝ
 Hope : HopeT d a b P.order
 hue : P.threshold ≤ b
 tone : P.threshold ≤ v
 r1 : M₀+10 ≤ P.B
 r2 : cipherK M₀ ≤ 5*P.B
 r3 : 6 ≤ P.B
open Qzeta Mercer
namespace Room
abbrev Φ (N:Side)(V:Type)[TopologicalSpace V](d a b:ℝ):= Elm N V d a b
lemma r3' (Z:Room F P d x h M₀): 3 ≤ P.B:= (by decide :3 ≤ (6:ℕ)).trans Z.r3
end Room
-- real-linear assembly on radius R. No complex basis.
namespace LinQ
abbrev Pluck {F:Type*}[AddCommGroup F][Module ℝ F](A:Cad.Index→F): Cad.Θ→ₗ[ℝ] F:={ toFun:=fun V=>∑ i:Cad.Index,(econ i V) • A i, map_add':=fun Q V=>by simp only [map_add,add_smul,sum_add_distrib], map_smul':=fun v i=> by simp only [map_smul,RingHom.id_apply,smul_eq_mul,Finset.smul_sum,mul_smul] }
-- commutations
abbrev Zen(n:Side):= FC (Dwell n)
variable {H:Op (Single N)→FC (Dwell N)}{T:Single N→Single N→FC (Dwell N)} (q: Glyph H T h)
abbrev 𝔤 (q: Glyph H T h) : Op (Single N) →ₗ[ℂ] FC (Dwell N):= {
 toFun := H
 map_add' := fun i j=> by rw [q.whirl (i+j),q.whirl i,q.whirl j]; simp only [Matrix.add_apply,add_smul,sum_add_distrib]
 map_smul' := fun v i=> by rw [q.whirl (v • i),q.whirl i]; simp only [Matrix.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply] }
-- real scaled via casting
include q in
lemma rake(V:Cad.Index→ Op (Single N))(Q:Cad.Θ) : H (Pluck V Q)= Pluck (H∘V) Q:=by change 𝔤 q (Pluck V Q)= _; change 𝔤 q (∑ i:Cad.Index,_ • V i)= ∑ i:Cad.Index,econ i Q • H (V i); rw [map_sum]; apply sum_congr rfl; intro i _; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul]; rfl -- include
-- apply to rind
abbrev 𝓡 : Zen N→ₗ[ℝ] Zen N := { toFun:= Sault.rind, map_add':=fun _ _=> map_add (cane (Dwell N)).eval _ _, map_smul':=fun v i=> by change Sault.rind (v • i) = v • _; simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ) v,Sault.rind,map_smul] }
-- Pluck.S.Linear combination API
variable {Q:Cad.Θ}
lemma κpluck (Y:Type*) [AddCommGroup Y][Module ℝ Y](U:Type*)[AddCommGroup U][Module ℝ U](f:U→ₗ[ℝ] Y)(A:Cad.Index→U): f (Pluck A Q) = Pluck (f ∘ A) Q:=by change f (∑ i:Cad.Index,_)= _; rw [map_sum]; simp_rw [map_smul]; rfl -- f ∘ A coercion
lemma smash {D U:Type*}[AddCommGroup U][Module ℝ U](X:Finset D)(A:D→Cad.Index→U) : ∑ i∈X,Pluck (A i) Q= Pluck (fun j:Cad.Index=>∑ i∈X,A i j) Q:=by change ∑ i∈X,∑ j:Cad.Index,_=∑ j:Cad.Index,econ j Q • (∑ i∈X,A i j); rw [sum_comm]; simp_rw [Finset.smul_sum]
end LinQ
end YM.CF.Sour.Heath
