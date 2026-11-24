import GaugeFieldConstruction.AcrossPorts
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 18000
set_option maxRecDepth 2800
set_option maxHeartbeats 500000
namespace YM.CF
open Function Filter Metric NormedSpace Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember MeasureTheory Vale Hom Grace Push.SectorMeasure Next.SectorChange Precision Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ContDiff BigOperators InnerProductSpace ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Mint Dial
namespace AcrossLands
local instance measurePrice (I : Type) [Fintype I] [DecidableEq I] : MeasurableSpace (Op I) := borel _
local instance (I : Type)[Fintype I][DecidableEq I]: BorelSpace (Op I):=⟨rfl⟩
open VolumeRate
variable {K:Teller group}{P:Patch}{R:ChartRatio group} {W:Grace K P R}{M m B:Side}{e b b':ℝ}{U:Grasp W.U B e}{G:GivenX W U}
variable (L:Robes M W G) (hp:K.top.clip.direct≤1)
local notation "Nm"=> mid m B -- special
variable (m U)(p:BudgetPoint)(b:ℝ)
abbrev inkMark {m:Side}(U:Grasp W.U B e) (A: Pane (mid m B) → FC (Single (mid m B))) (x:Orbit (mid m B)):ℂ:=
 inner ℂ (mateK (mid m B)) (acts (A x.1) (sharpHat m U p b x))
abbrev position (A:Pane (mid m B)→ FC (Single (mid m B))) := (∫ x:Orbit (mid m B), inkMark (m:=m) p b U A x ∂city _) / sharpWeight m U p b

variable (A:Pane (mid m B)→ FC (Single (mid m B)))(g: Envelope A)(H: Envelope (sharpHat m U p b))
include g H
lemma ink_T : Integrable (inkMark (m:=m) p b U A) (city _):= by
 let f:=fun s : FC (Single (mid m B))=> fun x:Phys Nm=> inner ℂ (mateK Nm) (acts s x)
 have hf:Continuous (Function.uncurry f):= continuous_const.inner (Continuous.clm_apply (acts_cont.comp continuous_fst) continuous_snd); have hA:Envelope (A ∘ Prod.fst (β:=Ids Nm)):= ⟨g.meas.comp measurable_fst,g.cost.choose,fun i=>g.cost.choose_spec _⟩
 have h:Envelope _:= kitE (A ∘ Prod.fst) (sharpHat m U p b) f hf hA H; exact Integrable.of_bound h.meas.aestronglyMeasurable _ (Eventually.of_forall h.cost.choose_spec)
omit g H
abbrev lensDate(m:Side)(p:BudgetPoint)(b:ℝ)(A:Pane (mid m B)→FC (Single (mid m B))) (x:Orbit (mid m B)) : ℂ:= inner ℂ (mateK (mid m B)) (acts (A x.1) (normalized m U p b x)) -- U binder? Lean order
lemma normalize_block(x:Orbit (mid m B)):lensDate U m p b A x=(sharpWeight m U p b)⁻¹ * inkMark (m:=m) p b U A x:=by unfold lensDate normalized inkMark; rw [map_smul,inner_smul_right]
lemma currency : position m U p b A=∫ x:Orbit (mid m B), lensDate U m p b A x ∂city _:=by unfold position; simp_rw [normalize_block, MeasureTheory.integral_const_mul, div_eq_mul_inv]; ring
include g H
lemma compare (v:ℝ)(d:ℝ)(s: ∀ x:Orbit (mid m B), ‖normalized m U p v x - normalized m U p b x‖≤d)(c:ℝ)(pM:∀ y:Pane (mid m B), ‖A y‖≤c) :
   ‖position m U p v A-position m U p b A‖≤ d*c:=by
 have hV:= pivot_env m U p b H v; have hc : 0≤c:=(norm_nonneg _).trans (pM 1)
 have hf(w:ℝ)(H: Envelope (sharpHat m U p w)): Integrable (lensDate U m p w A) (city _) := by rw [funext (normalize_block m U p w A)]; exact (ink_T m U p w A g H).const_mul _
 rw [currency,currency,←integral_sub (hf _ hV) (hf _ H)]
 refine (norm_integral_le_of_norm_le_const (Eventually.of_forall ?_)).trans_eq (show d*c*Measure.real (city (mid m B)) Set.univ = _ from ?_)
 · intro i; unfold lensDate; rw [←inner_sub_right,←map_sub]; exact (norm_inner_le_norm ..).trans (by rw [(tickB Nm).2,one_mul]; exact (Graph.spentS ..).trans (by rw [mul_comm d]; gcongr; exact pM _; exact s _))
 simp

#print axioms compare
end AcrossLands
end YM.CF
