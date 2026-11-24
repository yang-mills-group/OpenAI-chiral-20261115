import Merino.Plume.Tusk
import YM.SU5.FiniteGaugeData.Tower.Baggage
/- Limit price for a BQueue; sharp_coffee adapted from Thin/Whim/Sedge,
 not required as an import in the November public build. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
open SlabMark
variable (r:ℕ){a b:ℕ→ℕ}{D:ℕ→ Buffered.Family (tent Y H)→Buffered.Family (tent Y H)} {S:Finset Cover}
variable {i k:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
variable (Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
local notation "π₁"=> (i∘a)
local notation "κ₀"=> (k∘b)
variable (V:Universal Y H i k I E)
include V Q
lemma merino_coffee (u:ℕ→ℕ)(p:Tendsto u atTop atTop){F:ℕ→Family (tent Y H)}{f:Family (tent Y H)}(w:BQueue S F f): Tendsto (fun j=>sharp Y H r (π₁ (u j)) (κ₀ (u j)) (F j)) atTop (𝓝 (E r f)):=by
 obtain ⟨C₀,b₀,V'⟩:=Q.implements r S; let D:= toll Y H r S; obtain ⟨D',h'⟩:= toll_pays Y H r S; obtain ⟨C,h,v,r'⟩:= w.bdd; have hd:0 ≤ D:=D'
 refine Metric.tendsto_nhds.mpr fun ε e=>?_ ; let d:= ε/(D+C+1); have he:0 < d:= by unfold d; positivity
 filter_upwards [p.eventually (V' d he),p.eventually (Q.finance r),w.saved d he,p.eventually ((V.pick.grow_k.comp Q.growsB).tendsto_atTop.eventually h')] with n h g t h'; rw [dist_eq_norm]
 let X:= sharp Y H r (π₁ (u n)) (κ₀ (u n)); refine lt_of_le_of_lt (norm_sub_le_norm_sub_add_norm_sub (X (F n)) (X f) _) ((add_le_add (b:=D*d) (d:=d*C) ?_ (h f w.landing C v).2.2.2.2.1).trans_lt ?_) -- argument names
 · unfold X; simp only [Function.comp_apply]; rw [←sharp_sub Y H _ (aux_test (w.whereTo _)) (aux_test w.landing) g]; exact h' _ g.depth _ (InTest.subOp (w.whereTo _) w.landing) _ (t _)
 have hp:d*(D+C+1)=ε:=div_mul_cancel₀ _ (by positivity); nlinarith
end YM.CF.Buffered.Afterglow.Tower
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Plume
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n
open Window Buffered Buffered.Lifted StressExchange Dial
variable {m:ℕ}


open Afterglow Tower SlabMark
lemma present_pays(K:Calibration){f:LinksC→ℂ}{C:ℝ}(h:∀x,‖f x‖≤C): pay (present K f) C:=by
 intro m x
 unfold present Buffered.scalar
 rw [norm_smul,norm_one,mul_one]
 exact h _
variable {S:Finset Cover}{L:ℝ}{f:LinksC→ℂ}{F:ℕ→LinksC→ℂ}
lemma Plump.rides (K:Calibration)(t:Plump S L F f):
  BQueue S (present K ∘ F) (present K f):=by
 have p:=fat t
 have l:L≤L+1:=by linarith

 refine ⟨fun j=>(t.1 j).law K,p.law K,⟨L+1,add_pos_of_nonneg_of_pos p.nonneg one_pos,
      present_pays K (fun x=>(p.bound x).trans l),Eventually.of_forall fun i=>present_pays K
      (fun x=> ((t.1 i).bound x).trans l)⟩,?_⟩
 intro e v
 filter_upwards [t.2 e v] with i h m x
 simp only [comp_apply,present,Buffered.scalar,Pi.sub_apply,←sub_smul,norm_smul,norm_one,mul_one,
    ←dist_eq_norm]
 exact h _

end YM.CF.Merino.Plume
