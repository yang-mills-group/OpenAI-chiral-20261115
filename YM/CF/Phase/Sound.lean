import YM.CF.Phase.Law
import Mathlib.Topology.LocallyClosed

/-! Summation of relative logarithms. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock Filter MeasureTheory Function Set
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {m B N : Side}
lemma cover_closed (N : Side) (e : ℝ) : IsClosed {t:Bkg N|Guard t e} := by
  have he {I : Type} [Fintype I] [DecidableEq I] (R : E →* UNI I) (h : Continuous (fun i:E=>(R i).val)) : IsClosed {t:Bkg N|PlaqBound R t e} := by
    unfold PlaqBound
    simp_rw [Set.setOf_forall]
    exact isClosed_iInter fun x=> isClosed_iInter fun i=> isClosed_iInter fun j=> isClosed_iInter fun _=> isClosed_le (((h.comp (travel_cont (K:=E) x (square i j))).sub continuous_const).norm) continuous_const
  exact (he firstF SU.fund_cont).inter (he matter matter_cont)
lemma wear {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (d : X → ℂ) (c : Y → ℝ) (S : Set X) (Z : Set Y) (f : X → Y)
    (h : Continuous c) (g : Continuous f) (e : ContinuousOn d (S ∩ f ⁻¹' Z)) (r : tsupport c⊆Z) (u : IsOpen Z) :
    ContinuousOn (fun x=> (c (f x):ℂ)*d x) S := by
  intro x hx; by_cases he : f x∈Z
  · have ht : S ∩ f ⁻¹' Z ∈ nhdsWithin x S := inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (g.continuousAt (u.mem_nhds he)))
    exact (((Complex.continuous_ofReal.comp (h.comp g)).continuousAt).continuousWithinAt).mul ((e x ⟨hx,he⟩).mono_of_mem_nhdsWithin ht)
  have hw : f x∉tsupport c := fun l=>he (r l)
  apply ContinuousWithinAt.congr_of_eventuallyEq (f:=fun _=>0) continuousWithinAt_const
  · have ha : ∀ᶠ y in nhdsWithin x S, f y∉tsupport c := g.continuousAt.continuousWithinAt (isClosed_closure.isOpen_compl.mem_nhds hw)
    filter_upwards [ha] with y hy; have h : c (f y)=0 := by by_contra hp; exact hy (subset_closure hp)
    simp [h]
  have h : c (f x)=0 := by by_contra hp; exact hw (subset_closure hp)
  simp [h]

def payer (m B : Side) (e : ℝ) := {t:Skin m B×Cue m|Guard t.1 e ∧ ZeroF m B t.1 t.2}
def lyre (m B : Side) (cut : Part m B) (U : Skin m B) (y x : Cue m) := (law m B U x : ℂ)*logs m B cut U x y
def accord (m B : Side) (cut : Part m B) (U : Skin m B) (x : Cue m) := ∫ y, lyre m B cut U x y ∂rains m
lemma payer_space (m B : Side) (e : ℝ) : LocallyCompactSpace (payer m B e) :=
  (IsLocallyClosed.inter (IsClosed.isLocallyClosed ((cover_closed (Domain m B) e).preimage (continuous_fst (Y:= Cue m)))) ((open0 m B).isLocallyClosed)).locallyCompactSpace
variable (cut : Part m B) {e : ℝ} (b : Room B e) {U : Skin m B}
include b
lemma voice_cont : Continuous (fun t:(payer m B e) × Cue m=> lyre m B cut t.1.val.1 t.1.val.2 t.2) := by
  let F := fun t:(payer m B e) × Cue m=>(t.1.val.1,t.2)
  let Z := fun t:(payer m B e) × Cue m=> t.1.val.2
  let D := fun t:Skin m B × Cue m=>law m B t.1 t.2
  let L := fun t : Skin m B × Cue m × Cue m => logs m B cut t.1 t.2.1 t.2.2
  have hf : Continuous F := (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
  let Y := {t:Skin m B×Cue m|ZeroF m B t.1 t.2}
  let q := fun t => ((F t).1,(F t).2,Z t)
  have he : Continuous q := by unfold q Z; fun_prop
  rw [← continuousOn_univ]; change ContinuousOn (fun x => (D (F x):ℂ)*(L ∘ q) x) _
  apply wear (L ∘ q) D univ Y F (law_cont ..) hf _ (law_stock ..) (open0 ..)
  apply (etude cut b).comp he.continuousOn
  intro y hy; exact ⟨y.1.property.1, hy.2, y.1.property.2⟩
lemma accord_cont : ContinuousOn (fun t:Skin m B × Cue m=>accord m B cut t.1 t.2) (payer m B e) := by
  letI := payer_space m B e
  rw [continuousOn_iff_continuous_restrict]
  exact net_cont _ (rains m) (voice_cont cut b)
lemma lyre_sum {U : Skin m B} (x) (h : Guard U e) (g : ZeroF m B U x) : Integrable (lyre m B cut U x) (rains m) := by
  let v : payer m B e := ⟨(U,x),⟨h,g⟩⟩
  let f := fun y:Cue m=>(v,y); let F := fun t:(payer m B e)×Cue m=> lyre m B cut t.1.val.1 t.1.val.2 t.2
  apply net_compact; change Continuous (F ∘ f); exact (show Continuous F from voice_cont cut b).comp (continuous_const.prodMk continuous_id)
lemma transpose_mean (U : Skin m B) (g : Guard U e) (x y) (h : ZeroF m B U x) (l : ZeroF m B U y) :
    accord m B cut U x + logs m B cut U x y=accord m B cut U y := by
  unfold accord
  let a := logs m B cut U x y
  have he v : lyre m B cut U y v= lyre m B cut U x v+(law m B U v:ℂ)*a := by
    by_cases ht : law m B U v=0
    · simp [lyre,ht]
    have hp := allotted cut b g (law_rich m B U v ht) h l; unfold lyre; rw [←hp,mul_add]
  rw [show lyre m B cut U y=(lyre m B cut U x)+(fun v=>(law m B U v:ℂ)*a) from funext he]
  simp only [Pi.add_apply]
  rw [integral_add (lyre_sum cut b x g h),integral_mul_const,integral_complex_ofReal,rain_law,Complex.ofReal_one,one_mul]
  apply net_compact
  have hf : Continuous (law m B U) := by
    let f := fun x:Cue m=>(U,x); change Continuous ((fun t : Skin m B × Cue m => law m B t.1 t.2) ∘ f); exact (law_cont m B).comp (show Continuous f from continuous_const.prodMk continuous_id)
  exact (Complex.continuous_ofReal.comp hf).mul continuous_const
lemma accord_g (g : Site (Domain m B)→E) (x) (h : Guard U e) (l : ZeroF m B U x) :
    accord m B cut (gauge g U) (partner m B g x)=accord m B cut U x := by
  unfold accord; rw [← rain_subst m B g]; apply integral_congr_ae; apply Eventually.of_forall; intro a
  unfold lyre; dsimp only; rw [law_g]; by_cases he : law m B U a=0
  · simp [he]
  rw [transport_log cut b a x g h (law_rich _ _ _ _ he) l]
end YM.CF.Phase
