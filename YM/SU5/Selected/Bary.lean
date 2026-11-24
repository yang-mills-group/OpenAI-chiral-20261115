import YM.SU5.Selected.RankOne
/-!
# Read the actual probability for a chosen axis and character algebra
In construction also support correspondence & transfers to all other axes (when in play).
-/

set_option autoImplicit false
set_option maxHeartbeats 220000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory
open Function Filter Set Topology NormedSpace MeasureTheory Measure ContinuousMap WeakDual
open scoped Topology InnerProductSpace BigOperators NNReal ENNReal ComplexOrder
variable {A B : Type*} {W : Type} [CommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {D:Submodule ℂ W} [CompleteSpace D]

namespace Transaction
variable (Q:Transaction A B D) [MeasurableSpace (Resident A)] [BorelSpace (Resident A)]
local notation "O"=>Q.original
local notation "Φ"=>Q.corner
noncomputable def registration : C(Resident A,ℂ) →⋆ₐ[ℂ] (D→L[ℂ]D) := Q.corner.comp ((gelfandStarTransform A).symm : _ →⋆ₐ[ℂ] _)
noncomputable def ensemble := Spectral.Rep.sees (H:={space:=D}) Q.registration (O)
local notation "μ"=>Q.ensemble
instance : IsFiniteMeasure μ := Spectral.Rep.fin ..
instance : Measure.Regular μ := Spectral.Rep.regal ..
instance normalized : IsProbabilityMeasure μ := isProbabilityMeasure_iff_real.mpr
  ((Spectral.Rep.size (H:={space:=D}) (registration Q) (O)).trans (by rw [Q.unit,one_pow]))
lemma barcode : Q.Bary μ := by
  refine ⟨fun a=>?_⟩
  let h:= Spectral.Rep.pairings (H:={space:=D}) Q.registration (O) (gelfandStarTransform A a)
  exact h.trans (congrArg (fun x : A => inner ℂ O (Φ x O)) ((gelfandStarTransform A).symm_apply_apply a))

theorem full_support (h:∀ a:A,a≠0→ Φ a O ≠ 0) : IsOpenPosMeasure μ := by
  constructor
  intro V p hn H
  obtain ⟨i,m⟩:=hn
  obtain ⟨f,g,q,_⟩:= exists_continuous_zero_one_of_isClosed p.isClosed_compl (isClosed_singleton (x:=i)) (Set.disjoint_singleton_right.mpr (show i∉ Vᶜ from fun t=> t m))
  let F := Spectral.Rep.insert f
  let a := (gelfandStarTransform A).symm F
  have he(x:Resident A) : eye x a=F x := congrArg (fun p:C(Resident A,ℂ)=> p x) ((gelfandStarTransform A).apply_symm_apply _)
  have hx : eye i a=1:=by rw [he, show F i=↑(f i) from rfl, show f i=1 from q (mem_singleton i)]; simp
  have hp:=h a (fun v=> by rw [v,map_zero] at hx; exact zero_ne_one hx)
  have hu : ∀ᵐ i∂μ, eye i a=0:= by
    have ht : ∀ᵐ i∂μ,i∉V := by rw [ae_iff]; simpa using H
    filter_upwards [ht] with i t; rw [he,show F i=↑(f i) from rfl,show f i=0 from g (show i∈ Vᶜ from t)]; simp
  have hv:= Q.barcode.use_char (star a*a)
  rw [integral_eq_zero_of_ae (hu.mono (fun i h=>by change eye i _=0; rw [map_mul,h,mul_zero])), map_mul,map_star] at hv
  apply hp; exact inner_self_eq_zero.mp ((ContinuousLinearMap.adjoint_inner_right (Φ a) O _).symm.trans hv.symm)

theorem succeeds {x: Resident A → Prop} (c:ℝ)(a:A)(H: c≤ ‖inner ℂ O (Φ a O)‖)
    (p: ∀ᵐ t∂μ,x t) : ∃ t, x t ∧ c≤‖eye t a‖ := by
  let F (t:Resident A):=‖eye t a‖
  by_contra! h
  have hp : ∀ᵐ t∂μ,F t < c:= p.mono h -- tune neg binder
  have X : (∫ t,F t∂μ) ≥ c := H.trans (by rw [←Q.barcode.use_char a]; exact norm_integral_le_integral_norm ..)
  have Hc : (∫ _t:Resident A,c∂μ)=c := by simp
  have hc : F ≤ᵐ[μ] (fun _=>c) := hp.mono fun i h=> h.le
  have he:Integrable F μ:= (eyeline a).norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨t,u,v⟩ := (((integral_eq_iff_of_ae_le he (integrable_const _) hc).1
    (le_antisymm (integral_mono_ae he (integrable_const _) hc) (Hc.le.trans X))).and hp).exists
  exact v.ne u
end Transaction
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory.Transaction.full_support
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory.Transaction.succeeds
