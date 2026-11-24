
import SatinPP.Matinee
import SatinPP.Lights
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Set MeasureTheory
open Silk OS OS.Semigroup Spectral Boundary Probe Hierarchy.Seld
open YM.Quays YM.SatinJets
open scoped Topology Matrix BigOperators InnerProductSpace NNReal ContDiff

variable (F:SampleDose)

abbrev roll : E4≃L[ℝ] Vantage:=PiLp.continuousLinearEquiv 2 ℝ _
lemma roll_price {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
   (f:Vantage→X) : (∫ p,f (roll p))=(∫ p,f p):=
    (show MeasurePreserving (⇑roll) volume volume from PiLp.volume_preserving_ofLp Axis)
       |>.integral_comp (roll.toHomeomorph.measurableEmbedding) f
def Puff (p:E4):ℂ:= (F.val (roll p):ℂ)
lemma puff_support : tsupport (Puff F)=roll ⁻¹' tsupport F.val:=by
 rw [tsupport,tsupport,show roll ⁻¹' closure (support _) = closure (roll ⁻¹' support F.val) from
     roll.toHomeomorph.preimage_closure _]
 congr 1; ext1; simp [Puff]
lemma puffCS : HasCompactSupport (Puff F):=by
  have e := F.budget.comp_homeomorph roll.toHomeomorph
  rw [HasCompactSupport,puff_support,tsupport,show roll ⁻¹' closure _ = closure (roll ⁻¹' support F.val) from roll.toHomeomorph.preimage_closure _]
  exact e
def puff : Test4:=(puffCS F).toSchwartzMap
  (Complex.ofRealCLM.contDiff.comp (F.smooth.comp roll.contDiff))


lemma puff_at (p):puff F p=(F.val (roll p):ℂ):=rfl
lemma puff_inv : tsupport (puff F)=roll ⁻¹' tsupport F.val:=puff_support F

variable {F}
def Strict (l u:ℝ)(F:SampleDose):Prop:=∀ p∈tsupport F.val,l<p 3 ∧ p 3<u
lemma bandp {l u:ℝ}(v:Strict l u F):
 Band 3 l u (puff F):= ⟨puffCS F,fun p h=>v (roll p) (puff_inv F |>.le h)⟩
lemma bandp' {l u:ℝ}(v: Band 3 l u (puff F)):Strict l u F:=by
 intro p h; rcases roll.surjective p with ⟨p,rfl⟩
 exact v.snug p ((puff_inv F).ge h)

variable (F){b:ℝ}(h:0<b)
-- dilation
def poseT:Vantage≃L[ℝ]Vantage:= (roll.symm.trans (earlyT 3 h)).trans roll
/-- Later clocks by positive factor b on time. -/
def puffup : SampleDose where
 val p:= b⁻¹ * F.val ((poseT h).symm p)
 smooth:=(contDiff_const).mul (F.smooth.comp (poseT h).symm.contDiff)
 budget:=(F.budget.comp_homeomorph (poseT h).symm.toHomeomorph).mul_left (f:=fun _=>b⁻¹)

lemma puffup_ok : puff (puffup F h)=rev 3 h (puff F):=by
 ext1 p
 rw [puff_at,rev_val,puff_at]
 change ((b⁻¹ * _:ℝ):ℂ)=_; rw [Complex.ofReal_mul,Complex.ofReal_inv]
 rfl

lemma puffup_T (p)(i):poseT h p i=(if i=3 then b else 1)*p i:=rfl
lemma puffup_T' (p) :poseT h p 3=b*p 3:=by simp [puffup_T]
lemma puffup_1 : puffup F (by norm_num:0<(1:ℝ))=F:=by
  have e: poseT (b:=1) zero_lt_one = ContinuousLinearEquiv.refl ℝ Vantage:=by
   ext p i; simp [puffup_T]
  cases F with
  | mk f dv c=>
    unfold puffup
    congr 1
    funext p; simp [e]
lemma pu_space : tsupport (puffup F h).val = poseT h '' tsupport F.val:=by
  ext x
  obtain ⟨s,rfl⟩:= (poseT h).surjective x
  obtain ⟨p,rfl⟩:=roll.surjective s
  rw [Function.Injective.mem_set_image (poseT h).injective]
  -- LHS equivalent reelT p∈…
  refine (show poseT h (roll p)∈ tsupport (puffup F h).val ↔ reelT 3 b p∈tsupport (puff (puffup F h))
     from (by rw [puff_inv];rfl)).trans ?_
  rw [puffup_ok,rev_place,Function.Injective.mem_set_image (show Injective (reelT 3 b) from (earlyT 3 h).injective),puff_inv]
  rfl
lemma pu_pres : (∫ p,puff F p)= ((∫ p,F.val p):ℝ):=by
 simp_rw [puff_at,integral_complex_ofReal,roll_price]


variable {F}
lemma pu_normal (v:F.Normalized):(puffup F h).Normalized:=by
  refine ⟨fun x=> mul_nonneg (inv_nonneg.mpr h.le) (v.1 _),?_⟩
  apply Complex.ofReal_injective
  rw [←pu_pres,puffup_ok,rev_total,pu_pres,v.2]
lemma pu_strict {l u:ℝ}(v:Strict l u F):
 Strict (b*l) (b*u) (puffup F h):= by
  apply bandp';rw [puffup_ok];exact (bandp v).reduced h
#print backwardSite
lemma pu_sites₁ {μ:ℝ}(p:backwardSite F μ): backwardSite (puffup F h) (b*μ):=by
 intro x t;rw [pu_space] at t;rcases t with ⟨x,t,rfl⟩
 rw [puffup_T',←mul_neg]
 exact mul_le_mul_of_nonneg_left (p x t) h.le
lemma pu_sites₂ {μ:ℝ}(p:forwardSite F μ): forwardSite (puffup F h) (b*μ):=by
 intro x t;rw [pu_space] at t;rcases t with ⟨x,t,rfl⟩
 rw [puffup_T']
 exact mul_le_mul_of_nonneg_left (p x t) h.le

#print axioms pu_normal
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
