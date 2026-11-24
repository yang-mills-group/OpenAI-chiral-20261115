import GaugeFieldConstruction.StencilEquator
/-!
 # GoldArea test at any suitable pair of nonnegative normalized smears
 Proof uses direct Mink.W ℝ.Real continuation, not fixed-axis boost/Mink.Tube estimates.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20 NSF.LD
open YM.Boundary (Probe Probe.bar Joint Test4 Distn)
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable {A Z:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)
variable (W:NSF.Boundary.Surface (SurfRimL A))
variable (m:Axis)(X:Axis→ UV four)(K:UV four)(σ:ℂ)
private lemma material_mass_st {n:ℕ}(F:Fin n→Test4)(u:∀ i,(∫ x:E4,F i x)=1) : (∫ x:Points n, (YM.Boundary.Joint.materialize n F) x)=1:=by
 induction n with
 | zero => rw [YM.Points.volume_nil, integral_dirac]; rfl
 | succ n ih=>
   let t(x:E4× Points n):= F 0 x.1 * YM.Boundary.Joint.materialize n (Fin.tail F) x.2
   let A:= YM.Boundary.Joint.breakAt (n:=n); have he : MeasurePreserving A:= (WithLp.volume_preserving_ofLp _ _).comp (YM.Points.peel (n:=n)).measurePreserving
   calc _=(∫ y:E4× Points n,t y):= he.integral_comp A.toHomeomorph.measurableEmbedding t
        _ = _ := (integral_prod_mul _ _).trans (by rw[u 0,ih (Fin.tail F) (fun k=>u k.succ),one_mul])
section mesh
variable (f g:Test4)(p:SmallDoseSt f)(q:SmallDoseSt g)
local notation "FQ" => YM.Boundary.Joint.materialize 2 ![f,g]
-- positivity everywhere in U and FQ supported there. unit norm follows.
private lemma supportPeg_st (v:Points 2)(t:v∈tsupport ⇑FQ) : v 0∈tsupport ⇑f∧ v 1∈tsupport ⇑g :=by
 let M(i:Fin 2):= (![f,g]) i; let U(i:Fin 2):=tsupport ⇑(M i)
 have he(i:Fin 2): v i∈ U i:=by
    refine closure_minimal (t:=(fun x:Points 2=>x i)⁻¹' U i) ?_ ((isClosed_tsupport _).preimage (by fun_prop)) t
    intro p h; apply subset_closure; change M i (p i) ≠ 0; change FQ p≠0 at h; intro hp; rw [YM.Boundary.Joint.material_at] at h; exact h (Finset.prod_eq_zero (Finset.mem_univ i) hp)
 exact ⟨he 0,he 1⟩
include p q
private lemma compactPeg_st : HasCompactSupport ⇑FQ:=by
 let A₁:=PiLp.homeomorph 2 (fun _:Fin 2=> E4); let T(i:Fin 2):= tsupport ⇑(![f,g] i); have he(i:Fin 2):IsCompact (T i):=by fin_cases i; exact p.2.1; exact q.2.1
 exact ((A₁).isCompact_preimage.mpr (isCompact_univ_pi he)).of_isClosed_subset (isClosed_tsupport _) (fun v w i _=> by change v i∈ T i; fin_cases i; exact (supportPeg_st _ _ v w).1; exact (supportPeg_st _ _ v w).2)
private lemma realPeg_st (v:Points 2): (FQ v).im=0∧ 0 ≤ (FQ v).re :=by
 have h(k: Test4)(t: Probe.bar k=k)(x): (k x).im=0:=by
    have h := congrArg (fun f:Test4=> (f x).im) t; change -(k x).im =(k x).im at h; linarith
 rw [YM.Boundary.Joint.material_at, Fin.prod_univ_two]; change (f (v 0)* g (v 1)).im=0 ∧ _ ≤ Complex.re (f (v 0)* g (v 1)); have hf := fun x=> h f p.2.2.2.1 x; have hg:= fun x=> h g q.2.2.2.1 x; simp only [mul_re,mul_im,hf,hg,mul_zero,zero_mul,zero_add,sub_zero,true_and]; exact mul_nonneg (p.2.2.2.2 _) (q.2.2.2.2 _)
lemma momentPeg_st {U:Set (Points 2)} {R:Points 2→ℂ}{T δ:ℝ}(t:GoldAreaSt (Z:=Z) H W m X K σ U R T δ)(pU:∀ x∈ tsupport ⇑f,∀ y∈tsupport ⇑g, rectoAngleSt x y∈ U) : δ ≤ ((W.W 2 (H.TinCanL ∘ ![σ • X m,K])) FQ).re:=by
 have hv:tsupport ⇑FQ⊆ U:= fun v u=> (show rectoAngleSt (v 0) (v 1)=v from (by ext1 i; fin_cases i<;> rfl)) ▸ pU _ (supportPeg_st _ _ v u).1 _ (supportPeg_st _ _ v u).2
 let F:= FQ; have hw:=compactPeg_st f g p q; have he: (∫ x:Points 2,F x)=1:= material_mass_st _ (fun i=>by fin_cases i; exact p.2.2.1; exact q.2.2.1)
 rw [t.ink FQ hw hv]; let Z(y:Points 2):= R y*F y
 have hp:Integrable Z:=by
    apply Continuous.integrable_of_hasCompactSupport; swap; · exact hw.mul_left
    apply continuous_iff_continuousAt.2; intro u -- continuous not reducible?
    by_cases w:u∈ tsupport ⇑F
    · exact (t.ready.continuousAt (t.upfront.mem_nhds (hv w))).mul F.continuous.continuousAt
    apply ContinuousAt.congr_of_eventuallyEq continuousAt_const; filter_upwards [notMem_tsupport_iff_eventuallyEq.mp w] with t h; unfold Z; rw[h]; exact mul_zero ..
 let B(y: Points 2):= (F y).re; have hB : Integrable B:= F.integrable.re
 rw [show (∫ x:Points 2,R x* F x).re=(∫ x,(Z x).re) from (integral_re hp).symm, show δ= (∫ x:Points 2,δ*B x) from (?_)]
 · apply integral_mono (hB.const_mul _) hp.re; intro v; unfold Z; change _ ≤ Complex.re (R v* FQ v); rw [mul_re,(realPeg_st f g p q v).1]; change _ ≤ (R v).re*B v-_*0; simp only[mul_zero,sub_zero]; by_cases p':v∈tsupport ⇑F; · exact mul_le_mul_of_nonneg_right (t.margin v (hv p')).2.le (realPeg_st f g p q v).2
   rw [show B v=0 from (by unfold B; rw [image_eq_zero_of_notMem_tsupport p']; rfl),mul_zero,mul_zero]
 rw[integral_const_mul,show (∫ x,B x)= Complex.re (∫ x,F x) from (integral_re F.integrable),he,Complex.one_re,mul_one]
#print axioms momentPeg_st
end mesh
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
