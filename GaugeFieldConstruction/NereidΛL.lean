import GaugeFieldConstruction.EurekaΛL
/-!
 # Translation δ is THIS infinitesimal translation on fields. NO charges. On any vector on common domain:
 Va field(f) Va^-1. Cov.Rotation also law higher.
 δ insertion W probes derivatives *above* (verified via ΩEu to W shift). cost tie check from ordered & rays support.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Filter Set Finset Mink MeasureTheory Analysis LineDeriv
open scoped BigOperators Topology ContDiff InnerProductSpace
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}
variable {n:ℕ}(a:Axis)(f:Test4)(k:Fin n)
abbrev tshiftΛ (i:Axis)(t:ℝ)(b:Test4):Test4:= Joint.push (Poincare.translation (t • basis i)) b
lemma pushΛKnownL (t:ℝ)(x:E4): tshiftΛ a t f x=f (x - t • basis a):= by simp [tshiftΛ,Poincare.translation]
-- sign directional action. NEG input derivatives. x enters inverse placements.
lemma ΦTravelΛL : Tendsto (fun t:ℝ=> t⁻¹ • (tshiftΛ a t f - f)) (𝓝[≠] 0) (𝓝 (-ΦshiftΛ (basis a) f)) :=by
 let F(t:ℝ):= tshiftΛ a t f; let D(t:ℝ):= tshiftΛ a t (-ΦshiftΛ (basis a) f)
 have hc: Continuous D:=Work.C08.continuous_affine_probe (fun t:ℝ=> t • basis a) (fun t=>(1:Lorentz).sends.symm) _ (continuous_id.smul continuous_const) continuous_const continuous_const
 have he(t:ℝ)(x:E4): HasDerivAt (fun s:ℝ=> F s x) (D t x) t :=by
    simp only[F,D,pushΛKnownL]; let v(s:ℝ):=x-s • basis a; rw [neg_apply, ΦsΛKnownL];
    have hu:HasDerivAt v (-basis a) t:= ((hasDerivAt_const t x).sub ((hasDerivAt_id' t).smul_const (basis a))).congr_deriv (by simp)
    have hF:= (((f.smooth 1).differentiable (by simp) (v t))).hasFDerivAt.comp_hasDerivAt t hu; rw [map_neg] at hF; exact hF
 have H :=Work.C08.probe_slope_of_pointwise F D hc he
 have hp(f:Test4): tshiftΛ a 0 f=f:=by ext1 x; rw [pushΛKnownL]; simp
 rw [show D 0=_ from hp _,show F 0=f from hp _] at H; exact H
variable (R: Fields S)(e:R.Total)
local notation "XΩ"=> R.domain
include e
lemma LeafHereΛL (x: S.Union)(v:XΩ) : HasDerivAt (fun t:ℝ=> ((R.field x) (tshiftΛ a t f) v).val) (((R.field x) (-ΦshiftΛ (basis a) f) v).val) 0 := by
 let u':Test4→ₗ[ℂ] R.H := R.domain.subtype ∘ₗ (LinearMap.applyₗ' _ v) ∘ₗ (R.field x) -- tune
 let Z := u'.restrictScalars ℝ
 have ht : Continuous Z:= e.temperate x v
 have h:= ΦTravelΛL a f
 rw [hasDerivAt_iff_tendsto_slope]; refine (ht.continuousAt.tendsto.comp h).congr (?_)
 intro b
 simp only [slope_def_module, sub_zero,show tshiftΛ a 0 f=f from by ext1 x; simp [tshiftΛ]]; change Z (b⁻¹ • _) = _; rw [map_smul,map_sub]; rfl
omit e
variable {h:S.RealSpin}{V:S.Rotation}(W: Wightman S)(Q: W.Realizes (W:=Y) V h)(x: S.Union)
local notation "Fρ"=> W.operators
include Q
def LocalActΛL (p:Poincare): W.operators.domain→ₗ[ℂ] W.operators.domain:= ((W.action.V p).toLinearMap ∘ₗ W.operators.domain.subtype).codRestrict W.operators.domain fun i=> Q.covariance.domain p i.property
lemma LocalActPayΛL (p:Poincare)(x): (LocalActΛL W Q p x).val=W.action.V p x.val:=rfl
lemma LocalHomeΛL (p:Poincare)(x): LocalActΛL W Q p (LocalActΛL W Q p⁻¹ x)=x:=Subtype.ext (by rw[LocalActPayΛL,LocalActPayΛL]; nth_rw 1 [← inv_inv p]; rw[Action.goes])
noncomputable abbrev DragΛL (p:Poincare):Module.End ℂ W.operators.domain→ Module.End ℂ W.operators.domain:= fun t=> (LocalActΛL W Q p) ∘ₗ t ∘ₗ (LocalActΛL W Q p⁻¹)
lemma MeadΛL (p:Poincare)(x): DragΛL W Q p (W.operators.field x f) = W.operators.field (W.spin.rail p.Λ x) (Joint.push p f):=by
 apply LinearMap.ext; intro i; apply Subtype.ext; change (LocalActΛL W Q p _).val=_; let k:=LocalActΛL W Q p⁻¹ i; rw[LocalActPayΛL,LinearMap.comp_apply,Q.covariance.covariance]; change (W.operators.field _ _ (LocalActΛL W Q p k)).val=_; rw [show LocalActΛL W Q p k=i from LocalHomeΛL ..]
lemma LeafActΛL (i:W.operators.domain): HasDerivAt (fun t:ℝ=> (DragΛL W Q (Poincare.translation (t • basis a)) (W.operators.field x f) i).val) ((W.operators.field x (-ΦshiftΛ (basis a) f) i).val) 0 :=by
 simp_rw [MeadΛL, show ∀ b:E4,W.spin.rail (Poincare.translation b).Λ x=x from fun b=>Q.letters.identity x]; exact LeafHereΛL a f Fρ Q.total x i
#print axioms LeafActΛL
end YM.NSF.Boundary
