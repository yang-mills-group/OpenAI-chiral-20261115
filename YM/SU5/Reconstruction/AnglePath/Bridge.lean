import YM.SU5.Reconstruction.AnglePath.Switch
/-!
# Phase budgets passed via Friedrichs comparison (the second Clasp). Generic.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame.Cardio
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K J H D:Hilbert} {X:Type}
open Clasp

open Spectral OS Semigroup Boundary Picket
variable (F:H≃ₗᵢ[ℂ] D){a:Axis}(S:OS.Semigroup H a)
local notation "P"=> F.conjStarAlgEquiv
local notation "Y" => S.ℚmeasure
noncomputable def Sentry : OS.Semigroup D a where
 E t:= P (S.E t)
 U s:= P (S.U s)
 time t s:=by change P (S.E (t+s))=P (S.E t)*P (S.E s); rw [show S.E (t+s)=S.E t*S.E s from S.time t s,map_mul]
 space t s:=by change P (S.U (t+s))= P (S.U t)*P (S.U s); rw [show S.U (t+s)=S.U t*S.U s from S.space t s,map_mul]
 eZero:= by change _=1; rw [show S.E 0=1 from S.eZero,map_one]
 uZero:= by change _=1; rw [show S.U 0=1 from S.uZero,map_one]
 sym t:=by change star (P _)=_; rw [← show P (star (S.E t))=star (P (S.E t)) from F.conjStarAlgEquiv.map_star' (S.E t),show star (S.E t)=S.E t from S.sym t]
 shrinks t:= by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>?_); rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, F.norm_map, one_mul]; exact ((S.E t).le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)).trans_eq (F.symm.norm_map x))
 unitary t v:=by rw[LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,F.norm_map,S.unitary,F.symm.norm_map]
 independent t s:= by
    change (P _)*(P _)=_*_; rw [←map_mul,←map_mul,show S.E t*S.U s=S.U s*S.E t from S.independent t s]
 continuousE v:=by simp_rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]; exact F.continuous.comp (S.continuousE _)
 continuousU v:=by simp_rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]; exact F.continuous.comp (S.continuousU _)
local notation "Q"=> Sentry F S
lemma enters (u:ℝ≥0)(x:H): (Q).E u (F x)=F (S.E u x):=by unfold Sentry; rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]; simp
-- orientation-time identification of Kahler rotation. Real edge :: price not just translation of supports. reproduce under_heat
private lemma underT (t:ℝ)(x:H): (Q).edge t (F x)=F (S.edge t x):=by
    have hp {X:Hilbert} {r:Axis} (Q₀:OS.Semigroup X r) (f:X) : AnalyticOnNhd ℂ (fun v=> Q₀.F v f) inside := fun a' h=> ((ContinuousLinearMap.apply ℂ X.space f).analyticAt _).comp (Q₀.localHeat a' h)
    have h(y:H)(z:ℂ)(q:z∈inside): F (S.F z y)=(Q).F z (F y):=by
       refine ConePrice.Sail.pioneer («A»:=OS.Semigroup.inside) (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0|>.isPreconnected) (w:=1) (show ((↑(1:ℝ)):ℂ)∈ inside from (by change 0< (Complex.ofReal (1:ℝ)).re; simp)) 0 2 (by norm_num) (M₁:=fun z=> F (S.F z y)) (fun a' h=> (F.toLinearIsometry.toContinuousLinearMap.analyticAt _).comp (hp _ _ a' h)) (hp (Q) (F y)) ?_ q
       intro u v; change F (S.F (u:ℂ) y)=(Q).F (u:ℂ) (F y)
       rw [show (u:ℂ)=duration (Real.toNNReal u) from (by unfold duration; rw [Real.coe_toNNReal u v.1.le]), (Q).roots_heat (Real.toNNReal_pos.mpr v.1),S.roots_heat (Real.toNNReal_pos.mpr v.1),enters]
    apply congrFun (a:=x) ((S.whole 1).equalizer (((Q).edge t).continuous.comp F.continuous) (F.continuous.comp (S.edge t).continuous) _)
    funext u; dsimp only [Function.comp_apply]; rw [← enters F S,OS.Semigroup.high,OS.Semigroup.high,h _ _ (length.mpr zero_lt_one)]
lemma polished (x:E4)(u:H): Picket.trans Q x (F u)=F (Picket.trans S x u):= by
 have he(t: _root_.YM.OS.Cross a) : (Q).U t (F u)=F (S.U t u):=by unfold Sentry; rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]; simp -- tune namespace
 change (Q).edge (x a) ((Q).U (SEP a x) (F u))= _; rw [he,underT]; rfl -- tune
lemma enlightened(x:H):(Q).ℚmeasure.diagonal (F x)=S.ℚmeasure.diagonal x:=by
 apply Measure.ext_of_charFun; funext v; rw [(Q).joint,S.joint]; change inner ℂ _ (Picket.trans Q v (F x))=inner ℂ _ (Picket.trans S v x); rw [polished,F.inner_map_map]
lemma forwardP (h:ConePrice.Forward S):ConePrice.Forward Q:=by
 ext1 x; obtain ⟨x,rfl⟩:= F.surjective x
 apply ((Q).ℚmeasure.null_pair (ConePrice.closed_front a).isOpen_compl.measurableSet (F x)).1; rw [enlightened]
 exact (S.ℚmeasure.null_pair (ConePrice.closed_front a).isOpen_compl.measurableSet x).2 (by rw [h]; rfl)
-- independent funding of Radial range. Orth complement proof; bootstrap from local witnesses.
section ariel
variable (M:Submodule ℂ H)
private lemma onwards {U:H.Op} (e : IsSelfAdjoint U)(p:∀ x,x∈ M→ U x∈M) (x:H)(m:x∈ Mᗮ): U x∈Mᗮ := by intro y hy; change inner ℂ y (U x)=0; rw [show U=U.adjoint from e.symm,ContinuousLinearMap.adjoint_inner_right]; exact m _ (p y hy)
lemma inductReach (U:H.Op)(e:IsSelfAdjoint U)(x:H)(m:IsClosed (M:Set H))(p:∀ x,x∈ M→ U x∈M) (v: ∃ n:ℕ, (U^n) x∈M): U x∈M:=by
 letI: CompleteSpace M:=m.completeSpace_coe
 have H₂(y:H)(e' : U (U y)∈M): U y∈M := by
    let z:H:= M.starProjection y; let r:= y-z; have hp: z∈M:=M.starProjection_apply_mem _
    have h: U r∈ Mᗮ :=onwards M e p _ (Submodule.sub_starProjection_mem_orthogonal _);
    have hx: U (U r)∈M:= by unfold r; rw [map_sub,map_sub]; exact M.sub_mem e' (p _ (p _ hp))
    have hr: U (U r)=0:= inner_self_eq_zero (𝕜:=ℂ)|>.1 ((onwards M e p _ h) _ hx)
    have hv: U r=0:= inner_self_eq_zero (𝕜:=ℂ)|>.1 (by nth_rw 1 [show U=U.adjoint from e.symm]; rw [ContinuousLinearMap.adjoint_inner_left,hr,inner_zero_right])
    rw [show y=z+r from (by unfold r; abel),map_add,hv,add_zero]; exact p _ hp
 obtain ⟨n,w⟩:=v
 have he(n:ℕ)(y:H)(h:(U^n) y∈M): U y∈M:=by
    induction n generalizing y with
    | zero=> rw [pow_zero] at h; exact p _ h
    | succ n ih=>apply H₂ y; rw [pow_succ] at h; exact ih _ h
 exact he n x w
end ariel
end YM.CrossedFrame.Cardio
