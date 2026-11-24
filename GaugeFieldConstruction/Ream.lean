import GaugeFieldConstruction.Mangos
/-!
# 81 scalings on a comparison path (only rates required by U2–U5 transfers)

 No rescaling the whole theory between tests. Matrix prices derive from the *same* point system S without error on that choice. Test function cost is on a Piet (positive scale). `roll` includes Jacobian to cancel against the rescaled volume. Axis order tested by `sold n`.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace
open scoped Topology BigOperators ContDiff
open Floor Wick Invoice Gap
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n :ℕ}

structure Rim where
  r : ℝ
  p : 0<r
namespace Rim
variable (Q : Rim)
def normed (n : ℕ): ℝ:=Q.r^(4*n)
def pull {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] : X ≃L[ℝ] X := ContinuousLinearEquiv.smulLeft (Units.mk0 Q.r⁻¹ (inv_ne_zero Q.p.ne'))
lemma rv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (x:X): Q.pull x=Q.r⁻¹ • x :=rfl
lemma ne : Q.r≠0 := Q.p.ne'
lemma move (x: Points n) (h: Q.pull x ∈conf n): x∈ conf n:= fun i j u=> h (congr_arg (fun x : E4=> Q.r⁻¹ • x) u)
def roll : Module.End ℂ (Test n) := (normed Q n)⁻¹ • pullLinear Q.pull (fun i h=> Q.move i h)
def band (b : Bulb): Bulb where
  f:= b.f ∘ Q.pull
  d:=b.d.comp Q.pull.contDiff
  c:=by
    have he : support (b.f ∘ Q.pull)=(pull Q) ⁻¹' support b.f:=rfl
    rw [HasCompactSupport,tsupport,he]; exact show IsCompact (closure (Q.pull ⁻¹' support b.f)) from Eq.mp (congr_arg IsCompact ((Q.pull (X:=E4)).toHomeomorph.preimage_closure (support b.f))) ((Q.pull (X:=E4)).toHomeomorph.isCompact_preimage.mpr b.c)

lemma shot (b : Bulb) : (Q.band b).run=(Q.pull) ⁻¹' b.run:= by
  change closure (support (b.f ∘ Q.pull))= _; rw [show support (b.f ∘ Q.pull)=Q.pull ⁻¹' support b.f from rfl]
  exact (Q.pull.toHomeomorph.preimage_closure _).symm
lemma lively (x : E4) (b : Bulb) : Bulb.lit b (Q.pull x) → Bulb.lit (Q.band b) x:=fun h=> Q.pull.continuous.continuousAt.tendsto h
lemma fide (b a : Bulb) (u : Before b a) : Before (band Q b) (band Q a):= ⟨fun i h=> Q.lively _ _ (u.burns (Q.pull i) (show i ∈ Q.pull ⁻¹' b.run from Q.shot b ▸ h))⟩
lemma value (f : Test n) (x) : Q.roll f x=(normed Q n)⁻¹ • f (Q.pull x):=rfl
lemma via (x : Test n): tsupport (roll Q x) ⊆ (pull Q) ⁻¹' tsupport x := by rw [← ts_pull]; exact tsupport_smul_subset_right (fun _=>(normed Q n)⁻¹) ((x:Points n→ℂ) ∘ Q.pull)
lemma Works' {x : Test n} {b : Bulb} {k : Fin n} (h:Works b x k): Works (Q.band b) (Q.roll x) k:= by
  constructor
  · intro i p; apply Q.lively; exact h.bulb (Q.pull i) (via Q x p)
  intro i p s g; rw [shot]; exact h.direct _ (show Q.pull i∈ tsupport x from via Q x p) s g

def rolled (f : Foil): Foil :=
  ⟨Q.roll f.p,fun i u a t b q=> (f.plen (show Q.pull i∈ tsupport f.p from via Q f.p u)) a (congr_arg (fun x :ℝ=> Q.r⁻¹ • x) q), Q.band f.a,Q.band f.b,Q.band f.c, Q.Works' f.u,Q.Works' f.v,Q.Works' f.w,Q.fide _ _ f.q,Q.fide _ _ f.r, fun i p z u j e=>
    f.luck _ (show Q.pull i∈tsupport f.p from via Q f.p p) (pull Q z) (show z∈ Q.pull ⁻¹' f.a.run from Q.shot f.a ▸ u) j (congr_arg (fun x:ℝ => Q.r⁻¹ • x) e)⟩

lemma roll_der (f : Test n) (v : Points n): tilt v (Q.roll f)=Q.r⁻¹ • Q.roll (tilt v f):= by
  ext1 x; rw [tilt_pays,show (⇑(Q.roll f) : Points n→ℂ)=fun x=>(normed Q n)⁻¹ • f (Q.pull x) from rfl]; change fderiv ℝ ((normed Q n)⁻¹ • (f ∘ ⇑Q.pull)) x v= Q.r⁻¹ • ((normed Q n)⁻¹ • tilt v f (Q.pull x)); rw [tilt_pays]
  rw [fderiv_const_smul ((diffT f).differentiableAt.comp _ Q.pull.differentiableAt), ContinuousLinearMap.smul_apply, fderiv_comp _ (diffT f _) Q.pull.differentiableAt,ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply]
  change _ • (fderiv ℝ (⇑f) _ (Q.r⁻¹ • v))= _; rw [map_smul]; apply smul_comm
lemma roll_fee (u : Bond n) (w) (k : Fin n) (a): paid k a (u ∘ₗ Q.roll) w=Q.r • paid k a u (Q.roll w) := by
  rw [pays,pays,roll_der,dollar]; rw [LinearMap.comp_apply, smul_neg,smul_smul,mul_inv_cancel₀ Q.ne,one_smul]
lemma roll_price (u : Bond n) (k : Fin n) (a) : (Q.r:ℂ) • (paid k a u ∘ₗ Q.roll)=paid k a (u ∘ₗ Q.roll):= by ext1 x; rw [roll_fee]; exact Complex.real_smul.symm
lemma band_p (b : Bulb) (i) (x : E4): D (basis i) (Q.band b).f x=Q.r⁻¹ * D (basis i) b.f (Q.pull x):= by
  unfold D band; rw [fderiv_comp _ (b.d.differentiable (by simp) _) Q.pull.differentiableAt,ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply]
  change fderiv ℝ b.f _ (Q.r⁻¹ • basis i)=_; rw [map_smul]; rfl

lemma drop (w: Payroll n) (m:ℕ) (v:∀ i x,w.K i x= Q.r^m*w.K i (Q.pull x))
    (f : Test n) (t : Bulb) (k) (p:Works t f k) (i j): testcut w (Q.roll f) (Q.band t) (Q.Works' p).cared i j = Q.r^(3+m) • Q.roll (testcut w f t p.cared i j):= by
  ext1 x
  change testcut w (Q.roll f) (Q.band t) (Q.Works' p).cared i j x=Q.r^(3+m) • (Q.roll (testcut w f t p.cared i j) x)
  rw [testcut_v, value, band_p,value, testcut_v,show helm (Q.pull x)=Q.pull (helm x) by rw [rv,map_smul]; rfl,show riders (Q.pull x)=Q.pull (riders x) by rw [rv,map_smul]; rfl]
  nth_rw 1 [v j x]; simp only [smul_smul]; congr 1; unfold normed; rw [Nat.mul_add, pow_add,pow_add]; field_simp [Q.ne]; ring
lemma cash (w : Payroll n) (m : ℕ) (v:∀ i x,w.K i x= Q.r^m*w.K i (Q.pull x)) (f : Test n) (t : Bulb) (k) (p: Works t f k) (A: Variation n):
    delta w (Q.roll f) (Q.band t) (Q.Works' p).cared A= Q.r^(3+m) • delta w f t p.cared (fun i j=>A i j ∘ₗ Q.roll):=by
  unfold delta; simp_rw [drop Q w m v f t k p,dollar,Finset.smul_sum]; rfl
lemma do_move (a) (f :Test n) (t k) (p:Works t f k) (A : Variation n) : delta (ticket a) (Q.roll f) (Q.band t) (Q.Works' p).cared A= ((Q.r:ℂ)^3) • delta (ticket a) f t p.cared (fun i j=>A i j ∘ₗ Q.roll):= by
  rw [cash Q (ticket a) 0 (fun i x=> by simp [ticket] ) f t k p A, Complex.real_smul, Complex.ofReal_pow]; rfl
lemma do_turn (Ω) (f : Test n) (t k) (p:Works t f k) (A : Variation n): delta (desk k Ω) (Q.roll f) (Q.band t) (Q.Works' p).cared A= ((Q.r:ℂ)^4) • delta (desk k Ω) f t p.cared (fun i j=>A i j ∘ₗ Q.roll):= by
  have he (i) (x : Points (n+1)): lab k Ω i x=Q.r^1 * lab k Ω i (Q.pull x):=by rw [rv,map_smul]; simp [Q.ne]
  rw [cash Q (desk k Ω) 1 he f t k p A, Complex.real_smul,Complex.ofReal_pow]; rfl
end Rim
end YM.GaugeFieldConstruction.Ember
