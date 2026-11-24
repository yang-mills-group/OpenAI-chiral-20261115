import YM.SU5.FiniteGaugeData.Poin.Arc
import Mathlib
/-!
 # Geometry of the all-axes price test.
 -/
noncomputable section
open Metric Filter Function WithLp
open scoped Topology NNReal ENNReal InnerProductSpace
set_option autoImplicit false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Apso
open _root_.YM Flute Mink Mink.General Mink.Lorentz Real
local notation "k" => SpaceAxis
local notation "ₜ" => timeAxis
variable (i j : k) (t s : ℝ) (x : E4)
abbrev Rho := moveB (Ray.fromAxis i) t
@[simp] lemma Rho_root : Rho i 0=1 := Subtype.ext (tiny _)
@[simp] lemma Rho_inv : (Rho i t)⁻¹=Rho i (-t) := Subtype.ext (rev ..)
lemma Rho_more : Rho i t * Rho i s = Rho i (t+s) := Subtype.ext (fits ..)
abbrev gift (R : SO) : E4 →L[ℝ] E4 := General.walk R.val
@[simp] lemma gift_mul (R S : SO) : gift (R*S) x=gift R (gift S x) := rfl
@[simp] lemma gift_one : gift 1 x=x := rfl
@[simp] lemma gift_self (R : SO) : gift R (gift R⁻¹ x)=x := by rw [← gift_mul]; simp
@[simp] lemma gift_self' (R : SO) : gift R⁻¹ (gift R x)=x := by rw [← gift_mul]; simp
lemma gift_norm (R : SO) : ‖gift R x‖=‖x‖ := R.property.2 _
lemma gift_inner (R : SO) (x y : E4) : inner ℝ (gift R x) (gift R y) = inner ℝ x y :=
  (show E4 →ₗᵢ[ℝ] E4 from ⟨(gift R).toLinearMap,fun _ => gift_norm _ R⟩).inner_map_map x y
lemma warpT : time (gift (Rho i t) x)=cos t*time x - sin t*x i.castSucc := by change time (circleB _ _ _)=_; rw [ttake, Ray.onAxis]
lemma warpS : gift (Rho i t) x i.castSucc = sin t*time x + cos t*x i.castSucc := by
  rw [← Ray.onAxis, ← Ray.onAxis]; exact etake ..
lemma warpQ (h : j ≠ i) : gift (Rho i t) x j.castSucc=x j.castSucc := by
  change spatial (circleB (Ray.fromAxis i) t x) j = _
  rw [stake]
  simp [Ray.fromAxis, h, spatial]
lemma ear : timeAxis ≠ i.castSucc := by fin_cases i <;> decide
lemma pillar (h : j ≠ i) : gift (Rho i t) (basis j.castSucc)=basis j.castSucc := by
  apply ext_by
  · apply PiLp.ext
    intro u; change gift (Rho i t) (basis j.castSucc) u.castSucc = basis j.castSucc u.castSucc
    rcases eq_or_ne u i with rfl|v
    · rw [warpS]; simp [time, ear j,h.symm]
    exact warpQ i u t _ v
  rw [warpT]
  simp [time, ear j,h.symm]

inductive Loom : SO → Prop
| one : Loom 1
| turn (i : SpaceAxis) (t : ℝ) : Loom (Rho i t)
| chain (R S : SO) (p : Loom R) (q : Loom S) : Loom (R*S)
lemma Loom.reverse (R : SO) (p : Loom R) : Loom R⁻¹ := by
  induction p with
  | one => rw [inv_one]; exact Loom.one
  | turn i t => rw [Rho_inv]; apply Loom.turn
  | chain _ _ _ _ e h => rw [mul_inv_rev]; exact Loom.chain _ _ h e
lemma stand : ∃ t, gift (Rho i t) x i.castSucc=0 ∧ 0 ≤ time (gift (Rho i t) x) := by
  let z : ℂ := ⟨time x,x i.castSucc⟩
  refine ⟨-z.arg, ?_⟩
  let s := z.arg; rw [warpS, warpT, cos_neg,sin_neg]
  change -sin s*z.re+cos s*z.im = _ ∧ 0 ≤ cos s*z.re- -sin s*z.im
  rw [← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg]
  change -sin s*(‖z‖*cos s)+cos s*(‖z‖*sin s)= _ ∧ 0 ≤ cos s * _ - -sin s * (‖z‖*sin s)
  constructor
  · ring
  apply le_of_le_of_eq (norm_nonneg z)
  symm; linear_combination ‖z‖ * sin_sq_add_cos_sq s
private lemma glide : ∃ T : SO, Loom T ∧ time (gift T x)=0 ∧ 0 ≤ gift T x i.castSucc ∧
    ∀ j : k, j ≠ i → gift T (basis j.castSucc)=basis j.castSucc := by
  obtain ⟨t,H,G⟩ := stand i x
  refine ⟨Rho i (π/2)*Rho i t,Loom.chain _ _ (.turn ..) (.turn ..),?_⟩
  refine ⟨?_,?_,fun j p=> by rw [gift_mul, pillar _ _ _ p,pillar _ _ _ p]⟩
  · rw [gift_mul,warpT,Real.sin_pi_div_two, Real.cos_pi_div_two, H]; ring
  rw [gift_mul,warpS, Real.sin_pi_div_two, Real.cos_pi_div_two, one_mul, zero_mul, add_zero]; exact G
abbrev Fix (R : SO) (i : k) := gift R (basis i.castSucc)=basis i.castSucc
lemma fixesU (T : SO) (p : Fix T i) : gift T x i.castSucc=x i.castSucc := by
  calc
    _ = inner ℝ (gift T (basis i.castSucc)) (gift T x) := by rw [p,basis_inner]
    _ = _ := by rw [gift_inner,basis_inner]
lemma Fix.togetherK {T U : SO} (p : Fix T i) (q : Fix U i) : Fix (T*U) i := by
  unfold Fix; rw [gift_mul,q,p]
private lemma spiral (L : Finset k) : ∃ R : SO, Loom R ∧ (∀ i ∈ L,gift R x i.castSucc=0) ∧
    ∀ i ∉ L, Fix R i := by
  induction L using Finset.induction_on with
  | empty => exact ⟨1, Loom.one,by simp,fun _ _ => rfl⟩
  | @insert a L h ih =>
    obtain ⟨R,H,F,L'⟩ := ih
    obtain ⟨t,T,_⟩ := stand a (gift R x)
    use Rho a t * R
    refine ⟨.chain _ _ (Loom.turn _ _) H, ?_,?_⟩
    · intro i v
      rw [gift_mul]
      rcases Finset.mem_insert.mp v with rfl|e
      · exact T
      rw [warpQ, F i e]; rintro rfl; contradiction
    · intro i v
      exact Fix.togetherK _ (pillar a i t (fun p => v (Finset.mem_insert.mpr (Or.inl p)))) (L' _ fun e=> v (Finset.mem_insert_of_mem e))
private lemma bay (L : Finset k) (R : SO) (p : ∀ j ∈ L, Fix R j) (h : i ∉ L) :
    ∃ S : SO, Loom S ∧ ∀ j ∈ insert i L, Fix (S*R) j := by
  let x := basis i.castSucc
  obtain ⟨T,P,E,H⟩:= spiral (gift R x) ((insert i L)ᶜ)
  have V (a : k) (d : a∈L) : Fix T a := H a (by simp [d])
  obtain ⟨S,Q,A,D,G⟩:= glide i (gift (T*R) x)
  use S*T, Loom.chain _ _ Q P
  have B (j) (d : j ∈ L) : j ≠ i := fun e => h (e ▸ d)
  have f (j) (d : j∈L) : Fix (S*T*R) j := Fix.togetherK _ (Fix.togetherK _ (G j (B j d)) (V j d)) (p j d)
  intro j jL
  suffices V : Fix (S*T*R) i from (Finset.mem_insert.mp jL).elim (fun p=> p ▸ V) (f j)
  let z := gift (S*T*R) x
  have z0 : time z=0 := by rwa [← gift_mul, ← mul_assoc] at A
  have zp : 0 ≤ z i.castSucc := by rwa [← gift_mul, ← mul_assoc] at D
  have zP : ‖z‖ =1 := by rw [show ‖z‖=‖x‖ from gift_norm .., show ‖x‖=1 from basis_norm _]
  have ν (j) (p : j ≠ i) : z j.castSucc=0 := by
    by_cases d : j∈L
    · rw [show z j.castSucc= _ from fixesU j x _ (f j d)]; simp [x,p]
    unfold z; rw [mul_assoc,gift_mul, fixesU j _ S (G j p), gift_mul, E j (by simp [p,d])]
  have W : z = z i.castSucc • basis i.castSucc := by
    apply ext_by
    · apply PiLp.ext
      intro a; change z a.castSucc = (z i.castSucc • basis i.castSucc : E4) a.castSucc
      by_cases p : a=i
      · subst a; simp
      simp [ν a p,p]
    rw [z0,clock_mul]; simp [time, ear i]
  have v : z i.castSucc=1 := by rwa [W, norm_smul, Real.norm_eq_abs, abs_of_nonneg zp, basis_norm, mul_one] at zP
  change z=_; simpa [v] using W
lemma jade (R : SO) (hp : ∀ i, Fix R i) : R=1 := by
  let c := time (gift R (basis timeAxis))
  have σ : gift R (basis timeAxis)=c • basis timeAxis := by
    apply ext_by
    · rw [rest_mul,roll_space,smul_zero]; apply PiLp.ext; intro a; change gift R (basis timeAxis) a.castSucc=0
      rw [fixesU a _ R (hp a)]; simp [(ear a).symm]
    rw [clock_mul,roll_clock,mul_one]
  let d : Axis → ℝ := fun i => if i=timeAxis then c else 1
  let B := (EuclideanSpace.basisFun Axis ℝ).toBasis
  have he (i : Axis) : gift R (B i)=d i • B i := by
    have H : B i = basis i := by simp [B, basis, EuclideanSpace.basisFun_apply]
    rw [H]
    refine Fin.lastCases (motive:=fun i => gift R (basis i)=d i • basis i) ?_ ?_ i
    · change gift R (basis timeAxis)= d timeAxis • basis timeAxis; simpa [d] using σ
    intro j; rw [hp j]; simp [d,(ear j).symm]
  have D1 : LinearMap.toMatrix B B (gift R).toLinearMap=Matrix.diagonal d := by
    ext i j
    rw [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe, he]
    by_cases p : i=j
    · subst j; simp
    simp [p]
  have g : ∏ i, d i=1 := by rw [← Matrix.det_diagonal, ← D1, LinearMap.det_toMatrix]; exact R.property.1
  have I : c=1 := by simpa [d] using g
  have H (i) : gift R (B i)=B i := by rw [he]; simp [d,I]
  apply Subtype.ext
  apply General.ext; intro x
  change gift R x=x
  suffices y : (gift R).toLinearMap=LinearMap.id by exact DFunLike.congr_fun y x
  exact B.ext fun i => H i
#print axioms jade
private lemma olivine (R : SO) (L : Finset k) : ∃ S : SO, Loom S ∧ ∀ j ∈ L, Fix (S*R) j := by
  induction L using Finset.induction_on with
  | empty => exact ⟨1, Loom.one, by simp⟩
  | @insert a L h ih =>
    obtain ⟨T,v,w⟩:= ih; obtain ⟨S,p,q⟩:= bay a L (T*R) w h
    exact ⟨S*T,Loom.chain _ _ p v,fun j e => by rw [mul_assoc]; exact q j e⟩
-- entire motion as group generated by THREE ingredients (no spacelike-axis mixing ingredients).
lemma sheen (R : SO) : Loom R := by
  obtain ⟨S,p,q⟩:= olivine R Finset.univ
  rw [eq_inv_of_mul_eq_one_right (jade (S*R) (fun j=> q j (Finset.mem_univ j)))]
  exact p.reverse _
#print axioms sheen
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Apso
