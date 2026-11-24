import GaugeFieldConstruction.Pairs

/-!
# Calculate the reflection matrix at E4.basis τ by commuting powers first
-/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction.Wick
open Complex Gap Finset Cauchy Function Row YM.Analysis
open YM.Maxwell (normal Green)
open scoped Topology RealInnerProductSpace ContDiff
noncomputable def apex := basis τ
noncomputable abbrev stare:= eye apex
lemma exposed : apex ≠ 0 := fun p=> by have t := congr_arg (fun f:E4=> f τ) p; simp [apex] at t
@[simp] lemma watch : stare oneG=1:= cut_val (fun _=> (1:ℂ)) (fun _ _=> contDiffAt_const) exposed

section
local notation "T" i => Gap.step i
local notation "K" => Module.End ℂ SmoothGap
lemma tw (h : SmoothGap) : Gap.times oneG h=h := Gap.eyes fun z hz=> by
  have he : eye z oneG=1 := cut_val (fun _=>(1:ℂ)) (fun _ _=> contDiffAt_const) hz; rw [Gap.tick,he,one_mul]
noncomputable def clock (i : Axis) := lit (YM.Maxwell.compAxis i) (fun _ _=> ContinuousLinearMap.contDiff _ |>.contDiffAt)
lemma clockwork (i j) : (T i) (clock j)=if j=i then oneG else 0 := by
  apply individuated; intro z hz; rw [clock,light,lap _ _ hz]; unfold YM.Maxwell.grad D
  rw [ContinuousLinearMap.fderiv]
  change ((basis i j:ℝ):ℂ)=_
  by_cases h:i=j
  · subst i; rw [if_pos rfl]; simp [oneG, cut_val _ _ hz]
  rw [if_neg (Ne.symm h)]; simp [h,Ne.symm h]
lemma lever (i) : stare (clock i)=if τ=i then 1 else 0 := by
  change (clock _).val _=_; rw [clock,lap _ _ exposed]; change (((basis τ i):ℝ):ℂ)=_
  by_cases h:i=τ
  · rw [h]; simp
  simp [h,Ne.symm h]

/-- tower of radial prices normal times power of inverse norm squared. -/
noncomputable def slope (n : ℕ) := lit (fun x:E4=>normal * (‖x‖^2)⁻¹ ^ n) (fun _ hx=> by
  have hw:= norm_pos_iff.mpr hx; exact contDiffAt_const.mul (((contDiff_norm_sq ℝ).contDiffAt.inv (by dsimp; positivity)).pow _))
lemma sheer : stone=slope 1 := individuated fun z hz=>by rw [slope,lap _ _ hz,stone,lap _ _ hz,Green,pow_one]
lemma rank (i : Axis) (n : ℕ) : (T i) (slope n)=((-2:ℂ)*n) • Gap.times (clock i) (slope (n+1)) := by
  apply eyes; intro x hx
  rw [map_smul,tick]; change (Gap.step i (slope n)).val x= _ * ((clock i).val _ * (slope (n+1)).val _); simp only [clock,slope]; rw [light]
  rw [lap _ _ hx,lap _ _ hx,lap _ _ hx]; unfold YM.Maxwell.grad D
  have e:0< ‖x‖:= norm_pos_iff.mpr hx
  have h := ( (((hasFDerivAt_inv (show ‖x‖^2≠0 by positivity)).comp x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt).pow n).const_mul normal).fderiv
  change fderiv ℝ (fun y:E4=> normal*(‖y‖^2)⁻¹ ^ n) x=_ at h; rw [h]; simp [YM.Maxwell.compAxis,two_smul,real_inner_comm x]
  rw [← real_inner_comm x,basis_inner]
  cases n <;> simp [pow_succ] <;> try ring
lemma axis_s (i) : stare (slope i)= (normal:ℂ) := by
  change (slope _).val _=_; rw [slope,lap _ _ exposed]; simp [apex,basis]
lemma power_age (U : K) (n : ℕ) (p) : (U^(n+1)) p=U ((U^n) p) := by rw [pow_succ',Module.End.mul_apply]
lemma clocks (m : ℕ) (i : Axis) (h : SmoothGap) :
    ((T i)^(m+1)) (Gap.times (clock i) h)= Gap.times (clock i) (((T i)^(m+1)) h) + ((m:ℂ)+1) • (((T i)^m) h) := by
  induction m with
  | zero => simp [Gap.keep,clockwork,tw,add_comm]
  | succ m IH=>
    rw [power_age (T i) (m+1),IH,map_add, Gap.keep, clockwork,if_pos rfl,tw,map_smul,← power_age (T i) m,← power_age]
    push_cast; simp only [add_smul,one_smul]; abel
lemma distinct (i j : Axis) (h : i≠j) : Commute (T i) (Gap.times (clock j)) := LinearMap.ext fun t=>by
  rw [Module.End.mul_apply,Module.End.mul_apply,Gap.keep,clockwork, if_neg (Ne.symm h),map_zero, LinearMap.zero_apply,zero_add]

lemma plane_zero (M : K) (i : Axis) (p : Commute M (Gap.times (clock i))) (h : SmoothGap) (he : τ ≠ i) : stare (M (Gap.times (clock i) h))=0 := by
  rw [show M (Gap.times _ _)=Gap.times _ (M h) from LinearMap.congr_fun p h, Gap.tick,lever, if_neg he,zero_mul]

-- Fast integer recursion, no branching in spatial powers. n DIV 2 gives order increases for even
/-- derivative of radial^-2n at other-axis with m x derivatives. -/
def image : ℕ → ℕ → ℤ
  | 0,_=>1
  | 1,_=>0
  | m+2,n=> (-2*n)*(m+1)*image m (n+1)
lemma spatial (M : K) (i : Axis) (p : τ≠i) (g : Commute M (Gap.times (clock i))) : ∀ (m n : ℕ),
    stare (M (((T i)^m) (slope n)))= (image m n:ℂ) * stare (M (slope (n+m/2)))
 | 0,n=> by simp [image]
 | 1,n=>by simp [image,rank,plane_zero M i g _ p]
 | m+2,n=>by
   rw [pow_succ, Module.End.mul_apply,rank,map_smul, clocks,map_smul,map_smul, map_add,map_smul,map_add,plane_zero M _ g _ p,map_smul,spatial M i p g m (n+1)]
   rw [image,show n+(m+2)/2=n+1+m/2 by omega]; push_cast; simp only [smul_eq_mul]; ring

def age : ℕ → ℕ → ℤ
  | 0,_=>1
  | 1,n=> -2*n
  | m+2,n=> -2*n*(age (m+1) (n+1) + (m+1)*age m (n+1))
lemma ages : ∀ m n : ℕ, stare (((T τ)^m) (slope n))=(age m n:ℂ)* (normal:ℂ)
  | 0,n=>by simp [age,axis_s]
  | 1,n=>by simp [age,rank,tick,lever,axis_s]
  | m+2,n=>by
    rw [pow_succ,Module.End.mul_apply,rank,map_smul,clocks,map_smul,map_add, map_smul,tick,lever, if_pos rfl,ages (m+1),ages m]
    rw [age]; push_cast; simp only [smul_eq_mul]; ring

/-- All four orders. -/
def normalOp (u v w b : ℕ) :=
  let m:=1+u/2; let n:=m+v/2; let k:=n+w/2
  image u 1 * image v m * image w n * age b k

lemma slope_pay (u v w b : ℕ) : stare (((T τ)^b) (((T 2)^w) (((T 1)^v) (((T 0)^u) stone))))=
    (normal:ℂ) * (normalOp u v w b:ℂ) := by
  rw [sheer]
  have he (m p:ℕ) (i j : Axis) (h : i≠j): Commute ((T i)^m) (Gap.times (clock j)):= (distinct i j h).pow_left _
  rw [← Module.End.mul_apply,← Module.End.mul_apply,spatial (((T τ)^b) * ((T 2)^w) * ((T 1)^v)) 0 (by decide) (Commute.mul_left (Commute.mul_left (he _ 0 _ _ (by decide)) (he _ 0 _ _ (by decide))) (he _ 0 _ _ (by decide))),
    Module.End.mul_apply, spatial (((T τ)^b) * ((T 2)^w)) 1 (by decide) (Commute.mul_left (he _ 0 _ _ (by decide)) (he _ 0 _ _ (by decide))), Module.End.mul_apply,
    spatial (((T τ)^b)) 2 (by decide) (he _ 0 _ _ (by decide)), ages]
  dsimp only [normalOp]; push_cast; ring
end
end YM.GaugeFieldConstruction.Wick
