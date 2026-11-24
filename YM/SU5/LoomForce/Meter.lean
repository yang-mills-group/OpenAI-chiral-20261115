import YM.SU5.LoomForce.SpinIncome
import YM.SU5.WakeInvestment.Dip

/-! book the polynomial-lenses on color components of combined calibration. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Lat Lattice Phase SU Rush Mir Reflect Lifted
open Regis.Wake (Paint)
open scoped Topology ContDiff BigOperators ENNReal InnerProductSpace Classical
section Poly
variable {α : Type*} [Fintype α] {d e : ℕ}{f g : (α → ℝ) → ℂ}{B C : ℝ}

lemma meterConst (c : ℂ)(d:ℕ) : Paint (fun _ : α → ℝ => c) d ‖c‖ := by
  refine ⟨contDiff_const, fun K p _ _=>le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ p),fun K p x y _ _=>?_⟩; rw [sub_self,norm_zero]; positivity
lemma meterPlus (h:Paint f d B) (p:Paint g d C) : Paint (fun x => f x+g x) d (B+C) := by
  refine ⟨h.bright.add p.bright,fun K t x u=>?_, fun K t x y a b=>?_⟩
  · rw [add_mul]; exact (norm_add_le ..).trans (add_le_add (h.worth K t x u) (p.worth K t x u))
  rw [←sub_add_sub_comm,add_mul,add_mul] -- name
  exact (norm_add_le ..).trans (add_le_add (h.price K t x y a b) (p.price K t x y a b))
lemma meterMul (h:Paint f d B)(p:Paint g e C) : Paint (fun x=> f x*g x) (d+e) (B*C + B*C) := by
  have hb:= h.nonneg; have hc:= p.nonneg
  have hu (x y : ℂ) : 0 ≤ ‖x-y‖ := norm_nonneg _
  refine ⟨h.bright.mul p.bright,fun K t x a =>?_, fun K t x y a b=>?_⟩
  · rw [pow_add,norm_mul]; let he:= mul_le_mul (h.worth K t x a) (p.worth K t x a) (norm_nonneg _)
      (by positivity : 0 ≤ B*K^d)
    apply he.trans; exact le_trans (le_of_eq (by ring : B*K^d*(C*K^e)=B*C*(K^d*K^e)))
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity))
  rw [pow_add, show f x*g x-f y*g y = (f x-f y)*g x+ f y*(g x-g y) by ring]
  apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]; apply le_trans (add_le_add (mul_le_mul
    (h.price K t x y a b) (p.worth K t x a) (norm_nonneg _) (by positivity))
    (mul_le_mul (h.worth K t y b) (p.price K t x y a b) (norm_nonneg _) (by positivity))); exact le_of_eq (by ring)
lemma meterScale (c : ℂ)(h:Paint f d B) : Paint (fun x=> c*f x) d (‖c‖*B) := by
  refine ⟨contDiff_const.mul h.bright,fun K t x u=> ?_,fun K t x y u v=>?_⟩
  · rw [norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (h.worth K t x u) (norm_nonneg _)
  rw [←mul_sub,norm_mul,mul_assoc ‖c‖,mul_assoc ‖c‖]; exact mul_le_mul_of_nonneg_left (h.price K t x y u v) (norm_nonneg _)
lemma meterCoordinate (i : α) : Paint (fun x:α→ℝ=> (↑(x i):ℂ)) 1 1 := by
  refine ⟨Complex.ofRealCLM.contDiff.comp (contDiff_apply _ _ i),fun K t x u=>?_, fun K t x y a b=>?_⟩
  · rw [one_mul,pow_one,Complex.norm_real]; exact (norm_le_pi_norm ..).trans u
  rw [one_mul,pow_one, ← Complex.ofReal_sub,Complex.norm_real]; exact (norm_le_pi_norm (x-y) i).trans (le_mul_of_one_le_left (norm_nonneg _) t)
lemma meterInc (h:Paint f d B)(p:d≤ e)(q:B ≤ C) : Paint f e C := ⟨h.bright,
  fun K t x a=> (h.worth K t x a).trans (mul_le_mul q (pow_le_pow_right₀ t p) (by positivity) (h.nonneg.trans q)),
  fun K t x y a b=> (h.price K t x y a b).trans (mul_le_mul_of_nonneg_right
     (mul_le_mul q (pow_le_pow_right₀ t p) (by positivity) (h.nonneg.trans q)) (norm_nonneg _))⟩
lemma meterTally {I : Type*}(L : List I) {f : I → (α → ℝ) → ℂ}(h: ∀ i∈L, Paint (f i) d B) :
    Paint (fun x=> Chain.tally L (fun i=> f i x)) d (L.length*B) := by
  induction L with
  | nil=> simpa using meterConst («α»:=α) 0 d
  | cons a L ih=>
    let g := meterPlus (h a List.mem_cons_self) (ih (fun i t=> h i (List.mem_cons_of_mem _ t)))
    refine meterInc g le_rfl (le_of_eq ?_); rw [List.length_cons]; push_cast; ring
end Poly

def lensPay {I : Type*} (Z : Chart (loomZ I)) (tag : I → Sewer) (L : List I) (q : ℝ)
    (x : loomG I → ℝ) := fullPay (q • x) Z tag L

def tollMeter (C q : ℝ) (n U : ℕ) := U * (C * (2*(1+q))^n)
section
variable {I:Type*} [Fintype I]
local notation "ULA" => loomG I → ℝ
lemma polynomial_step (L : List (loomG I)) (q : ℝ)(p:0 ≤ q) : Paint (fun x: ULA => ((((L.map (q • x)).prod:ℝ)):ℂ)) L.length ((2*(1+q))^L.length) := by
  induction L with
  | nil=> simpa using meterConst (α:=loomG I) 1 0
  | cons i L ih=>
    have hp : Paint (fun x : ULA=> ((q * x i:ℝ):ℂ)) 1 q := by
      simp_rw [Complex.ofReal_mul]; simpa only [Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg p,mul_one] using
         meterScale (q:ℂ) (meterCoordinate i)
    let C := (2*(1+q))^L.length; have he : 0 ≤ C := by unfold C; positivity
    let Z:= meterMul hp ih; simp_rw [List.map_cons,List.prod_cons, Complex.ofReal_mul]
    refine meterInc Z (by simp [Nat.add_comm]) ?_; rw [List.length_cons, pow_succ']; change q*C + q*C ≤ 2*(1+q)*C
    linarith only [p,he]
lemma meters (C q:ℝ)(p:0 ≤ q)(Z:Chart (loomZ I))(h:0 ≤ C)(tag:I→Sewer)(L:List I)
    (v:∀ i∈ booths tag L,‖quoteSpin i Z‖≤C) : Paint (lensPay Z tag L q) L.length
      (tollMeter C q L.length (booths tag L).length) := by
  apply meterTally (booths tag L) (f:=fun b x=> routePay (q • x) Z b)
  intro i u; let n:= L.length; have hp : (paperF i).length ≤ n:=by
    apply (paperF_length i).trans; unfold n; rw [←booth_node u,List.length_map]
  let t:=2*(1+q); refine meterInc (meterScale (quoteSpin i Z) (polynomial_step (paperF i) q p)) hp ?_; exact mul_le_mul (v i u) (pow_le_pow_right₀ (by linarith : 1 ≤ 2*(1+q)) hp) (by positivity) h
#print axioms meters
end
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
