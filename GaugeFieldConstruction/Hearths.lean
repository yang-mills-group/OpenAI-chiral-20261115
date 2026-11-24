import GaugeFieldConstruction.Odour

/-!
# Link triangle contractions. x target, y outside. z initial stress slot.
  callback p sign spin lamp. -/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Complex Cauchy Row Wick Phys Function Filter Set
open YM.Maxwell (grad)
open scoped Topology BigOperators ContDiff
variable {α β γ η : Type*} {p : Wick.Bil α β} {q : Wick.Bil γ η}
    {dv : Axis → Module.End ℂ (J β)}

def orient (p : Wick.Bil α β) (q : Wick.Bil γ η) (z x y : E4) :
    J (α×γ) →ₗ[ℂ] Coupon β η := jet fun a=> (LinearMap.mul ℂ ℂ).compl₁₂
      (eye (x-z) ∘ₗ p (ket a.1)) (eye (y-z) ∘ₗ q (ket a.2))
lemma pair_up (a b c d) (z x y): orient p q z x y (times' a b) c d=
    eye (x-z) (p a c)*eye (y-z) (q b d) := by
  have h : ∀ a b, orient p q z x y (times' (ket a) (ket b)) c d=eye (x-z) (p (ket a) c)*eye (y-z) (q (ket b) d) := by intro a b; rw [takes,orient,on_ket]; rfl
  let X : J (α×γ) →ₗ[ℂ] ℂ := ((orient p q z x y).flip c).flip d
  have hw : productRead (eye (x-z) ∘ₗ p.flip c) (eye (y-z) ∘ₗ q.flip d)=X := crossing (fun i j=>
    (read_times (eye (x-z) ∘ₗ p.flip c) (eye (y-z) ∘ₗ q.flip d) (ket i) (ket j)).trans (h i j).symm)
  change X _= _; rw [← hw]; exact read_times (eye (x-z) ∘ₗ p.flip c) (eye (y-z) ∘ₗ q.flip d) a b -- adjust h
lemma everywhere (p : Wick.Bil α β) (q : Wick.Bil γ η) (a b c) {t z y : E4} (h : z≠y) (j : z≠t): ContinuousAt (fun w : E4×E4 => orient p q w.2 w.1 y a b c) (t,z) := by
  have he k : ContinuousAt (fun w : E4×E4=>eye (w.1-w.2) (p (ket k) b)) (t,z) := (Gap.healthy (p (ket k) b) (x:= t-z) (sub_ne_zero.mpr j.symm)).continuousAt.comp (x:=(t,z)) (continuousAt_fst.sub continuousAt_snd)
  have hp k :ContinuousAt (fun w : E4×E4=> eye (y-w.2) (q (ket k) c)) (t,z) := (propL (q (ket k) c) h).continuousAt.comp (x:=(t,z)) (g:=fun u => eye (y-u) (q (ket k) c)) (f:=Prod.snd) continuousAt_snd
  induction a using Finsupp.induction_linear with
  | zero=> simp; exact continuousAt_const
  | add a b p q=>simp only [map_add,LinearMap.add_apply]; exact p.add q
  | single i s=>
    rw [show Finsupp.single i s=s • ket i from by simp [ket]]; simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]; rw [← takes i.1 i.2]
    simp_rw [pair_up]; exact continuousAt_const.mul ((he i.1).mul (hp i.2))
lemma heading (p : Wick.Bil α β) (q : Wick.Bil γ η) (H : ∀ i a b, Gap.step i (p a b)=p a (dv i b))
    (x v t z y a b c) (g : z≠road x v t): HasDerivAt (fun t:ℝ=>orient p q z (road x v t) y a b c)
    (orient p q z (road x v t) y a (dv v b) c) t := by
  have he i: HasDerivAt (fun u=>eye ((road x v u)-z) (p (ket i) b)) (eye ((road x v t)-z) (p (ket i) (dv v b))) t := by
    refine speedy (F:=fun u=>eye (u-z) (p (ket i) b)) (propR g) |>.congr_deriv ?_
    rw [propR' _ _ g,H]
  induction a using Finsupp.induction_linear with
  | zero=> simpa only [map_zero,LinearMap.zero_apply] using! hasDerivAt_const t (0:ℂ)
  | add a b p q=>simp only [map_add,LinearMap.add_apply]; exact p.add q
  | single i s=>
    rw [show Finsupp.single i s=s • ket i from by simp [ket]]; simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]; rw [← takes i.1 i.2]; simp_rw [pair_up]
    exact HasDerivAt.const_mul s ((he i.1).mul_const _)

-- Payout per designated target leg already contracted with stress.
def FG (z x y : E4) : J GaugePair→ₗ[ℂ] Coupon Pen Pen :=
  orient ge ge z x y + orient ge ge z x y ∘ₗ Phys.swap Pen
lemma overpay (a b c d : PW) (z x y): FG z x y (times' a b) c d=
    eye (x-z) (ge a c)*eye (y-z) (ge b d) + eye (x-z) (ge b c)*eye (y-z) (ge a d) := by
  simp only [FG,LinearMap.add_apply,LinearMap.comp_apply,Phys.swap_apply,pair_up]
/-- for C_b target (b is Bool), choose which stress leg contracts at x. If C,
 the second (R). If R, first, and get minus from crossing Wick. -/
def FF (d : Bool) (z x y : E4) : J Spair →ₗ[ℂ] Coupon Mode Mode :=
    if d then -orient (yarn false) (yarn true) z x y else orient (yarn true) (yarn false) z x y ∘ₗ Phys.swap Mode
lemma days (a b : FW) (z x y i j) : FF false z x y (times' a b) i j=eye (x-z) (yarn true b i)*eye (y-z) (yarn false a j) := by rw [FF,if_neg Bool.false_ne_true,LinearMap.comp_apply,Phys.swap_apply,pair_up]
lemma sigh (a b : FW) (z x y i j) : FF true z x y (times' a b) i j = -(eye (x-z) (yarn false a i)*eye (y-z) (yarn true b j)) := by simp only [FF,↓reduceIte, LinearMap.neg_apply,pair_up]

def Flash (T : Axis→Axis→J GaugePair) : Lamp Pen Pen where
  pay:= ge; P:=lace; fast i a b:= baseG ..
  charge z x y i j:= FG z x y (T i j)
  cont _ p q i j a b := by simp only [FG,LinearMap.add_apply, LinearMap.comp_apply]; exact (everywhere _ _ _ _ _ p q).add (everywhere _ _ _ _ _ p q)
  climb x v t y z _ p q i j a b := by
    simp only [FG,LinearMap.add_apply, LinearMap.comp_apply]
    have ht (X) := heading ge ge (fun i a b=>(topG i a b).symm) x v t z y X a b q
    exact (ht (T i j)).add (ht _)

def Glove (T : Axis→Axis→J Spair) (d : Bool) : Lamp Mode Mode where
  pay:= yarn d; P:=stride d; fast i:=baseF d i
  charge z x y i j:= FF d z x y (T i j)
  cont _ p q i j a b := by
    cases d <;> simp only [FF,Bool.false_eq_true,↓reduceIte,LinearMap.neg_apply,LinearMap.comp_apply]
    · exact everywhere _ _ _ _ _ p q
    exact (everywhere _ _ _ _ _ p q).neg
  climb x v t y z _ p q i j a b := by
    cases d
    · exact heading (yarn true) _ (fun i a b=>(topF true i a b).symm) x v t z y (Phys.swap Mode (T i j)) a b q
    exact (heading (yarn false) (yarn true) (fun i a b=>(topF false i a b).symm) x v t z y (T i j) a b q).neg
end YM.GaugeFieldConstruction.Flux.One
