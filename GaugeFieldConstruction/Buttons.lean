import GaugeFieldConstruction.FramesWick

/-!
# Differentiating in the away calculus in the expense coordinates
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Wick
open Gap Cauchy Row Complex Finset
open scoped BigOperators
local notation "A" => Module.End ℂ SmoothGap
/-- true = on second argument. -/
def foot (b : Bool) (i : Axis) : A := if b then Gap.step i else -Gap.step i
def mi (b : Bool) (n : MI) := foot b 0^n.1 * foot b 1^n.2.1 * foot b 2^n.2.2
lemma balance (a b : Bool) (x y : Axis) : Commute (foot a x) (foot b y) := by
  have h := collide x y
  cases a <;> cases b <;> simp only [foot,reduceCtorEq, ↓reduceIte]
  · exact LinearMap.ext (fun f=>by rw [Module.End.mul_apply,Module.End.mul_apply]; simp only [LinearMap.neg_apply,map_neg,neg_neg]; exact LinearMap.congr_fun h f)
  · exact LinearMap.ext (fun f=>by rw [Module.End.mul_apply,Module.End.mul_apply]; simp only [LinearMap.neg_apply,map_neg]; exact congr_arg Neg.neg (LinearMap.congr_fun h f))
  · exact LinearMap.ext (fun f=>by rw [Module.End.mul_apply,Module.End.mul_apply]; simp only [LinearMap.neg_apply,map_neg]; exact congr_arg Neg.neg (LinearMap.congr_fun h f))
  exact h
lemma foot_mi (b c : Bool) (i : Axis) (p) : Commute (foot b i) (mi c p) :=
  ((Commute.mul_right ((balance b c i 0).pow_right _) ((balance b c i 1).pow_right _)).mul_right ((balance b c i 2).pow_right _))
lemma mi_mi (b c : Bool) (p q) : Commute (mi b p) (mi c q) :=
  Commute.mul_left (Commute.mul_left ((foot_mi b c 0 q).pow_left _) ((foot_mi b c 1 q).pow_left _)) ((foot_mi b c 2 q).pow_left _)
lemma legs (t k i p f) : foot t i (mi k p f)=mi k p (foot t i f) := LinearMap.congr_fun (foot_mi t k i p) f
lemma recruit (t k p q f) : mi t p (mi k q f)=mi k q (mi t p f) := LinearMap.congr_fun (mi_mi t k p q) f
lemma bump_mi (b i n) : mi b (bump i n) = mi b n * foot b i.castSucc := by
  have he : i=0 ∨ i=1 ∨ i=2 := by fin_cases i <;> decide
  have hm (k i : Axis) (d : ℕ) : foot b k * foot b i^d=foot b i^d*foot b k := ((balance b b k i).pow_right d).eq
  rcases he with h|h|h <;> subst i
  · change foot b 0^(n.1+1) * foot b 1^n.2.1 * foot b 2^n.2.2= _ * foot b 0
    rw [mi,pow_succ,mul_assoc _ (foot b 0),hm, ← mul_assoc, mul_assoc _ (foot b 0),hm,← mul_assoc]
  · change foot b 0^n.1 * foot b 1^(n.2.1+1) * foot b 2^n.2.2=_ * foot b 1
    rw [mi,pow_succ,← mul_assoc, mul_assoc _ (foot b 1),hm, ← mul_assoc]
  change foot b 0^n.1 * foot b 1^n.2.1 * foot b 2^(n.2.2+1)= _ * foot b 2
  rw [mi,pow_succ,← mul_assoc]
lemma ends (b) : mi b 0=1 := by change _^0* _^0* _^0=1; simp

section
variable {t : Axis → Axis → SmoothGap}
namespace Solution
variable (h : Solution t)
def truck (b : Bool) (a : S3) : Axis×Axis := if b then ((cw a).castSucc,(ccw a).castSucc) else (τ,a.castSucc)
def reads (t : Axis → Axis → SmoothGap) (b : Bool) (a : S3) := t (truck b a).1 (truck b a).2
include h
lemma idle (i : Axis) : t i i=0 := by
  have he : (2:ℂ) • t i i=0 := by rw [two_smul]; nth_rw 1 [h.sign i i]; simp
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)
lemma cap (b : Bool) : (∑ i:S3, Gap.step i.castSucc (reads t b i)) = 0 := by
  have he (p : S3→SmoothGap) : ∑ i:S3,p i=p 0+(p 1+p 2) := by simp [Fin.sum_univ_succ]
  rw [he]; cases b
  · change Gap.step 0 (t τ 0)+(Gap.step 1 (t τ 1)+Gap.step 2 (t τ 2))=_
    have H : Gap.step 0 (t 0 τ)+(Gap.step 1 (t 1 τ)+(Gap.step 2 (t 2 τ)+Gap.step τ (t τ τ)))=0 := by
      simpa [Fin.sum_univ_succ,τ] using h.sum τ
    rw [h.sign τ 0,h.sign τ 1,h.sign τ 2,map_neg,map_neg,map_neg]
    rw [h.idle,map_zero,add_zero] at H
    simp only [← neg_add,H,neg_zero]
  change Gap.step 0 (t 1 2)+(Gap.step 1 (t 2 0)+Gap.step 2 (t 0 1))=_
  rw [← add_assoc]; exact h.closes ..

lemma charge (b c : Bool) : ∑ i:S3,foot b i.castSucc (reads t c i)=0 := by
  cases b
  · simp [foot,h.cap c]
  exact h.cap c

lemma blast (m : Bool) (i : S3) : Gap.step τ (reads t m i)=
    Gap.step (cw i).castSucc (reads t (!m) (ccw i))-Gap.step (ccw i).castSucc (reads t (!m) (cw i)) := by
  cases m
  · have he (i : Axis) : Gap.step 0 (t 0 i)+Gap.step 1 (t 1 i)+Gap.step 2 (t 2 i)+Gap.step τ (t τ i)=0 := by
      simpa [add_assoc,Fin.sum_univ_succ, τ] using h.sum i
    have ht : i=0 ∨ i=1 ∨ i=2 := by fin_cases i <;> decide
    rcases ht with g|g|g <;> subst i
    · change Gap.step τ (t τ 0) = Gap.step 1 (t 0 1)-Gap.step 2 (t 2 0)
      have hu:=he 0; rw [h.idle 0,map_zero,h.sign 1 0,map_neg] at hu
      rw [eq_neg_of_add_eq_zero_right hu]; abel
    · change Gap.step τ (t τ 1) = Gap.step 2 (t 1 2)-Gap.step 0 (t 0 1)
      have hu:=he 1; rw [h.idle 1,map_zero,h.sign 2 1,map_neg] at hu
      rw [eq_neg_of_add_eq_zero_right hu]; abel
    change Gap.step τ (t τ 2) = Gap.step 0 (t 2 0) - Gap.step 1 (t 1 2)
    have hu:= he 2; rw [h.idle 2,map_zero,h.sign 0 2,map_neg] at hu
    rw [eq_neg_of_add_eq_zero_right hu]; abel
  change Gap.step τ (t _ _) = Gap.step _ (t _ _) - Gap.step _ (t _ _)
  have he := h.closes τ (cw i).castSucc (ccw i).castSucc; rw [h.sign (ccw i).castSucc τ,map_neg,add_assoc] at he
  simp only [truck,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  rw [eq_neg_of_add_eq_zero_left he]; abel
lemma booster (b c) (i) : foot b τ (reads t c i)=foot b (cw i).castSucc (reads t (!c) (ccw i))-foot b (ccw i).castSucc (reads t (!c) (cw i)) := by
  cases b
  · simp only [foot, Bool.false_eq_true,↓reduceIte, LinearMap.neg_apply,h.blast c]; abel
  exact h.blast ..

def game (b : Bool) (t : Axis → Axis → SmoothGap) : GJet →ₗ[ℂ] SmoothGap := jet fun i => mi b i.2.val.2 (reads t i.1 i.2.val.1)

lemma fields (b c : Bool) (i : S3) (z : MI) : game b t (G c i z)=mi b z (reads t c i) := by
  unfold G; split_ifs with f
  · unfold game; exact on_ket ..
  simp only [map_neg,map_add,game,on_ket,bump_mi]
  push Not at f; rcases f with ⟨rfl,f⟩
  conv_rhs =>
    rw [show z = bump 2 (strip z) from Prod.ext rfl (Prod.ext rfl <| by
      change z.2.2=z.2.2-1+1; omega), bump_mi]
  have he := h.charge b c
  rw [show (∑ i:S3,foot b i.castSucc (reads t c i)) = (foot b 0 (reads t c 0)+foot b 1 (reads t c 1)+foot b 2 (reads t c 2)) by simp [Fin.sum_univ_succ,Chart.cast2,add_assoc]] at he -- adjust
  have hk := eq_neg_of_add_eq_zero_right he
  simp only [Module.End.mul_apply,Chart.cast0, Chart.cast1,Chart.cast2, hk, map_neg,map_add]

lemma moves (p : GJet) (i : Axis) (b) : game b t (Gder i p)=foot b i (game b t p) := by
  suffices H: game b t ∘ₗ Gder i= foot b i ∘ₗ game b t by exact LinearMap.congr_fun H _
  apply ket_ext; intro u
  simp only [LinearMap.comp_apply]
  refine Fin.lastCases (i:=i) ?_ fun k => ?_
  · change game _ _ (Gder τ _)= foot b τ _
    rw [Glast,Gtime,on_ket]; dsimp only; rw [map_sub]
    rw [h.fields b,h.fields b,bump_mi,bump_mi,game,on_ket,legs, h.booster]
    simp only [Module.End.mul_apply,map_sub]
  rw [Gspace, Gshift,on_ket,h.fields]
  rw [game,on_ket,bump_mi,legs]; rfl

lemma cards (b : Bool) (i j : Axis) (n) : game b t (F i j n)=mi b n (t i j) := by
  refine Fin.lastCases (i:=i) ?_ fun u=>?_ <;> refine Fin.lastCases (i:=j) ?_ fun v=>?_
  all_goals simp only [F, Fin.lastCases_castSucc, Fin.lastCases_last]
  · rw [h.idle,map_zero,map_zero]
  · exact h.fields ..
  · rw [map_neg,h.fields,h.sign u.castSucc,map_neg]; rfl
  by_cases p : u=v
  · subst v; rw [if_pos rfl, map_zero,h.idle,map_zero]
  rw [if_neg p]; by_cases g : v=cw u
  · subst v; rw [if_pos rfl,h.fields]; congr 1; fin_cases u <;> rfl
  rw [if_neg g,map_neg,h.fields,h.sign u.castSucc,map_neg]
  congr 2
  have he : u=cw v := by fin_cases u <;> fin_cases v <;> simp_all [cw] <;> contradiction
  subst u; fin_cases v <;> rfl
end Solution
end
namespace Braid
variable {d : Bool} {T : Spin → SmoothGap} (H : ∀ a, ∑ i:Axis, ∑ c:Spin, coeffCR d i a c • Gap.step i (T c)=0)
def book (b : Bool) (T : Spin → SmoothGap) : CJet →ₗ[ℂ] SmoothGap := jet fun i=> mi b i.2 (T i.1)
lemma desk (b : Bool) (T : Spin→SmoothGap) (a n) : book b T (C a n)= mi b n (T a) := on_ket ..
include H
lemma drive (b : Bool) (p : CJet) (i : Axis) : book b T (Cder d i p)=foot b i (book b T p) := by
  suffices h: book b T ∘ₗ Cder d i= foot b i ∘ₗ book b T by exact LinearMap.congr_fun h p
  apply ket_ext; intro j
  simp only [LinearMap.comp_apply]
  have he : ket j=C j.1 j.2:=rfl
  refine Fin.lastCases (i:=i) ?_ fun k=>?_
  · change book _ _ (Cder d τ _)=foot b τ _
    have hp (a) : (∑ i:S3,∑ c:Spin, coeffCR d i.castSucc a c • foot b i.castSucc (T c))+ foot b τ (T a)=0 := by
      have h :∑ i:Axis,∑ c: Spin, coeffCR d i a c • foot b i (T c)=0 := by
        cases b
        · simp only [foot, Bool.false_eq_true, ↓reduceIte, LinearMap.neg_apply,smul_neg,sum_neg_distrib,H,neg_zero]
        exact H a
      rw [Fin.sum_univ_castSucc] at h
      have hr : ∑ c:Spin, coeffCR d (Fin.last 3) a c • foot b (Fin.last 3) (T c)=foot b τ (T a) := by
        rw [show Fin.last 3=τ from rfl]
        cases d <;> fin_cases a <;> simp [coeffCR,Hij,τ]
      rwa [hr] at h
    rw [Clast,Ctime,on_ket,map_neg, he, desk]; simp_rw [map_sum,map_smul,desk,bump_mi]
    rw [legs,eq_neg_of_add_eq_zero_right (hp j.1)]; simp only [map_neg,map_sum,map_smul,Module.End.mul_apply]
  rw [Cspace,Cshift,on_ket,he,desk,desk,bump_mi, legs]; rfl
end Braid
end YM.GaugeFieldConstruction.Wick
