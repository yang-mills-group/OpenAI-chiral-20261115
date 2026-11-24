import GaugeFieldConstruction.ProductData

/-!
# Signed moves of a curvature leg
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Cauchy
open Function Finset
open scoped BigOperators Matrix
namespace Maxwell
abbrev Ang := Axis → Axis → ℂ
def skin (w : Maxwell) : Ang := spinfield w.a
structure Bianchi (p : P4) (x : Ang) : Prop where
  alt (i j) : x i j= -x j i
  closed (i j k) : p i*x j k + p j*x k i + p k*x i j=0
  div (i) : ∑ k, p k * x k i = 0

open Chart (cw0 cw1 cw2 ccw0 ccw1 ccw2 cast2)
private lemma cycle (i : S3) : cw (cw i)=ccw i := by fin_cases i <;> rfl
private lemma cyclic (i : S3) : cw (ccw i)=i := by fin_cases i <;> rfl
private lemma cir (i : S3) : ccw (cw i)=i := by fin_cases i <;> rfl
private lemma differs (i : S3) : cw i ≠ ccw i := by fin_cases i <;> decide
private lemma three' (i j : S3) : i=j ∨ cw i=j ∨ ccw i=j := by fin_cases i <;> fin_cases j <;> decide
lemma earth (a : Bool → Sp) (i : S3) : spinfield a τ i.castSucc=a false i := by
  change spinfield a (Fin.last 3) _=_; simp only [spinfield,Fin.lastCases_last,Fin.lastCases_castSucc]
lemma magnet (a : Bool → Sp) (i : S3) : spinfield a (cw i).castSucc (ccw i).castSucc=a true i := by
  simp [spinfield,differs,cycle,show ccw (cw i)=i from cir i]
lemma alternate (a : Bool → Sp) (i j : Axis) : spinfield a i j = -spinfield a j i := by
  refine Fin.lastCases (i:=i) ?_ fun i' => ?_ <;> refine Fin.lastCases (i:=j) ?_ fun j' => ?_
  all_goals simp only [spinfield,Fin.lastCases_castSucc,Fin.lastCases_last, neg_neg, neg_zero]
  have h (s t : S3) : (if s=t then 0 else if t=cw s then a true (ccw s) else -a true (ccw t)) =
      -(if t=s then 0 else if s=cw t then a true (ccw t) else -a true (ccw s)) := by
    by_cases e : t=s
    · subst t; simp
    rcases three' s t with u|u|u
    · exact (e u.symm).elim
    · have p : s≠cw t := by rw [← u,cycle]; fin_cases s <;> decide
      rw [if_neg (Ne.symm e), if_pos u.symm, if_neg e, if_neg p, neg_neg]
    have p : t≠cw s := by rw [← u]; exact (differs s).symm
    have w : s=cw t := by rw [← u,cyclic]
    rw [if_neg (Ne.symm e),if_neg p,if_neg e, if_pos w]
  exact h _ _

-- Finite coordinate proofs with concrete components
private lemma shape (w : Maxwell) :
    w.skin 0 0 = 0 ∧ w.skin 1 1=0 ∧ w.skin 2 2=0 ∧ w.skin τ τ=0 ∧
    w.skin τ 0=w.a false 0 ∧ w.skin τ 1=w.a false 1 ∧ w.skin τ 2=w.a false 2 ∧
    w.skin 0 τ= -w.a false 0 ∧ w.skin 1 τ= -w.a false 1 ∧ w.skin 2 τ= -w.a false 2 ∧
    w.skin 1 2=w.a true 0 ∧ w.skin 2 0=w.a true 1 ∧ w.skin 0 1=w.a true 2 ∧
    w.skin 2 1= -w.a true 0 ∧ w.skin 0 2= -w.a true 1 ∧ w.skin 1 0= -w.a true 2 := by
  refine ⟨rfl,rfl,rfl,rfl,earth w.a 0,earth w.a 1, earth w.a 2, ?_, ?_, ?_,
    magnet w.a 0,magnet w.a 1,magnet w.a 2, ?_,?_,?_⟩ <;> rfl
private lemma shelf (i : Axis) : i=0 ∨ i=1 ∨ i=2 ∨ i=τ := by fin_cases i <;> decide
private lemma spatially (p : P4) (x : Sp) (α : ℂ)
    (he : p 0*x 0+(p 1*x 1+p 2*x 2)=α) : ∑ i : S3,p i.castSucc*x i=α := by
  simpa [Fin.sum_univ_succ] using he

private lemma sortedClosed (w : Maxwell) (i j k : Axis) (h : i<j) (m : j<k) :
    w.p i * w.skin j k + w.p j*w.skin k i + w.p k*w.skin i j=0 := by
  rcases shelf i with hh|hh|hh|hh <;> rcases shelf j with hv|hv|hv|hv <;>
    rcases shelf k with ht|ht|ht|ht <;> subst i <;> subst j <;> subst k <;> try contradiction
  all_goals
    have hx := shape w
    have he (i : S3) := w.curl true i
    have Hy : w.p 0*w.a true 0 + (w.p 1*w.a true 1+w.p 2*w.a true 2) = 0 := by
      simpa [Fin.sum_univ_succ] using w.charge true
    have u : w.p τ * w.a true 0 = w.p 1*w.a false 2-w.p 2*w.a false 1 := he 0
    have v : w.p τ * w.a true 1 = w.p 2*w.a false 0-w.p 0*w.a false 2 := he 1
    have l : w.p τ * w.a true 2 = w.p 0*w.a false 1-w.p 1*w.a false 0 := he 2
    simp only [hx] -- `simp only [hx]`
    first | linear_combination Hy | linear_combination u | linear_combination -v | linear_combination l

lemma rigor (w : Maxwell) : Bianchi w.p w.skin := by
  have ha (i j) : w.skin i j= -w.skin j i := alternate w.a i j
  have hx (i) : w.skin i i=0 := by linear_combination ha i i/2
  constructor
  · exact ha
  · intro i j k
    rcases lt_trichotomy i j with h|h|h
    · rcases lt_trichotomy j k with v|v|v
      · exact sortedClosed w i j k h v
      · subst k; rw [hx, ha j i]; ring
      rcases lt_trichotomy i k with hp|hp|hp
      · have ht := sortedClosed w i k j hp v
        rw [ha j k, ha k i, ha i j]; linear_combination -ht
      · subst k; rw [hx, ha j i]; ring
      have ht := sortedClosed w k i j hp h; linear_combination ht
    · subst j; rw [hx,ha k i]; ring
    rcases lt_trichotomy i k with v|v|v
    · have ht := sortedClosed w j i k h v
      rw [ha j k,ha k i,ha i j]; linear_combination -ht
    · subst k; rw [hx,ha j i]; ring
    rcases lt_trichotomy j k with hp|hp|hp
    · have ht := sortedClosed w j k i hp v; linear_combination ht
    · subst k; rw [hx,ha j i]; ring
    have ht := sortedClosed w k j i hp h
    rw [ha j k,ha k i,ha i j]; linear_combination -ht
  intro i
  have h : ∑ k, w.p k * w.skin k i = w.p 0*w.skin 0 i+(w.p 1*w.skin 1 i+
      (w.p 2*w.skin 2 i + w.p τ*w.skin τ i)) := by simp [Fin.sum_univ_succ,τ]
  rw [h]
  have s := shape w
  rcases shelf i with e|e|e|e <;> rw [e] <;> simp only [s]
  · have t : w.p τ*w.a false 0 = w.p 1*w.a true 2 - w.p 2*w.a true 1 := w.curl false 0
    linear_combination t
  · have t : w.p τ*w.a false 1 = w.p 2*w.a true 0 - w.p 0*w.a true 2 := w.curl false 1
    linear_combination t
  · have t : w.p τ*w.a false 2 = w.p 0*w.a true 1 - w.p 1*w.a true 0 := w.curl false 2
    linear_combination t
  have he := w.charge false
  simp [Fin.sum_univ_succ] at he; linear_combination -he

-- inverse: realizing a turned test as Maxwell
variable {p : P4} {X : Ang} (H : Bianchi p X)

def contents (X : Ang) (mask : Bool) (i : S3) :=
  if mask then X (cw i).castSucc (ccw i).castSucc else X τ i.castSucc
namespace Bianchi
lemma create (h : Bianchi p X) (i j : Axis) : spinfield (contents X) i j=X i j := by
  have hh (i) : X i i=0 := by linear_combination h.alt i i/2
  refine Fin.lastCases (i:=i) ?_ fun a => ?_ <;> refine Fin.lastCases (i:=j) ?_ fun b => ?_
  · rw [hh]; rfl
  · exact earth ..
  · rw [alternate, show Fin.last 3=τ from rfl, earth]
    exact (h.alt ..).symm
  rcases three' a b with e|e|e <;> subst b
  · simp [hh,spinfield]
  · have hv := magnet (contents X) (ccw a)
    change spinfield _ _ _ = X _ _ at hv; rwa [cyclic,show ccw (ccw a)=cw a by fin_cases a <;> rfl] at hv
  have hv := magnet (contents X) (cw a); change spinfield _ _ _ = X _ _ at hv
  rw [cir, cycle] at hv
  rw [alternate,hv,h.alt a.castSucc]; -- may rewrites RHS

def point (h : Bianchi p X) : Maxwell where
  p:=p
  a:=contents X
  charge mask:=by
    have eh (i) : X i i=0 := by linear_combination h.alt i i/2
    cases mask
    · apply spatially
      change p 0*X τ 0 + (p 1*X τ 1+p 2*X τ 2)=_
      have H : p 0*X 0 τ+(p 1*X 1 τ+(p 2*X 2 τ+p τ*X τ τ))=0 := by
        simpa [Fin.sum_univ_succ,τ] using h.div τ
      rw [eh] at H
      rw [h.alt τ 0,h.alt τ 1,h.alt τ 2]; linear_combination -H
    apply spatially; change p 0*X 1 2+(p 1*X 2 0+p 2*X 0 1)=_
    rw [← add_assoc]; exact h.closed ..
  curl mask i:=by
    cases mask
    · have he := h.div i.castSucc; have hv := h.create
      have eh (k : Axis) : ∑ a, p a * X a k=p 0*X 0 k+(p 1*X 1 k +(p 2*X 2 k+p τ*X τ k)) := by
        simp [Fin.sum_univ_succ,τ]
      have hh (j) : X j j=0 := by linear_combination h.alt j j/2
      have ti : i=0 ∨ i=1 ∨ i=2 := by fin_cases i <;> decide
      rcases ti with ti|ti|ti <;> subst i
      · change p τ*X τ 0=p 1*X 0 1-p 2*X 2 0
        have hx := h.div 0; rw [eh,hh,h.alt τ 0, h.alt 1 0] at hx
        rw [h.alt τ 0]; linear_combination hx
      · change p τ*X τ 1=p 2*X 1 2-p 0*X 0 1
        have hx := h.div 1; rw [eh,hh,h.alt 2 1] at hx; linear_combination hx
      change p τ*X τ 2=p 0*X 2 0-p 1*X 1 2
      have hx := h.div 2; rw [eh,hh,h.alt 0 2] at hx; linear_combination hx
    change p τ * X _ _ = p _ * X _ _ - p _ * X _ _
    have he := h.closed τ (cw i).castSucc (ccw i).castSucc
    rw [h.alt (ccw i).castSucc τ] at he; linear_combination he
end Bianchi

-- displacement frames
private lemma pa (s : Signed) (p : P4) (a) : s⁻¹.act p a=pay (s.flip a) (p (s.perm a)) := by
  simp [Signed.act,pay]
def turnd (s : Signed) (w : Maxwell) (i j : Axis) := pay ((s.flip i).xor (s.flip j)) (w.skin (s.perm i) (s.perm j))
lemma still (s : Signed) (w : Maxwell) : Bianchi (s⁻¹.act w.p) (turnd s w) := by
  constructor
  · intro i j; unfold turnd
    have h:= w.rigor.alt (s.perm i) (s.perm j)
    cases s.flip i <;> cases s.flip j <;> simp [h]
  · intro i j k; unfold turnd; rw [pa,pa,pa]
    have h := w.rigor.closed (s.perm i) (s.perm j) (s.perm k)
    cases s.flip i <;> cases s.flip j <;> cases s.flip k <;> simp only [Bool.true_xor,
      Bool.false_xor,Bool.not_false,Bool.not_true,pay_false,pay_true]
    all_goals first | linear_combination h | linear_combination -h
  intro i; unfold turnd
  have h := w.rigor.div (s.perm i)
  rw [← Equiv.sum_comp s.perm (fun k => w.p k * w.skin k (s.perm i))] at h
  have hv (k) : (s⁻¹.act w.p k * pay ((s.flip k).xor (s.flip i)) (w.skin (s.perm k) (s.perm i))) =
      pay (s.flip i) (w.p (s.perm k)*w.skin (s.perm k) (s.perm i)) := by
    rw [pa]; cases s.flip i <;> cases s.flip k <;> simp
  simp_rw [hv]
  cases s.flip i <;> simp [h]

open Row Raw Labels
/-- Turn target test to the original frame; `arc` transforms as a
 2-form. -/
lemma turns (s : Signed) (w : Maxwell) (i : Wed) : (still s w).point.read (arc i) =
    pay (wedAct.cost s i) (w.read (arc (wedAct.move s i))) := by
  unfold arc; rw [Maxwell.read_F, Maxwell.read_F]
  let a := i.toBlade.val.1; let b := i.toBlade.val.2
  change spinfield (contents (turnd s w)) a b * _ = _
  rw [Bianchi.create]
  · simp only [power]; simp only [Prod.fst_zero, Prod.snd_zero, pow_zero, mul_one] -- fin
    change pay ((s.flip a).xor (s.flip b)) _ = pay
      ((reverseBit (s.perm a) (s.perm b)).xor ((s.flip a).xor (s.flip b)))
       (w.skin (blade (s.perm a) (s.perm b) (s.perm.injective.ne i.toBlade.property.ne)).val.1 (blade (s.perm a) (s.perm b) (s.perm.injective.ne i.toBlade.property.ne)).val.2)
    unfold blade; split_ifs with h
    · rw [reverseBit, decide_eq_true h]
      have hf := w.rigor.alt (s.perm b) (s.perm a)
      dsimp only
      rw [hf]
      cases ((s.flip a).xor (s.flip b)) <;> simp
    rw [reverseBit, decide_eq_false h]; simp
  exact still s w
end Maxwell
end YM.GaugeFieldConstruction.Cauchy
