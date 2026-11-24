import GaugeFieldConstruction.CauchyData
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# U1: dense chart of RankSupplement

We can use ℂ. Keep variables and orientations in the order in
RankSupplement. For each leg translation is one factor of `mom`. Need only the
portion of the chart over non-isotropic generic spatial projections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Finset Function Complex
open scoped BigOperators
namespace Cauchy
structure Chart where
  l : ℂ
  a : ℂ
  b : ℂ
namespace Chart
variable (c : Chart)
def mom : P4 := fun i => c.l *
  ![ (c.b+c.a)*I,c.a-c.b,(1-c.a*c.b)*I, 1+c.a*c.b] i -- tweak

def pol (tag : Bool) : Spin → ℂ := if tag then ![-c.b,1] else ![-c.a,1]

theorem chiral (tag : Bool) (a : Spin) : ∑ i : Axis, ∑ j : Spin, c.mom i * c.pol tag j * coeffCR tag i a j = 0 := by
  cases tag <;> fin_cases a <;>
    norm_num [mom, Hij,pol,coeffCR,Fin.sum_univ_succ] <;> ring_nf <;> simp

def fermi (tag : Bool) : Weyl tag := ⟨c.mom,c.pol tag,c.chiral tag⟩

/-- w used in testing an F leg. Flag false for d/dA, true B. -/
def vel (flag : Bool) (i : Axis) : ℂ := c.l*
  (if flag then ![I,-1, -I*c.a,c.a] else ![I,1,-I*c.b,c.b]) i

def area (p w : P4) (i j : Axis) : ℂ := p i * w j - p j * w i

def emit (flag mask : Bool) (i : S3) :=
  if mask then area c.mom (c.vel flag) (cw i).castSucc (ccw i).castSucc else
    area c.mom (c.vel flag) τ i.castSucc

/-- Electric component divided through by l². Useful for the
chart-separation argument. -/
def ray (flag : Bool) (x : ℂ) : Sp :=
  ![ I*(1-x^2), pay flag (1+x^2), -2*I*x]

-- Fin cast simp tags
lemma cw0 : cw 0 = 1 := rfl
lemma cw1 : cw 1 = 2 := rfl
lemma cw2 : cw 2 = 0 := rfl
lemma ccw0 : ccw 0 = 2 := rfl
lemma ccw1 : ccw 1 = 0 := rfl
lemma ccw2 : ccw 2 = 1 := rfl
lemma cast0 : Fin.castSucc (0:S3) = 0 := rfl
lemma cast1 : Fin.castSucc (1:S3) = 1 := rfl
lemma cast2 : Fin.castSucc (2:S3) = 2 := rfl
-- Ensure `norm_num` before `ring` uses numerals consistently

private lemma electrical' (flag : Bool) :
    let z := if flag then c.a else c.b; let D := c.emit flag false
    (D 0 = c.l^2 * ray flag z 0) ∧ (D 1 = c.l^2 * ray flag z 1) ∧ (D 2 = c.l^2 * ray flag z 2) := by
  cases flag <;>
    simp [ray,emit,area,mom,vel,τ,cast2] <;> (repeat' constructor) <;> ring_nf

theorem electrical (flag : Bool) (i : S3) :
    c.emit flag false i = c.l^2 * ray flag (if flag then c.a else c.b) i := by
  have h := c.electrical' flag
  fin_cases i; exact h.1; exact h.2.1; exact h.2.2

private lemma magnetic' (flag : Bool) :
    let D := c.emit flag
    (D true 0=pay (!flag) (D false 0)) ∧ (D true 1=pay (!flag) (D false 1)) ∧
      (D true 2=pay (!flag) (D false 2)) := by
  cases flag <;>
    simp [emit,area,mom,vel,τ,cw0,cw1,cw2,ccw0,ccw1,ccw2,cast2] <;>
    (repeat' constructor) <;> ring_nf <;> (try simp; try ring)
lemma magnetic (flag : Bool) (i : S3) : c.emit flag true i=pay (!flag) (c.emit flag false i) := by
  have h := c.magnetic' flag; fin_cases i; exact h.1; exact h.2.1; exact h.2.2

lemma perpendicular (flag mask : Bool) : ∑ k:S3,c.mom k.castSucc * c.emit flag mask k = 0 := by
  cases mask <;> cases flag <;>
    simp [magnetic,electrical,mom,ray, Fin.sum_univ_succ] <;> ring_nf <;> try simp

lemma flux (flag mask : Bool) (i : S3) : c.mom τ * c.emit flag mask i =
    c.mom (cw i).castSucc * c.emit flag (!mask) (ccw i) -
    c.mom (ccw i).castSucc * c.emit flag (!mask) (cw i) := by
  suffices ∀ j : S3, j=0 ∨ j=1 ∨ j=2 →
      c.mom τ * c.emit flag mask j = c.mom (cw j).castSucc * c.emit flag (!mask) (ccw j) -
      c.mom (ccw j).castSucc * c.emit flag (!mask) (cw j) from this i (by fin_cases i <;> decide)
  rintro j (rfl|rfl|rfl) <;> cases flag <;> cases mask <;>
    simp [cw0,cw1,cw2,ccw0,ccw1,ccw2,cast2,τ,magnetic,electrical,mom,ray] <;>
    ring_nf <;> (try simp; try ring)

def face (flag : Bool) : Maxwell :=
  ⟨c.mom,c.emit flag,c.perpendicular flag,c.flux flag⟩
lemma wedge_formula (c : Chart) (flag : Bool) (i j : Axis) (z : MI) :
    (c.face flag).read (F i j z)=area c.mom (c.vel flag) i j * power c.mom z := by
  rw [Maxwell.read_F]
  congr 1
  have he (p q : P4) (i j : Axis) : spinfield (fun mask : Bool => fun f : S3 =>
      if mask then area p q (cw f).castSucc (ccw f).castSucc else area p q τ f.castSucc) i j = area p q i j := by
    refine Fin.lastCases (i:=i) ?_ fun a => ?_ <;> refine Fin.lastCases (i:=j) ?_ fun b => ?_ <;>
      simp only [spinfield,Fin.lastCases_last,Fin.lastCases_castSucc]
    · simp [area]
    · simp only [Bool.false_eq_true, ↓reduceIte]; rfl
    · change -(area p q (Fin.last 3) _) = _; rw [area,area]; ring
    · have h (a b : S3) (u : a=0 ∨ a=1 ∨ a=2) (v : b=0 ∨ b=1 ∨ b=2) :
          (if a=b then (0:ℂ) else if b=cw a then area p q (cw (ccw a)).castSucc (ccw (ccw a)).castSucc else
          -area p q (cw (ccw b)).castSucc (ccw (ccw b)).castSucc)=area p q a.castSucc b.castSucc := by
        rcases u with rfl|rfl|rfl <;> rcases v with rfl|rfl|rfl <;>
          simp (config:={decide:=true}) [area,cw0,cw1,cw2,ccw0,ccw1,ccw2]
      exact h a b (by fin_cases a <;> decide) (by fin_cases b <;> decide)
  exact he _ _ _ _

def broad (q : Sp) (t : ℂ) : P4 := ![q 0,q 1,q 2,t]
theorem spatial_broad (q : Sp) (t : ℂ) (i : S3) : broad q t i.castSucc=q i := by
  fin_cases i <;> rfl
abbrev norm3 (q : Sp) := q 0 ^2 + q 1 ^2 + q 2 ^2
def RegularQ (q : Sp) := q 0 ^2 + q 1 ^2 ≠ 0 ∧ norm3 q ≠ 0

/-- Given a regular spatial projection, on-shell charts over both roots. -/
structure Both (q : Sp) where
  t : ℂ
  hi : t ≠ 0
  u : Chart
  v : Chart
  line : u.mom=broad q t
  raym : v.mom=broad q (-t)
  hl : u.l≠0
  kl : v.l≠0
  diffA : u.a≠v.a
  diffB : u.b≠v.b

private lemma obtains (q : Sp) (h : RegularQ q) (t : ℂ) (ht : t^2= -norm3 q) :
    ∃ c : Chart, c.mom=broad q t ∧ c.l≠0 := by
  let T := t-I*q 2
  have hT : T≠0 := by
    intro hu
    have hp : t=I*q 2 := sub_eq_zero.mp hu
    rw [hp,mul_pow,I_sq] at ht
    apply h.1
    dsimp [norm3] at ht; linear_combination ht
  let a := (q 1-I*q 0)/T; let b := (-q 1-I*q 0)/T
  refine ⟨⟨T/2,a,b⟩, ?_, div_ne_zero hT (by norm_num)⟩
  ext1 i
  have hc : T=t-I*q 2 := rfl
  have h2 := h.2
  dsimp [norm3] at ht h2
  have hv : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by fin_cases i <;> decide
  rcases hv with rfl|rfl|rfl|rfl <;>
    simp [broad,mom,a,b] <;> field_simp
  all_goals try (rw [hc])
  all_goals ring_nf at * 
  all_goals simp_all
  all_goals ring

private lemma charts_at {q : Sp} {t : ℂ} (h : c.mom=broad q t) :
    2*c.l=t-I*q 2 ∧ 2*c.l*c.a=q 1-I*q 0 ∧ 2*c.l*c.b= -q 1-I*q 0 := by
  have e₀ := congr_fun h 0; have e₁ := congr_fun h 1
  have e₂ := congr_fun h 2; have e₃ := congr_fun h 3
  simp [mom,broad] at e₀ e₁ e₂ e₃
  rw [← e₀, ← e₁, ← e₂, ← e₃]
  refine ⟨?_,?_,?_⟩ <;> ring_nf <;> simp <;> ring

theorem both (q : Sp) (h : RegularQ q) : Nonempty (Both q) := by
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_pow_nat_eq (-norm3 q) (n:=2) (by decide)
  have hv : t≠0 := by
    rintro rfl; rw [zero_pow (by decide)] at ht; exact h.2 (neg_eq_zero.mp ht.symm)
  obtain ⟨u,hu,u0⟩ := obtains q h t ht
  obtain ⟨v,hv',v0⟩ := obtains q h (-t) (by rw [neg_sq]; exact ht)
  obtain ⟨e,a,b⟩ := charts_at _ hu
  obtain ⟨f,r,s⟩ := charts_at _ hv'
  have he : u.l ≠ v.l := by
    intro g; rw [g,f] at e
    apply hv; linear_combination -e/2
  refine ⟨⟨t,hv,u,v,hu,hv',u0,v0,?_,?_⟩⟩
  · intro hg; rw [hg,← r] at a
    have hp : v.a=0 := by
      by_contra hx; exact he (mul_left_cancel₀ (by norm_num : (2:ℂ)≠0) (mul_right_cancel₀ hx a))
    rw [hp,mul_zero] at r
    apply h.1; rw [sub_eq_zero.mp r.symm,mul_pow,I_sq]; ring
  intro hg; rw [hg,← s] at b
  have hp : v.b=0 := by
    by_contra hx; exact he (mul_left_cancel₀ (by norm_num : (2:ℂ)≠0) (mul_right_cancel₀ hx b))
  rw [hp,mul_zero] at s
  have hp' := sub_eq_zero.mp s.symm
  apply h.1; rw [← neg_sq (q 1),hp',mul_pow,I_sq]; ring
end Chart
end Cauchy
end YM.GaugeFieldConstruction
