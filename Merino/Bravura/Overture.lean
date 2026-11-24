import Merino.Bravura.Sonnet
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Bravura
open scoped Topology Classical InnerProductSpace
open Finset Filter
universe u v w
variable {A:Type u}[Fintype A] {ι:Type v}[Fintype ι]
 {V:Type w}[NormedAddCommGroup V][NormedSpace ℂ V] -- NormedSpace ℝ?
variable (B:ι→A→ℝ→V)

universe e
variable {H:Type e}[NormedAddCommGroup H][InnerProductSpace ℂ H]
variable (y z:H)
/-- It suffices to control the amount of the Y signal **in the direction** of Z.
Label r goes to zero. Cosine amount (one-sided) and transmission
(between the measuring probes for the discrepancy fixed, and movement), also
required only tested one-sided against Z. All measuring, no assumption of rank one. -/
def Skew:Prop:= (⟪y,z⟫_ℂ).re≤‖z‖^2/4
def Resonance (C α r:ℝ) (W:V):Prop:=
   (⟪z-y,z⟫_ℂ).re ≤ ‖z‖*α*(1/4+C*‖W‖/r^65)

variable {y z}
omit [NormedSpace ℂ V] in
lemma carries {C α r:ℝ} (a:0<α)(z0:α≤‖z‖)(p:0<r)
   {W:V} (h:Skew y z)(k:Resonance y z C α r W):
   Loud C r W:=by
 unfold Skew at h
 unfold Resonance at k
 rw [inner_sub_left,Complex.sub_re,inner_self_eq_norm_sq_to_K] at k
 have v:‖z‖*α*(3/4)≤‖z‖*α*(1/4+C*‖W‖/r^65):=by
   apply le_trans _ k
   change _ ≤ ((‖z‖:ℂ)^2).re - _
   rw [←Complex.ofReal_pow,Complex.ofReal_re]
   nlinarith [mul_le_mul_of_nonneg_left z0 (norm_nonneg z)]
 have e:=le_of_mul_le_mul_left v (mul_pos (a.trans_le z0) a)
 unfold Loud
 have t:= (le_div_iff₀ (pow_pos p 65)).mp (show 1/2≤ C*‖W‖/r^65 by linarith)
 linarith

variable (p:ℕ→ℝ) (δ C R D:ℝ) (l:ℕ→ι→ℂ)
def Canta :Prop :=
    (∀ᶠ s:ℕ in atTop, emitted C δ (p s) (harmony B (l s))) ∧
    (∃j,cantata B j ≠ 0)

/-- Kinematics for the criteria: use one reference width p_s ↘ 0 (monotonicity not
required), the compared discretization using per-axis shifts δ p^16,
and uniform constants. -/
structure Cadence :Prop where
 pink : ∀s,0<p s
 beats : Tendsto p atTop (𝓝 0)
 ideal : 0<δ
 pian : 0<C
 mid : 0<R
 pen : 0≤D
 composes : Timbre B R D

variable {p δ C R D B}
omit [Fintype ι] in
lemma smallR (h:Cadence B p δ C R D) :
 ∀ᶠ s in atTop,|gap δ (p s)| ≤ R ∧ Piano A C D δ (p s) ∧ p s≤1 :=by
 have a:Tendsto (fun s=>|gap δ (p s)|) atTop (𝓝 0):=by
    simpa [gap] using (Filter.Tendsto.abs ((h.beats.pow 16).const_mul δ))
 have b:=h.beats.const_mul (4*C*costS A C D δ)
 rw [mul_zero] at b
 filter_upwards [a.eventually (ge_mem_nhds h.mid),b.eventually (ge_mem_nhds zero_lt_one),
     h.beats.eventually (ge_mem_nhds zero_lt_one)] with s i j k
 exact ⟨i,j,k⟩

variable {l}
lemma letSing (h:Cadence B p δ C R D)
  (g:∀ᶠ s:ℕ in atTop, emitted C δ (p s) (harmony B (l s))):
    Canta B p δ C l:=by
 refine ⟨g,?_⟩
 by_contra! k
 obtain ⟨s,i⟩:=g.exists
 unfold emitted harmony at i
 simp [k] at i
 exact not_le_of_gt (pow_pos (h.pink s) 49) i
end YM.CF.Merino.Bravura
