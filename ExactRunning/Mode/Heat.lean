import ExactRunning.Mode.Rack
/-! # Positivity in kinetic spectrum -/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024


variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {p : Momentum} {L : Side}

lemma real_roll {q : Momentum} (h : rolls p q) (hp : star p=p) : star q=q := by
  obtain ⟨z,rfl⟩ := h
  simp [hp]; ext; simp [reciprocal]

lemma shade_missing (h : ¬ 0 < shadeK p) (hp : star p=p) :
    rolls p 0 := by
  obtain ⟨v,hv,e⟩ := Nave.roll p
  rw [← shadeK_round e] at h
  have hi := e.symm
  have ht := real_roll hi hp
  rw [← axes_of_real ht] at h hi hv
  have hh : 1/4 * flay _ ≤ 0 := (orbit_lower _ hv).trans (not_lt.mp h)
  have he : ‖WithLp.toLp 2 (fun i => (v i).re)‖ ≤ 0 :=
    nonpos_of_mul_nonpos_right hh (by norm_num)
  have hk := norm_eq_zero.mp (le_antisymm he (norm_nonneg _))
  rw [show (fun i => (v i).re) = 0 from congr_arg WithLp.ofLp hk] at hi
  exact hi

lemma shade_none : shadeK 0 = 0 := by
  unfold shadeK
  rw [show q (ground 0)=0 by ext; simp [q, ground, axes],slug_zero]

lemma multi_roll {q : Momentum} (h : rolls p q) (k : ℕ) :
    rolls (k • p) (k • q) := by
  induction k with
  | zero => simp; exact rolls.refl _
  | succ k ih => rw [succ_nsmul,succ_nsmul]; exact ih.plus h

lemma alias_shade (hp : star p=p) (hs : 0 < shadeK p) (l : Site L) :
    0 < shadeK (aliasAt p l) := by
  by_contra hn
  have he := multi_roll (shade_missing hn (by rw [← alias_conj,hp])) L.val
  rw [smul_zero] at he
  have hx : (↑L.val : ℂ) ≠ 0 := by exact_mod_cast L.property.ne'
  have hh : rolls p (L.val • aliasAt p l) :=
    ⟨lift l, by rw [← Nat.cast_smul_eq_nsmul ℂ, aliasAt, smul_add, mon,
        smul_smul,smul_smul, mul_inv_cancel₀ hx,one_smul,one_smul]⟩
  rw [shadeK_round (hh.trans he),shade_none] at hs
  exact lt_irrefl _ hs

-- accretivity
def Glow (K : CompM α α) : Prop :=
  ∀ v, v≠0 → 0 < (dotProduct (star v) (K *ᵥ v)).re

namespace Glow
variable {K : CompM α α}

lemma nn (h : Glow K) (v : Phase α) : 0 ≤ (dotProduct (star v) (K *ᵥ v)).re :=
  if hv:v=0 then by simp [hv] else (h v hv).le
lemma eq_zero (h : Glow K) (v : Phase α) (he : (dotProduct (star v) (K *ᵥ v)).re =0) :
    v=0 := by by_contra hv; exact (h _ hv).ne' he

lemma unit (h : Glow K) : IsUnit K.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  exact fun x y e => sub_eq_zero.mp (h.eq_zero _ (by simp [Matrix.mulVec_sub,e]))

lemma weighted_one (α : Type) [Fintype α] [DecidableEq α] {c : ℝ} (h : 0<c) :
    Glow ((c:ℂ) • (1:CompM α α)) := by
  intro v hv
  rw [smul_mulVec,one_mulVec,dotProduct_smul,slug_self]
  simpa [smul_eq_mul,pow_two] using mul_pos h (pow_pos (slug_pos hv) 2)

lemma one (α : Type) [Fintype α] [DecidableEq α] :
    Glow (1:CompM α α) := by
  simpa using weighted_one α zero_lt_one

lemma congr {U : CompM α α} (h : Glow K)
    (he : Injective (U.mulVec)) : Glow (Uᴴ * K * U) := by
  intro v hv
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,vested]
  exact h _ (fun g => hv (he (g.trans (mulVec_zero _).symm)))

/-- kinetic block -/
lemma principal {S : CompM (α⊕β) (α⊕β)} (h : Glow S) : Glow S.toBlocks₁₁ := by
  intro x hx
  have ht := h (Sum.elim x 0) (fun g=>hx (funext fun i => congr_fun g (.inl i)))
  rw [← Matrix.fromBlocks_toBlocks S] at ht

  rw [Matrix.fromBlocks_mulVec, show star (Sum.elim x 0 : α⊕β→ℂ) = Sum.elim (star x) 0 by
    ext (i|i) <;> simp,halvesP] at ht
  simpa [Sum.elim_comp_inl,Sum.elim_comp_inr] using ht

lemma comp {A : CompM β β} (h : Glow K) (g : Glow A) :
    Glow (fromBlocks K 0 0 A) := by
  intro x hx
  let y := x ∘ Sum.inl;let z := x ∘ Sum.inr
  have he : x = Sum.elim y z := by funext i; cases i <;> rfl
  rw [he,show star (Sum.elim y z) = Sum.elim (star y) (star z) by ext (i|i) <;> simp,
      Matrix.fromBlocks_mulVec, halvesP,Complex.add_re,zero_mulVec,zero_mulVec,
      zero_add,add_zero,Sum.elim_comp_inl,Sum.elim_comp_inr]
  by_cases hy:y=0
  · refine add_pos_of_nonneg_of_pos (h.nn _) (g _ (fun e => hx ?_))
    rw [he,hy,e];ext (i|i) <;> rfl
  exact add_pos_of_pos_of_nonneg (h y hy) (g.nn _)

lemma fold {F : Momentum → CompM α α}
    (hp : star p=p) (h : ∀ i : Site L, Glow (F (aliasAt p i))) :
    Glow (furnish L F p) := by
  intro x hx
  rw [sleeve _ hp, Complex.re_sum]
  apply Finset.sum_pos'

  · exact fun i _=> (h i).nn _
  suffices ∃ i,stackSlice i (crewAlias p x)≠0 from Exists.elim this (fun i e=>⟨i,mem_univ i,h i _ e⟩)
  by_contra! he
  have ht : crewAlias p x=0 := funext fun i => congr_fun (he i.1) i.2
  exact hx (by rw [← tile_crew (p:=p) x,ht,mulVec_zero])

variable {G : Gauge} {E : Pylon G}
lemma curtain (E : Pylon G) (hp : star p=p) (h : 0<shadeK p) :
    Glow (curtainG G E.B p) := by
  intro x hx
  let M := pageD G 0 p
  rw [curtainG,page_rear 0 hp,Matrix.add_mulVec,dotProduct_add,Complex.add_re,
    show (pageD G 0 p)*(pageD G 0 p)ᴴ = (Mᴴ)ᴴ*Mᴴ by simp [M],
    ← Matrix.mulVec_mulVec,vested,slug_self]
  have a : 0<(shadeK p * slug x)^2 := pow_pos (mul_pos h (slug_pos hx)) _
  rw [← pure_grade hp G x] at a
  have b := rug_test E.strip E.house E.floor hp x
  by_cases g : 0<slug (pageD G 1 p *ᵥ x)^2
  · exact add_pos_of_pos_of_nonneg ((mul_pos E.strict g).trans_le b)
      (by exact sq_nonneg _)
  have k := (le_antisymm (not_lt.mp g) (sq_nonneg _))
  rw [k,add_zero] at a
  rw [k,mul_zero] at b
  exact add_pos_of_nonneg_of_pos b a

lemma grenade {ι : Type} [Fintype ι] [DecidableEq ι] {P : Patch} (D : Eye ι (Acts G P))
    (hp : star p=p) : Glow ((grenadeFilm D).tab p) := by
  rw [grenade_ground D (Work.F07.realStrip _ (by norm_num) hp)]
  apply fold hp
  refine fun i v hv => lt_of_lt_of_le ?_ (throne_floor _ (by rw [← alias_conj,hp]) (inch_pos _))
  exact mul_pos (mul_pos (by norm_num) (peb_pos _ (inch_pos _))) (pow_pos (slug_pos hv) _)

lemma ghost (G : Gauge) (hp : star p=p) (he : 0<shadeK p) : Glow ((quarry G).tab p) := by
  rw [quarry_tab _ hp, stone_real hp]
  exact weighted_one _ (pow_pos he _)

end Glow

end ExactRunning
