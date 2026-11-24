import ExactRunning.Finite.Carries

/-!
One-cycle-periodic fields, complexification of the coordinate jets on
that subspace, and preservation of the cut through first order.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

variable {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {m : Side}

namespace Latitude
variable (D : Latitude)

/-- External waves and gauge parameters are fixed by translation by
one cycle along axis 3. Also used for polarizing jets. -/
def repeats (v : Co m α → ι) := v ∘ D.shift m α = v

lemma repeats_iff {v : Corn (Co m α)} :
    D.repeats v ↔ D.spin m α *ᵥ v = v := by rw [spin,scroll_mulVec,repeats]

lemma repeats_iffC {v : Phase (Co m α)} :
    D.repeats v ↔ approached (D.spin m α) *ᵥ v = v := by rw [spin, approached_scroll_mulVec,repeats]

variable {D}
namespace repeats
lemma comp {β : Type} {v : Co m α → ι} (h : D.repeats v) (f : ι → β) :
    D.repeats (f ∘ v) := congr_arg (fun x => f ∘ x) h

variable {u v : Co m α → ι}
lemma smul {𝕜 : Type} [SMul 𝕜 ι] (h : D.repeats v) (z : 𝕜) :
    D.repeats (z • v) := h.comp (z • ·)
lemma neg [Neg ι] (h : D.repeats v) : D.repeats (-v) := h.comp Neg.neg
lemma add [Add ι] (h : D.repeats u) (k : D.repeats v) :
    D.repeats (u+v) := congr_arg₂ (·+·) h k
lemma sub [Sub ι] (h : D.repeats u) (k : D.repeats v) :
    D.repeats (u-v) := congr_arg₂ (·-·) h k

lemma wave {p : Site m} (hp : D.quiet (mon p)) (v : Phase α) : D.repeats (tune p v) := by
  rw [D.repeats_iffC, spin_tune,(D.quiet_iff_wind (real_frequency _)).mp hp,one_smul]

lemma wave' {p : Site m} {q} (hq : rolls (mon p) q) (hp : D.quiet q) (v : Phase α) :
    D.repeats (tune p v) := wave (hp.rolls hq.symm) v
end repeats

end Latitude

def seatL [Fintype ι] [DecidableEq ι] (U : Corn ι → Matrix α β ℝ) :
    Phase ι →ₗ[ℂ] Matrix α β ℂ where
  toFun := seat U
  map_add' := by
    intro u v; ext a b; simp only [seat,art, Matrix.of_apply,Matrix.add_apply]
    have hj (x : Phase ι) : (![x] : Fin 1 → Phase ι) = update (0:Fin 1 → Phase ι) 0 x := by ext i; fin_cases i; simp
    rw [hj,hj u,hj v,MultilinearMap.map_update_add]
  map_smul' := by
    intro z u; ext a b; simp only [seat,art, Matrix.of_apply,Matrix.smul_apply]
    have hj (x : Phase ι) : (![x] : Fin 1 → Phase ι) = update (0:Fin 1 → Phase ι) 0 x := by ext i; fin_cases i; simp
    rw [hj,hj u,MultilinearMap.map_update_smul]; rfl

lemma via_relay (v : Phase (Co m α)) :
    ∃ w : Phase (Co m α), v = ∑ i : Co m α, w i • relay i.1 i.2 := by
  refine ⟨(rotations m α)⁻¹ *ᵥ v,?_⟩
  have h : rotations m α *ᵥ ((rotations m α)⁻¹ *ᵥ v) = v := by
    rw [mulVec_mulVec,Matrix.mul_nonsing_inv _ (rotations_unit m α),one_mulVec]
  conv_lhs => rw [← h]

  ext ⟨x,i⟩; rw [Matrix.mulVec,dotProduct, Finset.sum_apply]
  apply sum_congr rfl; rintro ⟨p,j⟩ _
  simp [coef_wave,mul_comm]

@[simp] lemma seatL_app [Fintype ι] [DecidableEq ι] (U : Corn ι → Matrix α β ℝ) (v : Phase ι) :
    seatL U v = seat U v := rfl

namespace Latitude
variable (D : Latitude)
variable [Fintype ι] [DecidableEq ι] {K : Film ι α β}
    {U : OperatorF ι m α β}

lemma seat_spin (h : Ticket K U) (v : Phase (Co m ι)) :
    approached (D.spin m α) * seat U v =
      seat U (approached (D.spin m ι) *ᵥ v) * approached (D.spin m β) := by
  change _ * seatL U v = seatL U _ * approached _
  obtain ⟨w,hv⟩ := via_relay v
  rw [hv, mulVec_sum, map_sum,map_sum, Matrix.mul_sum,Matrix.sum_mul]
  apply sum_congr rfl; rintro ⟨p,j⟩ _
  change _ * seatL U (_ • relay p j) = seatL U (_ *ᵥ _ • relay p j) * _
  rw [mulVec_smul, show approached (D.spin m ι) *ᵥ relay p j = _ from D.spin_tune p (Pi.single j 1),
     map_smul,map_smul,map_smul, Matrix.mul_smul,Matrix.smul_mul, Matrix.smul_mul]

  exact congr_arg (w (p,j) • ·) (D.jaunt_spin (h.spot j p _ (rolls.refl _)))

lemma card_spin (h : Ticket K U) :
    D.spin m α * U 0 = U 0 * D.spin m β := by
  apply approached_inj
  rw [prom_mul,prom_mul]
  exact D.jaunt0_spin h.tab

lemma dir_spin (h : Ticket K U) {v : Corn (Co m ι)} (i : D.repeats v) :
    D.spin m α * directionM U 0 v = directionM U 0 v * D.spin m β := by
  have hi := i.comp Complex.ofReal
  have hh := D.seat_spin h (axes v)
  rw [(D.repeats_iffC (v:=axes v)).mp hi,seating] at hh
  apply approached_inj
  rw [prom_mul,prom_mul]
  exact hh

/-- Fit for a ticket sampled along any curve whose first derivative
repeats. No restriction on higher jets. -/
lemma ticket_fit (h : Ticket K U)
    {v : ℝ → Corn (Co m ι)}
    (hv : v 0 = 0) (hd : DifferentiableAt ℝ v 0)
    (i : D.repeats (deriv v 0)) :
    Fit (D.cut m α) (D.cut m β) (fun t => U (v t)) := by
  have he (a b) :
      HasDerivAt (fun t => U (v t) a b) (directionM U 0 (deriv v 0) a b) 0 := by
    have hi := ((show DifferentiableAt ℝ (fun z => U z a b) (v 0) from
      hv.symm ▸ (h.finance a b).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hd.hasDerivAt)
    rwa [hv] at hi
  refine Fit.of_deriv (fun a b => (he a b).differentiableAt) (cut_of_spin rfl ?_) (cut_of_spin rfl ?_)
  · rw [hv]; exact D.card_spin h
  rw [show Fit.diff (fun t => U (v t)) = directionM U 0 (deriv v 0)
      from Matrix.ext fun a b => (he a b).deriv]
  exact D.dir_spin h i

lemma ticket_fit_line (h : Ticket K U) {v : Corn (Co m ι)} (i : D.repeats v) :
    Fit (D.cut m α) (D.cut m β) (fun t => U (t • v)) := by
  apply D.ticket_fit h (v:=fun t => t • v) (zero_smul ..) (by fun_prop)
  rwa [((hasDerivAt_id' (0:ℝ)).smul_const v).deriv,one_smul]
end Latitude
end ExactRunning
