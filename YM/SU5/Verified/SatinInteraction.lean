import YM.SU5.FiniteGaugeData.Signal.Sapphire

/-! Apply the two halves of Season.Abundance to the same late-scale reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Reliance.Season
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal Classical
attribute [local instance] opCStarAlgebra
open Concord Py Py.Rate LocalLimit Preparation FullBill
open Afterglow Afterglow.Sound Afterglow.Satin Afterglow.Journey
open YM.SU5.FiniteGaugeData.Audit1102 CF.Signal CF.Signal.Showcasing CF.Signal.Ovation

private theorem shelter_sublist {T S : Finset Cover} {I J : List Cover}
    (h : Shelter T S J) (u : I.Sublist J) : Shelter T S I :=
  ⟨h.1, fun x hx => h.2.1 x (u.subset hx), h.2.2.1.sublist u,
   fun x hx => h.2.2.2 x (u.subset hx)⟩

variable {Λ : Preparation} {l : ℕ} {Y : Course Λ (VolumeCape.Dream.Nimbus l)}
  {H : Real.exp 1 ≤ Λ.x} {g c : ℝ} {j : ℕ} {p : Reservation Λ g c j}
  {F : ℕ → Buffered.Family (tent Y H) → ℕ → ℂ} {E : ℕ → Buffered.Family (tent Y H) → ℂ}
  {P : Playhouse Λ l} {i k : ℕ → ℕ} {W : Traced Y H i k F E P}

/-- One uniform positive margin and one finite support budget provide a nonzero marked
reading and a failure of gauge–matter product factorization for every slot at late scales,
on the same elected signed functional E. The probes may depend on scale and slot. -/
theorem Abundance.mixed_at_late_scales (A : Abundance Y H p W) :
    ∃ (C a : ℝ) (T S : Finset Cover) (J : List Cover), 0 < C ∧ 0 < a ∧
    ∀ᶠ s : ℕ in atTop, ∀ l : SU.Slot, ∃ (I : List Cover) (x : junior (tent Y H)),
      I.Sublist J ∧ I ≠ [] ∧ Shelter T S I ∧ Effect (tent Y H) l S T I x ∧
      a < ‖E s x.val‖ ∧ (∀ m : Side, ∀ y, ‖x.val m y‖ ≤ C) ∧
      ∃ (f : LinksC → ℂ) (b : Buffered.Family (tent Y H)), Scherzo.Parfume.Soft T f ∧
        b ∈ Scherzo.Parfume.price (tent Y H) (Window.family l) S I ∧ E s b = 0 ∧
        E s (Scherzo.Parfume.stucco (tent Y H) f * b) ≠
          E s (Scherzo.Parfume.stucco (tent Y H) f) * E s b := by
  obtain ⟨C, a, T, S, J, h⟩ := A.mean
  refine ⟨C, a, T, S, J, h.gain.cost, h.gain.gain, ?_⟩
  filter_upwards [h.gain.earn] with s hs l
  obtain ⟨I, sub, ne, x, effect, pos, bounded⟩ := hs l
  have sheltered := shelter_sublist h.gain.house sub
  have nz : E s x.val ≠ 0 := norm_pos_iff.mp (h.gain.gain.trans pos)
  exact ⟨I, x, sub, ne, sheltered, effect, pos, bounded, A.cross s l sheltered ne effect nz⟩
end YM.CF.Buffered.Reliance.Season
