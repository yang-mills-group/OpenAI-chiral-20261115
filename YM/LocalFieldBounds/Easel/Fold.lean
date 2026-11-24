import YM.SU5.SatinWard.Resolution.Peralta
import YM.SU5.SatinWard.Resolution.Moonglow
import YM.SU5.Reconstruction.Seams.Bills
import YM.SU5.Macro.Across

/-!
# Real smears

A curtain as a compactly supported real nonnegative spacetime smear of total mass
one. We'll use identical coordinates to read Eu (Wick recovered) and real-time
prices. Here we record support and normalization in making the test-function
calibration change, and movement of these labels.
-/

open Function Filter Set MeasureTheory
open scoped Classical Topology NNReal ContDiff

noncomputable section
namespace YM.LocalFieldBounds.Easel
open GarnetAct.Cut Boundary Probe
abbrev Paper := Fin 4 → ℝ -- Vantage coords

/-- Pass to E4, axis 3 kept for Eu / Mink time. -/
abbrev face : Paper → E4 := WithLp.toLp 2

variable (F : Curtain)

abbrev paperE : E4 ≃L[ℝ] Paper := PiLp.continuousLinearEquiv _ _ _
theorem face_eq : face = paperE.symm := rfl

private theorem screen {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [Zero C]
    (h : B ≃ₜ A) (f : A → C) :
    tsupport (f ∘ h) = h.symm '' tsupport f := by
  unfold tsupport
  rw [h.symm.image_closure]
  congr 1
  ext x
  simp [Homeomorph.image_symm, Function.comp, Function.mem_support]

private abbrev mask := Complex.ofReal ∘ (F.val ∘ paperE)
private lemma floor_plan : tsupport (mask F) = face '' F.boxS := by
  rw [mask, tsupport_comp_eq Complex.ofReal_eq_zero]
  exact screen paperE.toHomeomorph F.val

lemma cont_face : Continuous face :=
  paperE.symm.continuous

/-- Same unit weights as in the registered Wick prices. -/
def film : Test4 :=
  HasCompactSupport.toSchwartzMap (f := mask F)
    (by rw [HasCompactSupport, floor_plan]; exact F.budget.image cont_face)
    (Complex.ofRealCLM.contDiff.comp (F.classy.comp paperE.contDiff))

theorem aperture : tsupport (film F) = face '' F.boxS :=
  floor_plan F
theorem density (x : Paper) : film F (face x) = F.val x := rfl
theorem film_real : bar (film F) = film F := by
  ext x
  rw [bar_at, show film F x = ↑(F.val (paperE x)) from rfl, Complex.star_def, Complex.conj_ofReal]
theorem allocation (x : E4) : 0 ≤ ((film F x).re) := F.positive _

/-- Retain Lebesgue normalization, even without assuming measurability
in this test-weight identity. -/
theorem transpire {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (v : E4 → X) :
    (∫ x, film F x • v x) = ∫ x, v (face x) ∂ F.ppm := by
  letI : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ ℂ X
  have hm : MeasurableEmbedding face := paperE.toHomeomorph.symm.toMeasurableEquiv.measurableEmbedding
  rw [← (PiLp.volume_preserving_toLp (Fin 4)).integral_comp hm (fun x => film F x • v x), F.honest]
  exact integral_congr_ae (ae_of_all _ (fun x => Complex.coe_smul _ _))

theorem normalized : ∫ x, film F x = 1 := by
  simpa using (transpire F (fun _ => (1:ℂ)))

/-- Translation in Minkowski coordinates of a normalized label. -/
def sweep (o : Paper) : Curtain where
  val := fun x => F.val (x-o)
  classy := F.classy.comp (by fun_prop)
  budget := F.budget.comp_homeomorph (Homeomorph.subRight o)
  positive _ := F.positive _
  mass := by rw [integral_sub_right_eq_self, F.mass]

theorem lantern (o : Paper) :
    film (sweep F o) = ahead (face o) (film F) := by
  ext x
  rw [ahead_at]
  rfl

theorem sweep_foot (o : Paper) :
    (sweep F o).boxS = (fun x => x+o) '' F.boxS :=
  screen (Homeomorph.subRight o) F.val

theorem sweep_room {r : ℝ} (o : Paper)
    (h : F.boxS ⊆ Metric.closedBall (0 : Paper) r) :
    (sweep F o).boxS ⊆ Metric.closedBall o r := by
  rw [sweep_foot]
  rintro _ ⟨x, h', rfl⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using h h'

end YM.LocalFieldBounds.Easel
