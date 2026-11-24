import ExactRunning.Dyne.Lateral

/-!
# The predicting (low tangent) field

At chevron, prediction's first derivative `castLow` amounts to
taking the mean of W; thus has symbol `result` by `actor`
(trial equations in symbol form). Fourier laws give the repetition
properties of predicted and lifted legs.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024

open Pairing

variable {G : Gauge} {E I : Pylon G} {m L : Side} {X : BlockTie E I}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace BlockTie
variable (X)

theorem actor {p : Momentum} (h : star p=p) :
    primalV X.Phi E.B I.B p ∧ secondV X.Phi I.B X.kernel.penalty p := by
  let η := E.σ/inch X.L
  have hu : 0<η := div_pos E.house (inch_pos _)
  let R : Armada walent (X.up ∘ walent) X.patch X.kernel := ⟨fun i=>rfl⟩
  have t : E.B.metric.strip (inch X.patch.L*η) E.C := by
    rw [mul_div_cancel₀ E.σ (inch_pos _).ne']
    exact E.strip
  exact actor_duo R I.house I.strip hu t X.hη X.bridge.1 walentes
    (W:=fun n=> X.W (walent n)) (fun _=> X.via _) (fun i => (X.diagonal _).trial) h

def result (p : Momentum) : CompM (Entry G) (Entry G) :=
  1-X.kernel.penalty⁻¹ • rug G I.B p
def resultM (m) := patron G (Precision.mean (X.step m)*X.W m)
lemma success {p} (hx : star p=p) :
    meanRay G X.patch p * X.Phi p = X.result p := (X.actor hx).2
lemma runup : Poster I.σ X.result :=
  (Poster.web _).shares ((rug_played (G:=G) I.B I.strip I.house).plus_nec (↑(X.kernel.penalty⁻¹):ℂ))

lemma predictM (x : Link G m) :
    X.castLow m x = X.resultM m *ᵥ x := by
  let S := X.step m
  have hp := Push.side (X.fore m) (X.fore_smooth.differentiableAt (by simp)) x
  rw [resultM,patron_mul, ← mulVec_mulVec, patron_fee,patron_fee]
  refine hp.unique ?_
  refine ray_content (by rw [zero_smul,X.lead_zero,X.Z_zero]) fun i=>?_
  have he : uniformM (Precision.mean S) (X.lift0 m x) =
      uniformM (Precision.mean S) (endorse (X.W m) x).1 - gradientA G m (endorse (X.W m) x).2 := by
    rw [show (endorse (X.W m) x).2=0 from rfl,map_zero,sub_zero]
    rfl

  rw [he]
  unfold lead chevron
  simp_rw [map_smul]
  exact centered_pred X.branches _ _ _

lemma predictQ (m) : Jaunt (approached (X.resultM m)) X.result 0 := by
  have h := (bond_travel (G:=G) (X.step m)).hoist (X.via m)
  intro a p hp v
  rw [← X.success (hp.metric (real_frequency _)),resultM,patron_mul,prom_mul]
  rw [show approached (patron G (Precision.mean (X.step m)))*approached (patron G (X.W m)) =
       _ from repack_multiply (Equiv.refl _) (unitSplit G (X.step m) 1) (Equiv.refl _) _ _]
  exact h a p hp v

lemma predicts (m) : Turns (fun p => Matrix.toLin' (X.result p)) (X.castLow m) where
  basis :=
    ⟨Matrix.toLin' (approached (X.resultM m)),fun v=>by rw [predictM,Matrix.toLin'_apply,prom_vec],
    fun i q h v=> by simpa only [add_zero,Matrix.toLin'_apply] using X.predictQ m i q h v⟩

lemma sends {D : Latitude} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {U : Matrix (Co m α) (Co m β) ℝ} {F : Momentum → CompM α β}
    {x : Corn (Co m β)} (h : Jaunt (approached U) F 0)
    (q : D.repeats x) : D.repeats (U *ᵥ x) := by
  have hi : D.spin m α * U = U * D.spin m β := approached_inj <| by rw [prom_mul,prom_mul,D.jaunt0_spin h]
  rw [D.repeats_iff,mulVec_mulVec,hi,← mulVec_mulVec,D.repeats_iff.mp q]

lemma send_low {r : ℝ} {x : Link G m} (h : (ridge r).repeats x) : 
    (ridge r).repeats (X.castLow m x) := by rw [predictM]; exact sends (X.predictQ m) h

lemma send_high {r : ℝ} {x : Link G m} (h : (ridge r).repeats x) :
    (X.back r).repeats (X.lift0 m x) := by
  let e := (X.rolled 1).pack m
  let i := Equiv.refl (Co m (Loc G 1))
  have hp : (ridge r).repeats (repackM e i (patron G (X.W m)) *ᵥ (x ∘ i.symm)) :=
    sends (X.via m) h
  rw [repack_act,patron_fee] at hp
  ext1 y
  have ht := congr_fun hp (e y)
  rw [Function.comp_apply,X.carries_rolled 1 y r |>.symm,Function.comp_apply,e.symm_apply_apply,Function.comp_apply,e.symm_apply_apply] at ht
  exact ht

end BlockTie
end ExactRunning
