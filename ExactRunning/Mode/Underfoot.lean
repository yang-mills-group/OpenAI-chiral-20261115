import ExactRunning.Mode.Heat
/-!
# Symbols from native to rolled

Positivity via `Glow.fold`: fold all fine aliases over any coarse momentum
nonzero mod periods (no alias zero), also for the kinetic operator
identified (`fas_symb`) via `Jaunt.press` and all periods.
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
namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}

open Pairing

variable (X) {p : Momentum}

lemma forest (w : ℝ) (hw : 0<w) (hi : w ≤ E.σ) :
    Poster w (curtainG G E.B) :=
  (rug_played _ (A:=E.C) (fun i j => (E.strip i j).mono hi le_rfl) hw).amounts
    ((page_linen 0).forge ((page_linen 0).reverse))

lemma march (E : Pylon G) (m : Side) :
    Jaunt (approached (epMat E.p E.r (1 : Config G m))) (curtainG G E.B) 0 := by
  rw [epMat, prom_addition, flare_matches E.paths (E.floor _) E.attached (E.sworn _),
      mailed_zero, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, prom_mul]
  exact (rug_plane _ E.B (E.B.metric.rights _ _ E.strip E.house.le)).plus
      ((page_read _ 0).hoist (page_read _ 0 |>.takes))


lemma rolled_act {k : ℕ} {u : Filling (Du G) (X.rolled k) (X.rolled k)}
    {F : Momentum → CompM (Loc G k) (Loc G k)}
    (U : Tray G (X.rolled k) (X.rolled k) u)
    (h : ∃ w : ℝ, 0<w ∧ Poster (X.μ*w) F)
    (hf : ∀m, Jaunt (approached (u m 0)) F 0)
    (hp : star p=p) :
    U.symb p = furnish X.L F p := by
  obtain ⟨w,a,b⟩ := h
  exact U.align (Tub.stock _ _ _ (fun m=> u m 0) (furnish X.L F) ⟨_,a,b.furnish_ok⟩
    (fun m=> Jaunt.press (X.S m).ratio (hf m) b a))
    (fun _ => rfl) hp

lemma fas_symb (hp : star p=p) :
    X.fas.symb p = furnish X.L (curtainG G E.B) p := by
  apply X.rolled_act X.fas _ _ hp
  · refine ⟨E.σ,E.house,forest _ (mul_pos X.hμ E.house)
      (mul_le_of_le_one_left E.house.le (inch_le X.L))⟩
  · simp only [X.fg_bg_zero]
    exact fun _=> march E _

lemma fas_glow (hp : star p=p) (hs : 0<shadeK p) :
    Glow (X.fas.symb p) := by
  rw [X.fas_symb hp]
  exact Glow.fold hp (fun _=> Glow.curtain E
    (by rw [← alias_conj,hp]) (alias_shade hp hs _))

lemma innerGhost_glow (hp : star p=p) (hs : 0<shadeK p) :
    Glow (X.innerGhost.symb p) := by
  have h x := (quarry_g (G:=G) (m:=X.up x)).tab
  simp only [cardM,input_zero] at h
  rw [X.rolled_act (F:=(quarry G).tab) X.innerGhost ⟨1,zero_lt_one,quarry_p.tab⟩
    (by simp_rw [X.fg_bg_zero]; exact h) hp]
  exact Glow.fold hp (fun _=> Glow.ghost G
    (by rw [← alias_conj,hp]) (alias_shade hp hs _))

lemma outerGhost_glow (G : Gauge) (hp : star p=p) (hs : 0<shadeK p) :
    Glow ((outerGhost G).symb p) := Glow.ghost G hp hs

lemma blow_glow (hp : star p=p) : Glow (X.blow.symb p) :=
  Glow.grenade X.eye hp

end BlockTie
end ExactRunning
