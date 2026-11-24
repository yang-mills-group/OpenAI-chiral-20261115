import ExactRunning.Dyne.Pitch

/-!
# Projecting to the magnetic test

`Melody`: convergence only of the one intensive Hessian coefficient,
along the magnetic momentum axis. Real quadratic Taylor coefficient
in momentum (`rQuad`) in this case is our target probe.
Any identification by `Touch` in external amplitude (agreement through
order two) passes to exact equality of Melodies as functions of momentum
via thermodynamic limits on the periods in `Pitch` and continuity.
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

variable {lo : ℕ} {i : G.ColorIndex}
variable {f u v : Law (Entry G)} {P Q : ℝ → ℂ}

structure Melody (lo : ℕ) (i : G.ColorIndex) (u : Law (Entry G)) (g : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ 2 g
  lit (m : Side) (h : lo≤m.val) : ContDiffAt ℝ ω (u m) 0
  plays {t : ℝ} (w : Pitch (tilt 0 t) lo) :
    Tendsto (fun n => echo (u (w.side n)) (w.face n) (stripe i) (stripe i)) atTop (𝓝 (g t))

section echo

lemma echo_add {f g : Corn (Co m ι) → ℝ} (h : ContDiffAt ℝ ω f 0)
    (k : ContDiffAt ℝ ω g 0) (a b c) :
    echo (f+g) a b c = echo f a b c+echo g a b c := by
  unfold echo
  rw [beat_as_cost,note_add h.analyticAt k.analyticAt]
  simp only [mul_add,smul_add,_root_.add_apply, ← beat_as_cost]

lemma echo_smul {f : Corn (Co m ι) → ℝ} (h : ContDiffAt ℝ ω f 0) (d : ℝ) (a b c) :
    echo (d • f) a b c = d • echo f a b c := by
  unfold echo
  rw [beat_as_cost,note_bill d h.analyticAt _, smul_comm, ← beat_as_cost,_root_.smul_apply]
  simp [mul_left_comm]

lemma echo_const (d : ℝ) (a : Site m) (b c : ι) :
    echo (fun _=>d) a b c=0 := by
  unfold echo beat enlarge
  simp [recording_apply,iteratedFDeriv_const_of_ne (by decide : 2≠0)]
end echo

namespace Melody

lemma add (h : Melody lo i u P) (k : Melody lo i v Q) : Melody lo i (u+v) (P+Q) where
  smooth := h.smooth.add k.smooth
  lit m a := (h.lit m a).add (k.lit m a)
  plays w := ((h.plays w).add (k.plays w)).congr fun n =>
    (echo_add (h.lit _ (w.large n)) (k.lit _ (w.large n)) _ _ _).symm

lemma smul (h : Melody lo i u P) (c : ℝ) : Melody lo i (c•u) (c•P) where
  smooth := h.smooth.const_smul c
  lit m a := (h.lit m a).const_smul c
  plays w := ((h.plays w).const_smul c).congr fun n =>
    (echo_smul (h.lit _ (w.large n)) c _ _ _).symm

lemma const (D : Side → ℝ) : Melody lo i (fun m _=>D m) 0 where
  smooth := contDiff_const
  lit _ _ := contDiffAt_const
  plays _ := (tendsto_const_nhds (x:=(0:ℂ))).congr fun _ => (echo_const ..).symm

theorem eq_of_touch (D : Latitude) (h : Melody lo i u P) (k : Melody lo i v Q)
    (he : ∀ m, lo ≤ m.val → ∀ x, D.repeats x →
      Touch (fun t => u m (t•x)) (fun t => v m (t•x))) :
    P=Q := by
  refine Radian.equalizer h.smooth.continuous k.smooth.continuous fun t ht => ?_
  obtain ⟨w⟩ := (Ode.magnetic D).pitch ht lo
  refine tendsto_nhds_unique ((h.plays w).congr ?_) (k.plays w)
  intro n
  dsimp only [echo]
  congr 1
  have hy : D.quiet (tilt 0 t) := (Ode.magnetic D).quiet t
  exact D.beat_of_touch (h.lit _ (w.large n)) (k.lit _ (w.large n)) (he _ (w.large n))
    (Latitude.repeats.wave (hy.neg.rolls (w.hits n).flip_sign.symm) _)
    (Latitude.repeats.wave (hy.rolls (w.hits n).symm) _)

end Melody

lemma Playing.bare {D : Latitude} {K} (h : Playing D u K) (i) :
    Melody lo i u (magcurve K i) where
  smooth := h.score (Ode.magnetic D) _ _
  lit m _ := (h.res m).reg
  plays w := by
    have a := h.waves ((Ode.magnetic D).quiet _) w
      (Pi.single (stripe i) 1) (Pi.single (stripe i) 1)
    rw [single_dotProduct,mulVec_single] at a
    simpa [echo, relay, magcurve] using a

def wind (A : Eye (Entry G) ι) (K : Kin ι) (i : G.ColorIndex) : ℝ → ℂ :=
  fun t => A (-tilt 0 t) (Pi.single (stripe i) 1) ⬝ᵥ
    K (tilt 0 t) *ᵥ A (tilt 0 t) (Pi.single (stripe i) 1)

lemma Playing.windy {D : Latitude} {K : Kin ι} {U : Law ι} (h : Playing D U K)
    {A : Eye (Entry G) ι} {L : (m : Side) → Link G m →L[ℝ] Corn (Co m ι)}
    (ha : ∀m, lo ≤ m.val → Turns A (L m)) (i : G.ColorIndex)
    (hs : ContDiff ℝ 2 (fun t=> A (tilt 0 t) (Pi.single (stripe i) 1))) :
    Melody lo i (fun m => U m ∘ L m) (wind A K i) where
  smooth := Score.val h.score (Ode.magnetic D) (by
    simpa only [Function.comp_def,id,tilt_neg] using! hs.comp contDiff_id.neg) hs
  lit m _ := ContDiffAt.comp _ (by rw [map_zero];exact (h.res _).reg) (L m).contDiff.contDiffAt
  plays {t} w := by
    let e : Phase (Entry G) := Pi.single (stripe i) (1:ℂ)
    refine (h.waves ((Ode.magnetic D).quiet _) w (A (-tilt 0 t) e) (A (tilt 0 t) e)).congr ?_
    intro n
    obtain ⟨T,b,c⟩ := (ha _ (w.large n)).basis
    dsimp only [echo]
    rw [beat_comp (L _) T b (h.res _).reg,
        show T ∘ ![relay (-w.face n) (stripe i), relay (w.face n) (stripe i)] =
          ![tune (-w.face n) (A (-tilt 0 t) e),tune (w.face n) (A (tilt 0 t) e)] from
          funext fun j => by
            fin_cases j
            · exact c _ _ (w.hits n).flip_sign e
            exact c _ _ (w.hits n) e]

def rQuad (P : ℝ→ℂ) := quad (Complex.re ∘ P)

lemma rQuad_val (a : ContDiff ℝ 2 P) : rQuad P = (quad P).re :=
  quad_re a.contDiffAt

lemma rQuad.add (a : ContDiff ℝ 2 P) (b : ContDiff ℝ 2 Q) :
    rQuad (P+Q)=rQuad P+rQuad Q := by
  rw [rQuad_val (P:=P+Q) (a.add b),rQuad_val a,rQuad_val b,quad_add a.contDiffAt b.contDiffAt]
  rfl
lemma rQuad.weight (a : ContDiff ℝ 2 P) (r : ℝ) :
    rQuad (r • P)=r*rQuad P := by
  rw [rQuad_val (P:=r•P) (a.const_smul r),rQuad_val a,quad_weight a.contDiffAt];simp

lemma rQuad.touch (a : ContDiff ℝ 2 P) (b : ContDiff ℝ 2 Q)
    (h : Touch P Q) : rQuad P = rQuad Q := by
  rw [rQuad_val a,rQuad_val b,h.quad_eq a.contDiffAt b.contDiffAt]

@[simp] lemma rQuad.mag (K : Kin (Entry G)) (i) : rQuad (magcurve K i) = alphaK K i := rfl

end ExactRunning
