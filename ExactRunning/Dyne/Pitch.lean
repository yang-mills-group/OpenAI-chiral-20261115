import ExactRunning.Mode.Finish

/-!
# Curves realizable on quiet external meshes

Identify thermodynamic response functions by probing on a dense
set of momenta p. For each of these, obtain periods/frequencies
realizing p exactly (mod periods in momentum), and hold p fixed
as volume grows. One can then extend along curves (`Ode`) and fit
Taylor coefficients in p without working with simultaneous limits
in external momentum, internal cutoff and volume.

`Playing` packages thermodynamic convergence of Hessian matrices and
regularity (`Score`) together with the finite-volume resonance laws.
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

structure Pitch (p : Momentum) (lo : ℕ) where
  side : ℕ → Side
  face : ∀ n, Site (side n)
  large n : lo ≤ (side n).val
  grows : Tendsto (fun n => (side n).val) atTop atTop
  hits n : rolls (mon (face n)) p

structure Ode (D : Latitude) (g : ℝ → Momentum) : Prop where
  smooth : ContDiff ℝ ω g
  real t : star (g t)=g t
  quiet t : D.quiet (g t)
  pitch {t} (h : Radian t) (lo : ℕ) : Nonempty (Pitch (g t) lo)

variable {p : Momentum} {lo : ℕ}

def Pitch.negative (u : Pitch p lo) : Pitch (-p) lo where
  side := u.side
  face n := -u.face n
  large := u.large
  grows := u.grows
  hits n := (u.hits n).flip_sign

def Pitch.split (u : Pitch p lo) (X : BlockTie E I) (l : Site X.L) : Pitch (aliasAt p l) lo where
  side n := X.up (u.side n)
  face n := duesM (X.step (u.side n)) (u.face n) p l
  large n := (u.large n).trans <| Nat.le_mul_of_pos_right _ X.L.property
  grows := tendsto_atTop.2 fun b =>
    ((tendsto_atTop.1 u.grows b).mono fun _ hn => hn.trans <| Nat.le_mul_of_pos_right _ X.L.property)
  hits n := duesM_real (X.step _) _ l (u.hits n)

namespace Ode
variable {D : Latitude} {g : ℝ → Momentum}

lemma neg (h : Ode D g) : Ode D (-g) where
  smooth := h.smooth.neg
  real t := by simp only [Pi.neg_apply,star_neg,h.real]
  quiet t := (h.quiet t).neg
  pitch u lo := (h.pitch u lo).map Pitch.negative

lemma axis (D : Latitude) {a : Axis} (ha : a≠3) : Ode D (tilt a) where
  smooth := tilt_smooth a
  real := tilt_real a
  quiet := tilt_quiet D ha
  pitch h lo := by
    obtain ⟨m,hg,hl,F,hF⟩ := h.packet_tilt a lo
    exact ⟨⟨m,F,hl,hg,hF⟩⟩

lemma magnetic (D : Latitude) : Ode D (tilt 0) := axis _ (by decide)
lemma sideways (D : Latitude) : Ode D (tilt 1) := axis _ (by decide)

lemma aliases (X : BlockTie E I) {r : ℝ} (h : Ode (ridge r) g) (l : Site X.L) :
    Ode (X.back r) (fun t => aliasAt (g t) l) where
  smooth := ContDiff.add (h.smooth.const_smul _) contDiff_const
  real t := by rw [← alias_conj,h.real]
  quiet t := (Latitude.quiet_alias (d:=0) (p:=g t) (l:=l)).mpr (h.quiet t)
  pitch u lo := (h.pitch u lo).map (fun p => p.split X l)

end Ode

abbrev Law (ι : Type) := (m : Side) → Corn (Co m ι) → ℝ

def Score (D : Latitude) (K : Kin ι) : Prop :=
  ∀ {g}, Ode D g → ∀ i j, ContDiff ℝ 2 (fun t => K (g t) i j)

structure Playing (D : Latitude) (u : Law ι) (K : Kin ι) where
  score : Score D K
  mesh : Side → Kin ι
  res m : Resonance D (mesh m) (u m)
  played {p : Momentum} (hp : star p=p) (hq : D.quiet p) {f : ℕ → Side}
    (grows : Tendsto (fun n => (f n).val) atTop atTop) :
    Tendsto (fun n => mesh (f n) p) atTop (𝓝 (K p))

variable {D : Latitude} {g : ℝ → Momentum} {K : Kin ι} {u : Law ι}

def Playing.through {u : Law ι} {J : Scene ι} (h : D.Medium J)
    (v : ∀ m, Resonance D (D.play m J) (u m)) : Playing D u (D.run J) where
  score := fun i a b => (h.smooth i.smooth i.real i.quiet a b).of_le (WithTop.coe_le_coe.mpr le_top)
  mesh m := D.play m J
  res := v
  played := h.plays

def Playing.native (h : Score D K) (v : ∀ m, Resonance D K (u m)) :
    Playing D u K where
  score := h
  mesh _ := K
  res := v
  played _ _ _ _ := tendsto_const_nhds

namespace Play

lemma smmul {κ : Type} [Fintype κ] {M : ℝ → CompM ι κ} 
    (h : ∀ i j, ContDiff ℝ 2 (fun t => M t i j)) {u : ℝ → Phase κ}
    (i : ContDiff ℝ 2 u) :
    ContDiff ℝ 2 (fun t => M t *ᵥ u t) :=
  contDiff_pi.mpr fun _ =>
    ContDiff.sum (fun _ _ => (h _ _).mul (contDiff_pi.mp i _))

lemma smdot {x y : ℝ → Phase ι} (h : ContDiff ℝ 2 x) (i : ContDiff ℝ 2 y) :
    ContDiff ℝ 2 (fun t => x t ⬝ᵥ y t) :=
  ContDiff.sum (fun j _ => (contDiff_pi.mp h j).mul (contDiff_pi.mp i j))

end Play

lemma Score.val (s : Score D K) (h : Ode D g) {x y}
    (a : ContDiff ℝ 2 x) (b : ContDiff ℝ 2 y) :
    ContDiff ℝ 2 (fun t => x t ⬝ᵥ K (g t) *ᵥ y t) :=
  Play.smdot a (Play.smmul (s h) b)

lemma Playing.waves (s : Playing D u K) (d : D.quiet p) (w : Pitch p lo) (x y) :
    Tendsto (fun n => (cents (w.side n) : ℂ)⁻¹ * beat (u (w.side n)) 0 2
      ![tune (-w.face n) x,tune (w.face n) y]) atTop
      (𝓝 (x ⬝ᵥ K p *ᵥ y)) := by
  have h : Continuous (fun M : CompM ι ι => x ⬝ᵥ M *ᵥ y) :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  exact ((h.tendsto _).comp (s.played ((w.hits 0).metric (real_frequency _)) d w.grows)).congr
    (fun n => ((s.res _).pair (w.hits n) d x y).symm)

lemma score_aux {f : Momentum → ℂ}
    (h : ∀ p, star p=p → ∀ᶠ x in 𝓝 p, DifferentiableAt ℂ f x)
    (i : Ode D g) : ContDiff ℝ 2 (f ∘ g) :=
  contDiff_iff_contDiffAt.mpr fun t =>
    (((PolyDisc.finiteD f (h (g t) (i.real t))).contDiffAt.restrict_scalars ℝ).comp _
      i.smooth.contDiffAt).of_le le_top

lemma ode_poster {κ : Type} {σ} {P : Momentum → CompM ι κ} (h : Poster σ P)
    (w : 0<σ) (i : Ode D g) (a b) :
    ContDiff ℝ 2 (fun t => P (g t) a b) := by
  refine score_aux (f:=fun p=> P p a b) ?_ i
  intro p hp
  filter_upwards [(Work.F07.stripOpen (α:=Axis) _).mem_nhds (Work.F07.realStrip _ w hp)]
    with q hq using h.shape hq a b

end ExactRunning
