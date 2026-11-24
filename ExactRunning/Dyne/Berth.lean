import ExactRunning.Dyne.Cutoff

/-!
# Intensive incoming Hessians

Volume factor and aliases in the intensive probe on a pullback over W:
exactly `cargo` using the base splitting into waves (`nose`) and the
resonance condition, no approximation here.
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

def harmonic (K : Kin (Entry G)) (i : G.ColorIndex) (l : Site X.L) (t : ℝ) : ℂ :=
  nose X.Phi (-tilt 0 t) (-l) (stripe i) ⬝ᵥ
    K (aliasAt (tilt 0 t) l) *ᵥ nose X.Phi (tilt 0 t) l (stripe i)

def cargo (K : Kin (Entry G)) (i : G.ColorIndex) (t : ℝ) : ℂ :=
  (X.L.val:ℂ)^4 * ∑ l, X.harmonic K i l t

private lemma nose_top {p : Momentum} (h : star p=p)
    (l : Site X.L) (a b : Entry G) :
    ∀ᶠ q in 𝓝 p, DifferentiableAt ℂ (fun q => nose X.Phi q l a b) q := by
  let W := plankTile X.L (Loc G 1)
  let d := ((inch X.L:ℂ)^2)
  filter_upwards [(Work.F07.stripOpen (α:=Axis) X.η).mem_nhds (Work.F07.realStrip _ X.hη h)] with q hq
  have hp : BillD (fun p=> (W p)⁻¹* X.Phi p) q :=
    BillD.bond ((tile_lit q).take (tile_solid q)) (X.bridge.1.shape hq)
  convert! (hp (l,b) a).const_mul d using 1
  funext p
  dsimp only
  rw [nose,stackSlice,untier,crewAlias,mulVec_mulVec, Pi.smul_apply,mulVec_single_one]
  rfl

lemma nose_smooth {g : ℝ → Momentum} {D} (h : Ode D g)
    (l : Site X.L) (a : Entry G) :
    ContDiff ℝ 2 (fun t => nose X.Phi (g t) l a) :=
  contDiff_pi.mpr fun b=> score_aux (f:=fun q => nose X.Phi q l a b)
    (fun _ hp=> X.nose_top hp l a b) h

lemma harmonic_smooth {K : Kin (Entry G)} {r} (k : Score (X.back r) K)
    (i : G.ColorIndex) (l : Site X.L) :
    ContDiff ℝ 2 (X.harmonic K i l) :=
  Score.val k ((Ode.magnetic _).aliases X l)
    (X.nose_smooth (Ode.magnetic (ridge r)).neg (-l) (stripe i))
    (X.nose_smooth (Ode.magnetic (ridge r)) l (stripe i))

lemma cargo_smooth {K : Kin (Entry G)} {r} (k : Score (X.back r) K)
    (i : G.ColorIndex) : ContDiff ℝ 2 (X.cargo K i) := by
  unfold cargo
  exact contDiff_const.mul <| ContDiff.sum fun l _=> X.harmonic_smooth k i l

def passes (U : Law (Entry G)) : Law (Entry G) :=
  fun m=> U (X.up m) ∘ X.lift0 m

lemma coBeat {F : Link G m → ℝ} (u v) :
    (cents m:ℂ)⁻¹ * beat F 0 2 ![u,v] = 2 * fiscal F u v := by
  rw [beat_as_cost]
  norm_num [Nat.factorial,fiscal,mul_left_comm]

lemma sendsEcho {r} {t : ℝ} {a : Site m} (g : rolls (mon a) (tilt 0 t)) {U : Law (Entry G)} {K}
    (h : Resonance (X.back r) K (U (X.up m))) (i : G.ColorIndex) :
    echo (X.passes U m) a (stripe i) (stripe i) = X.cargo K i t := by
  let y (l : Site X.L) := duesM (X.step m) a (tilt 0 t) l
  have k l := duesM_real (X.step m) a l g
  have q (l : Site X.L) :=
    ((Ode.magnetic (ridge r)).aliases X l).quiet t
  let F := U (X.up m)
  change echo (F ∘ uniformM (X.W m)) _ _ _ = _
  rw [echo,coBeat (G:=G), fiscal_bolted (X.step m) F _ _ _ _ _ (X.via m) g.flip_sign g h.reg.analyticAt]
  rw [mul_left_comm,cargo]; refine congr_arg (fun z => (X.L.val:ℂ)^4 * z) ?_
  rw [sum_comm,mul_sum]
  refine sum_congr rfl fun l _=> ?_
  rw [mul_sum,sum_eq_single (-l)]
  · rw [duesM_neg _ _ g, ←coBeat (G:=G)]
    exact h.pair (k l) (q l) ..
  · intro j _ hj
    rw [← coBeat (G:=G)]
    let d j := duesM (X.step m) (-a) (-tilt 0 t) j
    have hk : rolls (mon (d j)) (aliasAt (-tilt 0 t) j) :=
      duesM_real (X.step m) (-a) j g.flip_sign
    have hu := ((Ode.magnetic (ridge r)).neg.aliases X j).quiet t
    rw [h.waves (hu.rolls hk.symm) ((q l).rolls (k _).symm) (k l) ..]
    rw [if_neg ?_, mul_zero]
    intro e
    apply hj
    apply duesM_one _ _ g.flip_sign
    rw [duesM_neg _ _ g]
    exact eq_neg_of_add_eq_zero_left e
  simp

theorem cargo_song {U : Law (Entry G)} {K : Kin (Entry G)} {r : ℝ}
    (h : Playing (X.back r) U K) (i) :
    Melody X.lo i (X.passes U) (X.cargo K i) where
  smooth := X.cargo_smooth h.score _
  lit m _ := ContDiffAt.comp (f:=X.lift0 m) _ (by
      rw [map_zero];exact (h.res _).reg) (X.lift0 m).contDiff.contDiffAt
  plays {t} w := by
    simp_rw [fun n=> X.sendsEcho (w.hits n) (h.res ..) i]
    unfold cargo harmonic
    refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun l _=> ?_)
    let a := w.split X l
    have e := h.played ((Ode.aliases X (Ode.magnetic (ridge r)) l).real t)
      ((Ode.aliases X (Ode.magnetic (ridge r)) l).quiet t)
      a.grows
    let u := nose X.Phi (-tilt 0 t) (-l) (stripe i)
    let v := nose X.Phi (tilt 0 t) l (stripe i)
    exact
      ((show Continuous (fun M : CompM (Entry G) (Entry G) => u ⬝ᵥ M *ᵥ v)
        from continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)).tendsto _).comp e

end BlockTie
end ExactRunning
