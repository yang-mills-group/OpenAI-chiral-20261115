import ExactRunning.Dyne.Rudder
/-!
# Pictures contribute intensive magnetic coefficients

Connector for kinetic and one-loop inputs: Picture slots at order
two give intensive Hessians by resonance (note factor two). Convert
our single-color probe to the same `alphaPay` used for quadratic
Pictures; vanishes under fourth-order softness.
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

namespace Picture
variable {M : Picture G 1} {U : Law (Entry G)} {σ A : ℝ} {D : Latitude}

def kin (M : Picture G 1) : Kin (Entry G) :=
  fun p => (2:ℂ) • rowscape M p

lemma exact_entry {f : Link G m → ℝ} (h : ∀ i j,Firm σ A (M i j)) (k : Recorded M f 0)
    (a b : Site m) (p : Momentum) (hb : rolls (mon b) p) (i j) :
    fiscal f (relay a i) (relay b j) = if a+b=0 then rowscape M p i j else 0 := by
  have w : Recorded M f (cents m*0) := by rwa [mul_zero]
  split
  next e =>
    rw [eq_neg_of_add_eq_zero_left e]
    have hy := royalty_right (m:=fun _=>m) (ε:=fun _=>0)
      h (fun _=>w) i j (fun _=>b) (fun _=>p) (fun _=>hb)
        tendsto_const_nhds (hb.metric (real_frequency _)) tendsto_const_nhds
    exact tendsto_nhds_unique tendsto_const_nhds hy
  next e => exact norm_eq_zero.mp (le_antisymm (clips_off w i j a b e) (norm_nonneg _))

lemma resonance {f : Link G m → ℝ} (h : ∀ i j,Firm σ A (M i j)) (k : Recorded M f 0)
    (c : ContDiffAt ℝ ω f 0) : Resonance D (kin M) f := by
  refine ⟨c, ?_⟩
  intro a b p i j _ _ hb
  rw [← inv_mul_cancel_left₀
      (show (cents m:ℂ)⁻¹≠0 from inv_ne_zero (by exact_mod_cast (cents_pos (m:=m)).ne')) (beat f 0 2 ![_,_]),
     inv_inv, BlockTie.coBeat, exact_entry h k a b p hb]
  simp only [kin, Matrix.smul_apply,smul_eq_mul]
  split_ifs
  · rfl
  simp

lemma score (D : Latitude) (h : ∀ i j,Firm σ A (M i j)) : Score D (kin M) := by
  intro g e i j
  let u := Matrix.vecCons i.2 (Matrix.vecCons j.2 Matrix.vecEmpty)
  let v := Matrix.vecCons i.1 (Matrix.vecCons j.1 Matrix.vecEmpty)
  refine contDiff_const.mul
    (score_aux (f:=fun p=> rowscape M p i j) ?_ e)
  intro p hp
  let r (x : Momentum) : Space 1 := fun j => x j.2
  have a : Differentiable ℂ r := differentiable_pi.mpr fun i => differentiable_apply _
  have hf := h u v
  have hu : star (r p)=r p := funext fun i=> congr_fun hp i.2
  filter_upwards [a.continuous.continuousAt.tendsto
     ((Work.F07.stripOpen _).mem_nhds (hf.in_range hu))] with q hq
  exact (hf.1.hol _ hq).comp q (a q)

def plays (D : Latitude) (h : ∀ i j,Firm σ A (M i j)) (k : ∀m, Recorded M (U m) 0)
    (c : ∀m, AnalyticAt ℝ (U m) 0) : Playing D U (kin M) :=
  Playing.native (score D h) fun m=>resonance h (k m) (c m).contDiffAt

theorem alpha (h : ∀ i j,Firm σ A (M i j)) (i) :
    alphaK (kin M) i = alphaPay i M := by
  let g := pressLens M ![i,i] 1 1
  let v : Track := Lattice.step (0:Axis)
  let W := ContinuousLinearMap.toSpanSingleton ℝ v
  have a : AnalyticAt ℝ g (W 0) := by rw [map_zero]; exact priceL h ..
  have c : magcurve (kin M) i = (2:ℂ) • (g ∘ W) := rfl
  have z : ContDiffAt ℝ 2 (g ∘ W) 0 := a.contDiffAt.comp 0 W.contDiff.contDiffAt
  rw [alphaK,c,quad_re
    (f:=(2:ℂ) • (g ∘ W))
    (z.const_smul (2:ℂ)),quad_weight z]
  have q : quad (g ∘ W)=speedy g 2 v := by
    rw [quad,wired W a]
    norm_num [speedy,Tensor.diagonal,Tensor.coeff,Nat.factorial,map_zero,show W 1=v from one_smul ℝ v]
    rfl
  rw [q]
  simp [g,v,alphaPay, leapTip, smul_eq_mul,Complex.mul_re]

open Asymptotics

lemma alpha_zero (h : ∀ i j,Firm σ A (M i j))
    (r : ∀ i j, Rays 4 (M i j ∘ axes)) (i) :
    alphaK (kin M) i = 0 := by
  rw [alpha h i]
  let f := pressLens M ![i,i] 1 1
  have w : Rays 4 f := by
    intro y
    dsimp only [f,pressLens]
    simp_rw [map_smul]
    exact r _ _ _
  have hz := (rays_jet (priceL h ![i,i] 1 1) _).mp w 2 (by simp)
  simp [alphaPay,leapTip,speedy,Tensor.diagonal,Tensor.coeff,hz]

theorem lateral (D : Latitude) (w : ∀i, Contractible (M i)) :
    Lateral D (kin M) LinearMap.id := by
  intro g hg t v u
  have h := both_ends w (hg.real t)
  simp only [LinearMap.id_coe,id_eq]
  constructor
  · unfold kin
    rw [mulVec_mulVec,smul_mul,h.1,smul_zero,zero_mulVec,dotProduct_zero]
  unfold kin
  rw [dotProduct_comm,inflow,mulVec_mulVec,Matrix.mul_smul,h.2,smul_zero,zero_mulVec,zero_dotProduct]

end Picture

end ExactRunning
