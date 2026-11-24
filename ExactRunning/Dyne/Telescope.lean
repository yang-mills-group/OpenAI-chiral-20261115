import ExactRunning.Dyne.Wake

/-!
# Uniform sublinear bound over adjacent steps
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

def tailEnd (E : Pylon G) (i : G.ColorIndex) (d : ℝ) :=
  epValue E.F (Latitude.native d) i + G.slopeConstant * Real.log d⁻¹

def owes (G : Gauge) (L : Side) := G.slopeConstant * Real.log L.val

lemma tendsto_scale {a : ℝ} (h : 0<a) :
    Tendsto (fun d => d*a) (𝓝[>] 0) (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨by
    simpa [ContinuousWithinAt] using (continuous_id.mul_const a).continuousWithinAt (x:=0) (s:=Set.Ioi 0),
    by filter_upwards [self_mem_nhdsWithin] with d hd using mul_pos hd h⟩

/-- We take d as radius on **input**, d*L coarse output. -/
lemma BlockTie.asRuns (X : BlockTie E I) (i : G.ColorIndex) :
    Tendsto
      (fun d=> tailEnd E i d - tailEnd I i (d*X.L.val))
      (𝓝[>] 0)
      (𝓝 (X.q + owes G X.L)) := by
  have hu := side_pos X.L
  have h := X.h_toFull i
  rw [← X.owns i] at h
  rw [←zero_add X.q]
  refine ((((E.endpoint.correction X.L i).add (h.comp (tendsto_scale hu))).add_const
    (owes G X.L)).congr' ?_) -- zero+
  filter_upwards [self_mem_nhdsWithin] with d hd
  have hd' : 0<d := hd
  have he := X.comparison (mul_pos hd' hu) i
  have hq : X.back (d*X.L.val) = Latitude.incoming X.L d := by rw [mul_comm];rfl
  rw [hq] at he
  simp only [Function.comp_apply,he,tailEnd,ridge,owes,Real.log_inv,Real.log_mul hd'.ne' hu.ne']
  ring

structure Arch (G : Gauge) (L : Side) (u : ℕ→ℝ) where
  atPoint : ℕ→Pylon G
  make (j : ℕ) : ∃ x : BlockTie (atPoint j) (atPoint (j+1)), x.q = u j ∧ x.L = L

variable {u : ℕ→ℝ} (a : Arch G L u) (i : G.ColorIndex)

lemma Arch.interval (j k : ℕ) :
    Tendsto
      (fun d=> tailEnd (a.atPoint j) i d - tailEnd (a.atPoint (j+k)) i (d*(L.val:ℝ)^k))
      (𝓝[>] 0)
      (𝓝 (∑ r∈range k, (u (j+r)+owes G L))) := by
  induction k with
  | zero => simp only [pow_zero,mul_one,Nat.add_zero,sub_self,sum_range_zero]; exact tendsto_const_nhds
  | succ k h =>
    obtain ⟨x,hx,e⟩ := a.make (j+k)
    have hd := x.asRuns i
    rw [hx,e] at hd
    rw [sum_range_succ]
    exact (h.add (hd.comp (tendsto_scale (pow_pos (side_pos L) k)))).congr
      (fun d=> by simp only [Function.comp_apply, pow_succ, ← mul_assoc, sub_add_sub_cancel]; rfl)

include i in
/-- Uniform O(1) shift error, positive orientation (toward coarser). -/
theorem Arch.error {A C : ℝ} (ha : 0≤A) (hc : 0≤C)
    (h : ∀ j, Grounds A C (a.atPoint j).F)
    (j k : ℕ) :
    |∑ r∈range k, (u (j+r)+owes G L)| ≤ 2 * SlabPole.charge G A C := by
  have hu (r) (w : ℝ) (hw : 0<w) :
      ∀ᶠ d in 𝓝[>] 0, |tailEnd (a.atPoint r) i (d*w)| ≤ SlabPole.charge G A C := by
    apply (tendsto_scale hw).eventually (p:=fun x=> |tailEnd (a.atPoint r) i x| ≤ SlabPole.charge G A C)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with x ht hl using
      (a.atPoint r).endpoint.finite_part (h r) ha hc ht hl _
  refine le_of_tendsto (a.interval i j k).abs ?_
  filter_upwards [hu j 1 zero_lt_one, hu (j+k) _ (pow_pos (side_pos L) k)] with d h g
  rw [mul_one] at h
  rw [two_mul]
  exact (abs_sub _ _).trans (add_le_add h g)

end ExactRunning
