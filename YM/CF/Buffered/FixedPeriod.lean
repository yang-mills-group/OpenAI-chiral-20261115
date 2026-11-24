import YM.CF.Buffered.Transfer

/-! # At the first limit, actual cutoff, fixed moment

Bridge positivity with presrec, rec-delta and the heat history matching
precisely on the mark arguments. Here all comparisons are on the fixed
period, and we enlarge the UV lower threshold there. Mark is fixed.
No generic comparator/stability assumed through either normalization.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window Vale Girt
open Py (Vestal Cape)
open Reed (Fine)
open Advance Heat Burn
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
section
variable {m B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ}
variable {P : Grasp Y B e} {R : Cape m B L}
lemma Granted.paid {n J : ℕ} {Z : Vestal m B L} {A : Steps m B L} {q : Chi} {d : ℝ} {Q : ℕ → Haro.SpaceM} (h : Granted P Z R q d n Q A J) (k : ℕ) (u : k<n) : Integrable (denZ (Z k) P (R k)) (city _) ∧ Measurable (R k) := by
  obtain ⟨w⟩:= h.grant k u; obtain ⟨x,r,t,l,H⟩:= w.cap; have ht:=Girt.buoy w (A k) (h.aligned k u) (h.branch k u) (Q k).val
  have hp := (Env.integrableX ht ((city _).prod (city _))).integral_prod_left
  refine ⟨hp.congr ?_, l.bill⟩; exact ((measurePreserving_fst («μ»:=prior group (More (cell m B L k))) («ν»:=depot (cell m B L k))).quasiMeasurePreserving.ae ((h.noTies k u.le) _)).mono fun z p=> h.wears _ u z p
variable (P R) (X Z : ℕ→Vestal m B L) (b₀ : ℕ) (C M : ℝ)
local notation "c" => Vale.cell m B L 0
-- Inputs from lemma comparing glued histories (ms. p-delt) and pc-low.
structure AtUV (n : ℕ) : Prop where
  diffK : Delta P (X n 0) (Z n 0) (R 0) (bill m.val n b₀ M)
  low : presrec m.val C ≤ ‖vac0 P (Z n 0) (R 0)‖
  pay : Integrable (denZ (Z n 0) P (R 0)) (city _)
  pay' : Integrable (denZ (X n 0) P (R 0)) (city _)
  loom : Measurable (R 0)
variable {P R X Z C M b₀} {n : ℕ → ℕ} (u : Tendsto n atTop atTop)
variable (v : ∀ᶠ k in atTop, AtUV P R X Z b₀ C M (n k))
include u v
lemma lowerAt_fixed : ∀ᶠ k in atTop, (presrec m.val C)/2 ≤ ‖vac0 P (X (n k) 0) (R 0)‖ ∧ partitionZ (X (n k) 0) P (R 0)≠0 ∧ partitionZ (Z (n k) 0) P (R 0)≠0 := by
  have he : 0<presrec m.val C:= Real.exp_pos _
  filter_upwards [v, ((bill_shrinks b₀ m.val M).comp u).eventually (gt_mem_nhds (half_pos he))] with i p h
  have hg:= transfer_lower P _ _ _ p.loom p.pay' p.pay p.diffK _ p.low h.le
  exact ⟨hg,part_ne_zero _ _ _ (norm_pos_iff.mp ((half_pos he).trans_le hg)), part_ne_zero _ _ _ (norm_pos_iff.mp (he.trans_le p.low))⟩
lemma ratios_at {F : Mark (cell m B L 0)} (g : RG.Envelope F) (Y : ℂ) (h : Tendsto (fun k => atZero P (X (n k)) R F) atTop (𝓝 Y)) : Tendsto (fun k => atZero P (Z (n k)) R F) atTop (𝓝 Y) := by
  let a := fun k => atZero P (X (n k)) R F; let b:=fun k=> atZero P (Z (n k)) R F; obtain ⟨B,hb⟩:=g.cost
  have ht : Tendsto (fun i=> a i-b i) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun i=>(B+(‖Y‖+1))*bill m.val (n i) b₀ M / presrec m.val C) atTop (𝓝 0) from ?_)
    · have he:= Real.exp_pos (-C*m.val^4); filter_upwards [v, ((bill_shrinks b₀ m.val M).comp u).eventually (gt_mem_nhds (half_pos he)), h.norm.eventually (gt_mem_nhds (show ‖Y‖ < ‖Y‖+1 by linarith))] with i w p h
      change ‖a i-b i‖ ≤ _
      unfold a b atZero; rw [←same_ratio, ←same_ratio]; refine transfer_ratio P _ _ _ w.loom w.pay' w.pay w.diffK he w.low p.le F g hb ?_; rw [same_ratio]; exact h.le
    have he := (((bill_shrinks b₀ m.val M).comp u).const_mul (B+(‖Y‖+1))).div_const (presrec m.val C); simpa using he
  simpa only [a,b, sub_sub_self,sub_zero] using h.sub ht
section cut
variable (q : Chi) (d : ℝ) (A : ℕ → Steps m B L) (Q : ℕ → ℕ → Haro.SpaceM) {D J w U : ℕ} (s : ℤ) (i : Axis) (p : Margin L D w J U)
variable (p₀ : Stencil.LaurentRadius j L D) (l : 3 ≤ L.val) (a : ∀ k,LoomLaw (R k) w)
  (h : ∀ᶠ k in atTop, Nonempty (Donor P (Z (n k)) R (n k)) ∧ Granted P (Z (n k)) R q d (n k) (Q (n k)) (A (n k)) J)
include h l p a p₀
lemma fixedPeriod {f : Mark (cell m B L 0)} (t : AtSupport false (band c i (gaugeShift B s) U) f) (Y : ℂ) (u' : Tendsto (fun k=>atZero P (X (n k)) R (squareMark (gaugeShift B s) i f f)) atTop (𝓝 Y)) : 0 ≤ Y := by
  have he:=ratios_at u v (F:=squareMark (gaugeShift B s) i f f) (env_mult ((t.refl i (gaugeShift B s)).env) t.env) _ u'
  apply ge_of_tendsto he; filter_upwards [h, lowerAt_fixed u v] with k j z; exact donor P (Z (n k)) R q d (n k) (Q (n k)) (A (n k)) i p₀ l j.2 (fun k _=>a k) p s (Classical.choice j.1) z.2.2 t
end cut
end
end YM.CF.Buffered
