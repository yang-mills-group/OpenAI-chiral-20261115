import YM.SU5.Reconstruction.Cross.Aperture
import Mathlib.Order.Filter.Curry
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
/-!
Generic argument for *absolute-position* averaging. Use all coordinates, in an
open neighborhood. Use the width and mesh sequentially enabled via the filter Curry,
not a fixed diagonal chosen in advance. This enables comparison over actual common
aperature of multidimensional time axes. See the construction notes.
-/
open _root_.YM.SelectionAnalysis
section finite_average
-- one convenient finite identity (fold independent translations into one average)
variable {A B Z I:Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [Fintype A] [Fintype B] [Nonempty B]
open Average
lemma omitOne (a:A)(D:(A→B)→Z) (w:B) (h: ∀ (i:A→B) x,D (update i a x)=D i) :
    Average.center D= Average.center (fun i: Average.Other A a→ B => D ((Equiv.funSplitAt a B).symm (w,i))) := by
  rw [Average.point a D]
  let f (x:B)(i:Average.Other A a→ B):= (Equiv.funSplitAt a B).symm (x,i)
  have he (x:B) (i): D (f x i)=D (f w i):= by
    rw [←h (f x i) w]; congr 1; funext b; by_cases k:b=a; subst b; rw [update_self]; simp [f]; rw [update_of_ne k]; simp [f,k]
  change Average.center (fun x:B=> Average.center (fun i: Average.Other A a→ B => D (f x i)))=_
  simp_rw [he,Average.constant]; rfl
end finite_average

variable (M:Mesh)
-- width index first; sampling fineness second.
abbrev nested : Filter (ℕ × ℕ) := (atTop : Filter ℕ).curry (atTop : Filter ℕ)
local notation "P"=>seeMesh M
-- CLASSICAL fixed denominator finite cardinal
abbrev Samples (r:ℕ) := Axis→Fin (M.L^r)
instance sample_live (r:ℕ) : Nonempty (Samples M r) := ⟨fun _=> ⟨0,avg_num M r⟩⟩
noncomputable def offsets (t r:ℕ) (p:Samples M r):seeMesh M:= grid M (t+r) (fun i=> (p i).val)
lemma offset_width (t r:ℕ)(p:Samples M r) (i : Axis) : |toR (M:=M) (offsets M t r p) i| ≤ (mill M t:ℝ):=by
  unfold offsets toR; rw [grid_eval]; refine (le_of_eq (congrArg abs (natural_time M (t+r) ((p i).val)))).trans ?_
  rw [abs_of_nonneg]
  · apply le_trans (show ((whenly M (t+r) ((p i).val):ℝ≥0):ℝ) ≤ (whenly M (t+r) (M.L^r):ℝ≥0).val from NNReal.coe_le_coe.mpr ((when_le M _ _ _).mpr ((p i).isLt.le)))
    refine le_of_eq (congrArg ((↑):ℝ≥0→ℝ) ?_); unfold whenly; rw [Nat.cast_pow]; simpa only [Nat.add_sub_cancel_left t] using mill_finer M t (t+r) (by omega)
  exact (whenly ..).property

def spacetimeDist (v w:P):ℝ := dist (toR (M:=M) v) (toR (M:=M) w)
lemma offset_distance (t r:ℕ)(p:Samples M r) (x:P) : dist (x+offsets M t r p) x ≤ (mill M t : ℝ) := by
 rw [dist_eq_norm]; simp only [add_sub_cancel_left] -- what if subgroup not norm? instance?
 apply (pi_norm_le_iff_of_nonneg (mill_pos M t|>.le)).mpr (fun i=> ?_)
 change |((offsets M t r p) i:ℝ)| ≤ _; exact offset_width ..

variable {M}
instance nested_ne_bot : NeBot nested:= by
  constructor; intro h; have p : ∀ᶠ _ : ℕ×ℕ in nested, False := by rw [h]; simp
  rw [eventually_curry_iff] at p; obtain ⟨_,h⟩:=p.exists; obtain ⟨_,h⟩:=h.exists; exact h

lemma nearby (M:Mesh)(x:seeMesh M)(A:Set (seeMesh M))(h:A∈𝓝 x) :
    ∀ᶠ q : ℕ×ℕ in nested,∀ p:Samples M q.2,x+offsets M q.1 q.2 p∈A:=by
  obtain ⟨u,hu,h⟩:= Metric.mem_nhds_iff.mp h
  rw [eventually_curry_iff]
  have hv:Tendsto (fun i:ℕ=> (mill M i:ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.mpr (vanishes M)
  filter_upwards [hv.eventually (gt_mem_nhds hu)] with i hi; exact Eventually.of_forall fun r p=> h ((offset_distance M i r p x).trans_lt hi)

noncomputable def smear {Z:Type*}[NormedAddCommGroup Z] [NormedSpace ℂ Z](M:Mesh) (F:seeMesh M → Z)(x:seeMesh M)(t:ℕ×ℕ) : Z := Average.center (fun p:Samples M t.2=>F (x+offsets M t.1 t.2 p))
theorem smear_here {Z:Type*}[NormedAddCommGroup Z] [NormedSpace ℂ Z](M:Mesh) (F:seeMesh M → Z)(x:seeMesh M)(h:ContinuousAt F x): Tendsto (smear M F x) nested (𝓝 (F x)) := by
  rw [Metric.tendsto_nhds]; intro ε e
  filter_upwards [nearby M x (F ⁻¹' (Metric.closedBall (F x) (ε/2))) (h (Metric.closedBall_mem_nhds _ (half_pos e)))] with t ht
  change dist _ (F x) < _
  refine (le_trans ?_ (le_refl (ε/2))).trans_lt (half_lt_self e)
  exact (by
    have he: (Average.center (fun _ : Samples M t.2 => F x))=F x:= Average.constant _
    -- use inequality with constant on right of center
    exact (show dist (smear M F x t) (Average.center (fun _ : Samples M t.2=> F x)) ≤ _ from Average.norm_dist ht) |> ((he ▸ ·)))

-- reduction lemmas for average of errors.
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
local notation "D₀" F:max v:max => smear M F v -- binder implicit
lemma beside (F G:seeMesh M → Z)(x:seeMesh M)(z:Z)(t:Tendsto (D₀ F x) nested (𝓝 z))
    (h:Tendsto (fun y=>dist (F y) (G y)) (𝓝 x) (𝓝 0)) : Tendsto (smear M G x) nested (𝓝 z):=by
  apply tendsto_of_tendsto_of_dist t
  refine Metric.tendsto_nhds.mpr ?_
  intro ε e; filter_upwards [nearby M x ((fun y=>dist (F y) (G y)) ⁻¹' Set.Iio (ε/2)) (h (gt_mem_nhds (half_pos e)))] with t A
  change dist (dist (smear M F x t) (smear M G x t)) 0< ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg]; exact ((Average.norm_dist (fun p : Samples M t.2=> (A p).le)): dist (smear M F x t) (smear M G x t) ≤ ε/2).trans_lt (half_lt_self e) -- tune coercion ht
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.smear_here
