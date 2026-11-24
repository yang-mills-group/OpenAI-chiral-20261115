import YM.SU5.Reconstruction.Cross.Slot
import YM.SU5.Reconstruction.Footprint
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
/-! # Physical slots; graph localization facts in Euclidean setting. -/
-- max norm RSpace
section
lemma pitch_norm (Λ:Preparation)(s:ℕ): ((mill (timeMesh Λ) s):ℝ) = gaugeMesh Λ s*(ruler Λ.block:ℤ):=by
 unfold timeMesh mill gaugeMesh ruler; dsimp only; push_cast; field_simp
 <;> ring
lemma bell_norm (Λ:Preparation) (s:ℕ)(x:ℤ) : bell (timeMesh Λ) s x= gaugeMesh Λ s*((ruler Λ.block*x:ℤ):ℝ) :=by unfold bell; push_cast; change (x:ℝ)*(↑(mill (timeMesh Λ) s):ℝ) = _; rw [pitch_norm]; ring
variable {s : ℕ} (x : Cover)
local notation "ψ" => gaugeMesh Λ s
local notation "R" => (reserve Λ l:ℝ)*ψ
lemma rim (t:ℝ) (j:Axis) (v: |t| ≤ (reserve Λ l:ℝ)*gaugeMesh Λ s) :
    (Function.update (gaugePosition Λ s x) j (t+gaugePosition Λ s x j))∈stamp Λ l s x:=by
 apply stamp_abs.mpr; intro i
 by_cases h:i=j; · rw [h,update_self,add_sub_cancel_right]; exact v
 rw [update_of_ne h,sub_self,abs_zero]; exact (abs_nonneg t).trans v
variable (j:Axis) (S:Finset Cover)
theorem stamp_span {a b:ℤ} : silhouette Λ l s S⊆ {y:RSpace|y j∈ Icc (bell Μ s a) (bell Μ s b)} ↔ Between (tent Y H) j (ruler Λ.block*a) (ruler Λ.block*b) S :=by
 let w:=ruler Λ.block; let A:=w*a; let B:=w*b; have hp:0 <ψ:=gaugeMesh_pos ..
 have h1(i:ℤ): (A:ℤ) + reserve Λ l ≤ i ↔ bell Μ s a+R ≤ (i:ℝ)* ψ := by
    unfold A w; rw [bell_norm, mul_comm (gaugeMesh Λ s),←_root_.add_mul,mul_le_mul_iff_left₀ hp]; norm_cast
 have h2(i:ℤ): i+(reserve Λ l :ℤ) ≤ B ↔ (i:ℝ)*ψ+R ≤ bell Μ s b:=by unfold B w; rw [bell_norm, mul_comm (gaugeMesh Λ s),← _root_.add_mul,mul_le_mul_iff_left₀ hp]; norm_cast
 constructor
 · intro h x i; let L:= gaugePosition Λ s x; let c:ℝ:=R; have hc: 0≤c:=mul_nonneg (by positivity) hp.le
   have ha:= h (silhouette_iff.mpr ⟨x,i, rim (Λ:=Λ) (s:=s) (l:=l) x c j (by rw [abs_of_nonneg hc])⟩); have hb:= h (silhouette_iff.mpr ⟨x,i,rim (Λ:=Λ) (s:=s) x (-c) j (by rw [abs_neg,abs_of_nonneg hc])⟩)
   change A+ ↑(reserve Λ l) ≤ x j ∧ x j + ↑(reserve Λ l) ≤ B
   apply And.intro ((h1 _).2 ?_) ((h2 _).2 ?_) -- tune
   all_goals
     have u := ha.2; have v:=hb.1; rw [update_self] at u v
     unfold gaugePosition at *; unfold c at *; linarith -- gaugePosition def multiplication order? tune
 intro h y e; obtain ⟨x,i,v⟩:= silhouette_iff.mp e; let z:= h x i; let P':=y j
 have w: (x j:ℝ)*ψ≥bell Μ s a+R:= (h1 _).1 z.1
 have hb:(x j:ℝ)*ψ+R ≤ bell Μ s b:= (h2 _).1 z.2
 obtain ⟨d,e⟩:=abs_le.mp (stamp_abs.mp v j); unfold gaugePosition at *; exact ⟨by linarith, by linarith⟩
end
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.stamp_span
