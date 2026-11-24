import YM.SU5.Assay.Reel
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Six

variable {P:Spine}{f g:P.Test}{S T D:Finset Cover}{s t:ℕ}{W:Bool}
local notation "K"=> P.calibration
variable {j:Axis}{d w:ℕ}
/-!
# Shrinking Reel charges and footprints. Use 1+s² copies of the sticker,
allow exponential input growth (at the price width, axis j only).
-/
abbrev ply (s:ℕ):=1+s^2
variable {Z:Lead.Clan}
namespace Glaze
def Tiny (B:ℕ→P.Glaze):Prop:=Tendsto (fun s=> ((B s).w:ℝ)*P.macroStep s) atTop (𝓝 0)
lemma aperture (B:P.Glaze)(s:ℕ)(i:Axis): (B.apron s).realWidth P i=(B.w:ℝ)*P.macroStep s:= by
 change (B.w:ℤ) * (mill (timeMesh P.par) s:ℝ)=_
 push_cast; rfl
def Grows (j:Axis)(B:ℕ→P.Glaze):Prop:=∃ C:ℝ,0≤ C ∧ ∃ L:ℝ,0≤ L ∧ ∀ᶠ s in atTop,‖(B s).tile j s‖≤ C*L^s
end Glaze

namespace Reel
variable (R:P.Reel j Z){B:ℕ→P.Glaze}
lemma shadow_vanish (h:Glaze.Grows j B):
  Tendsto (fun s=>‖(R.dusk (B s) (ply s)).tile j s‖) atTop (𝓝 0):=by
 obtain ⟨C,c,L,l,w⟩:=h
 let D:=R.c
 have d:0≤D:=R.paid.2.2.1
 have e:D<1:=R.paid.2.2.2.1
 have hy:Tendsto (fun N:ℕ=> L*D^N) atTop (𝓝 0):=by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one d e).const_mul L
 obtain ⟨N,g⟩:=(hy.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))).exists -- gt_mem_nhds?
 let q:= L*D^N; have ht: 0≤q:=by unfold q; positivity
 have hk : Tendsto (fun s:ℕ=> C*q^s) atTop (𝓝 0):=by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ht (show q<1 from g)).const_mul C
 apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hk (Eventually.of_forall (fun _=>norm_nonneg _))
 filter_upwards [w,R.history,eventually_ge_atTop N] with s v u y
 have hp:N*s≤ply s:=le_trans (Nat.mul_le_mul_right s y) (by unfold ply; rw [pow_two]; omega)
 unfold q
 apply (u _ _).trans
 rw [mul_pow,←pow_mul,←mul_assoc]
 exact mul_le_mul v (pow_le_pow_of_le_one d e.le hp) (pow_nonneg d _) (mul_nonneg c (pow_nonneg l _))

variable (P) in
lemma macro_decay (k:ℕ): Tendsto (fun s:ℕ=>(s:ℝ)^k*P.macroStep s) atTop (𝓝 0):=by
 let M:=timeMesh P.par; let L:ℝ:=↑M.L; have hL: 1<L:=by unfold L; exact_mod_cast (show 1<M.L from M.Llarge)
 let A:ℝ:=M.base
 have h:‖L⁻¹‖<1:= by rw [norm_inv,Real.norm_of_nonneg (zero_le_one.trans hL.le)]; exact inv_lt_one_of_one_lt₀ hL
 have ht: Tendsto (fun s:ℕ=>(s:ℝ)^k*(L⁻¹)^s*A) atTop (𝓝 0):=by simpa using ((summable_pow_mul_geometric_of_norm_lt_one k h).tendsto_atTop_zero.mul_const A)
 apply ht.congr; intro s
 change _ = _* ((M.base / (M.L:ℝ≥0)^s :ℝ≥0):ℝ)
 unfold A L; rw [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_natCast,inv_pow]; ring

def wrapMix (B:ℕ→P.Glaze)(s:ℕ):P.Glaze:=R.twist (B s) (ply s)
lemma wrap_span (s:ℕ): (R.wrapMix B s).w=(B s).w+ply s*(R.d+R.d+1):=R.dusk_span ..
lemma stays_tiny (h:Glaze.Tiny B):Glaze.Tiny (R.wrapMix B):=by
 have ht:=h.add ((P.macroStep_zero.add (macro_decay P 2)).mul_const ((R.d:ℝ)+R.d+1))
 simp only [zero_add,zero_mul] at ht
 apply ht.congr; intro s
 rw [wrap_span]; unfold ply; push_cast; ring

lemma tile_splice (G:P.Glaze)(s M:ℕ):
    (R.twist G M).tile j s = (G.swell (d:=(R.dusk G M).w) (by rw [R.dusk_span];omega)).tile j s - (R.dusk G M).tile j s:=by
 let D:=R.dusk G M
 let V:= G.swell (d:=D.w) (by unfold D; rw [R.dusk_span];omega)
 change P.meanBox j s (D.w+D.w) (P.shifts j D.w (V.F - D.F))= _
 rw [map_sub]; exact meanBox_sub s (V.centers j) (D.centers j)
lemma stays_paid (h:Glaze.Grows j B):Glaze.Grows j (R.wrapMix B):=by
 obtain ⟨C,c,L,l,w⟩:=h
 refine ⟨2*C,by positivity,L,l,?_⟩
 filter_upwards [w,R.history] with s v u
 let G:= B s; let n:=ply s; let D:=R.dusk G n; have h:G.w≤ D.w:=by unfold D; rw [dusk_span];omega
 change ‖(R.twist G n).tile j s‖≤_
 rw [tile_splice]
 have he:‖D.tile j s‖≤‖G.tile j s‖:= (u G n).trans (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ R.paid.2.2.1 R.paid.2.2.2.1.le))
 apply le_trans (norm_sub_le ..)
 apply (add_le_add ((G.tile_swell j h s).trans v) (he.trans v)).trans
 exact le_of_eq (by ring)
end Reel
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
