import SatinThinCorner
import SatinThinPromenade
import SatinThinBeam
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x j
local notation "M"=> P.ColorHil j (ξ)
local notation "G"=> P.ManyF j (ξ)
local notation "E" r:max=> P.singleState 3 r x
local notation "Ω"=> P.colorZero j ξ
local notation "Γ"=>P.cartage j ξ
local notation "Η"=>P.seasons j ξ
local notation "κ"=>P.wealth j ξ
local notation "Πγ"=>P.enter j ξ
local notation "ω"=> P.heaven j ξ
/-! # quote comparison. Same shape and law. Pitched unprojection. -/
variable (C:Cover)(p:Plans j C r P)
local notation "Φx"=>P.Spectrum0 3
local notation "μ'"=> P.pillars 3
local notation "R!" v:max=>P.clockPlate r v C
local notation "Y0" v:max=> P.flume j C v p
noncomputable abbrev quoteBill (w:ℕ)(v:ℕ)(C:Cover)(p:Plans j C w P):P.naturalVox j v:=⟨P.flume j C v p,P.clock_colors _⟩
local notation "D!" v:max=> P.quoteBill j r v C p
abbrev quoteRay(w:ℕ)(v:ℕ)(C:Cover)(p:Plans j C w P):= P.province j ξ v (P.quoteBill j w v C p)
local notation "Q!" v:max=> P.quoteRay j x r v C p
include p
lemma quote_born(v:ℕ): P.birthF j v (P.visitOne v (P.clockPlate r v C)):=⟨D! v,rfl⟩
local notation "Ζ" v:max=> P.visitOne v (R! v)
lemma hue_pay (v:ℕ)(p0:P.birthF j v (P.centeredQ x v (P.clockPlate r v C))) : P.viewF j ξ v p0= Q! v - inner ℂ Ω (Q! v) • Ω:=by
 let y:= P.quote_born j C p v; change P.viewF j ξ v p0=P.province j ξ v (D! v)-_; have he:Q! v=P.viewF j ξ v y:= Eq.symm (P.holdsF j ξ v y _ rfl); let hh:= P.dewy
 change P.viewF j ξ v p0=Q! v - _; rw [he,P.view_scalar,P.single_agrees]; let c:= (E v) (Ζ v); let u:= P.faceUnit j v; exact (P.sixWard_view_sub j ξ v y (P.birthScaleJ j v c u) p0).trans (congrArg (fun r:M=> P.viewF j ξ v y-r) (show _=c • Ω from Eq.trans (P.viewJ_scale j ξ v c u) (congrArg (c •·) (P.view_one ..)))) -- tune
lemma carried_lens (u:s ≤ v) (t0:r≤ s) (g:ℝ) : ‖P.stateVox j ξ v (P.cameo j C g t0 u p)‖=zoomM P.par.R.L^(s-r)* ‖(g:ℂ) • (Q! v) - Q! s‖:=by
 change ‖P.compared_state j C p u t0 g (ξ)‖=_; rw [P.state_moving, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (zoomM_p L|>.le) _), ← (P.gnsIn j ξ).norm_map ((g:ℂ) • (Q! v) - (Q! s)),map_sub,map_smul]; simp_rw [P.coincides] -- tune parentheses
-- lens bound Cr persisted. Use real ratio without division ambiguous
lemma carried_upper {d:ℝ}(u:s ≤ v) (t0:r≤ s) (g:ℝ)(h: ‖P.stateVox j ξ v (P.cameo j C g t0 u p)‖^2 ≤ d^2) (q:0≤d): ‖(g:ℂ) • (Q! v)‖ ≤ ‖Q! s‖+d/zoomM P.par.R.L^(s-r):=by
 let C':=zoomM P.par.R.L^(s-r); let V:=(g:ℂ) • (Q! v); let F':= Q! s; have hK: 0 < C':= pow_pos (zoomM_p L) _; let t0':= P.cameo j C g t0 u p
 have ht: ‖V-F'‖ ≤ d/C':=(le_div_iff₀ hK).mpr ( (mul_comm ..).trans_le ( (P.carried_lens j x C p u t0 g).symm.trans_le ( (sq_le_sq₀ (norm_nonneg _) q).mp h)))
 calc ‖V‖= ‖(V-F')+F'‖:=by rw [sub_add_cancel]
      _ ≤ ‖V-F'‖ + ‖F'‖ := norm_add_le ..
      _ ≤ ‖F'‖+d/C' := by linarith only [ht]
omit p
variable (l:List Axis)
local notation "D△" f:max v:max=> (P.basePlay x f v).pivot P l
local notation "Gx" f:max v:max=> pivotQ (P.granule (P.megaK f v)) l
local notation "Ωκ"=>P.sidesPerTick
noncomputable abbrev beamWatch (f v:ℕ)(l:List Axis)(t:ℝ):= P.beamRaw j x ((P.basePlay x f v).pivot P l) t
lemma pivot_Fax (X:Cover) : P.issuing v (D△ f v) X=P.centeredQ x v ((Gx f v)+Ωκ • X):=by
 have he:(D△ f v).s=v:= (P.basePlay x f v).pivot_s P l; exact ( (congrArg (fun y=>P.issuing y (D△ f v) X) he.symm).trans ( (P.issuing_here ..).trans ((congrArg (P.chartAll X) (P.baseP_F x l f v)).trans (P.chart_center x ..))))
private lemma cent_bound {Z:Hilbert}(w z:Z)(h:‖w‖=1): ‖z-inner ℂ w z • w‖≤ 2*‖z‖:=by
 apply (norm_sub_le ..).trans; rw [norm_smul,h,mul_one]; have ht:=norm_inner_le_norm w z (𝕜:=ℂ); rw [h,one_mul] at ht; linarith only [ht]
include p
lemma cap_tide (X:Cover)(V:R! v = (Gx f v)+P.sidesPerTick • X)(e:ℝ)(t:P.roomy*P.macroStep v≤ P.meshPose v X j)(h:P.meshPose v X j ≤ e): ‖P.beamRaw j x (D△ f v) e‖≤2* ‖Q! v‖:=by
 let D':= D△ f v; let c:= P.meshPose v X j; let F':= Q! v; have he:D'.realWidth P j≤ c:=by unfold D'; rw [Apron.pivot_w,P.play_width]; exact t
 obtain ⟨z,hz⟩:=P.beam_grid_pose_view j x D' v X he ((P.basePlay x f v).pivot_s P l|>.le); have hp: P.issuing v D' X=P.centeredQ x v (R! v):= (P.pivot_Fax x l X).trans (congrArg _ V.symm); have hs:P.birthF j v (P.centeredQ x v (R! v)):=hp ▸ z
 apply (P.beam_right_le j x D' he h).trans; rw [← P.beam_tide_norm,← hz, P.identical_F j ξ v z hs hp, P.hue_pay j x C p]; exact cent_bound (Z:= P.ColorHil j (P.advocate 3 x j)) Ω F' (P.norms_color ..) -- tweak
lemma cap_travel {d:ℝ}(X:Cover)(V:R! v =(Gx f v)+Ωκ • X)(e:ℝ)(t:P.roomy*P.macroStep v ≤ P.meshPose v X j)(h:P.meshPose v X j ≤ e)(u:s ≤ v) (t0:r≤ s)(a g k:ℝ)(k₀:0≤k)(h₀: |a| ≤ k *|g|)(q:0≤d)(u0: ‖P.stateVox j ξ v (P.cameo j C g t0 u p)‖^2 ≤ d^2):
     ‖(a:ℂ) • P.beamWatch j x f v l e‖ ≤ 2*k* (‖Q! s‖ + d/zoomM P.par.R.L^(s-r)):=by
 let V':= P.beamRaw j x (D△ f v) e; let X':= Q! v; let Q₁:= ‖Q! s‖ + d/zoomM P.par.R.L^(s-r); have hb: ‖V'‖ ≤ 2*‖X'‖:= P.cap_tide j x C p l X V e t h -- explicit l implicit?
 have ht: ‖(g:ℂ) • X'‖≤ Q₁ := P.carried_upper j x C p u t0 g u0 q; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs] at ht ⊢; refine le_trans ( (mul_le_mul h₀ hb (norm_nonneg _) (mul_nonneg k₀ (abs_nonneg _)))) ?_
 linarith only [mul_le_mul_of_nonneg_left ht k₀] -- change Q₁ let
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.cap_travel
