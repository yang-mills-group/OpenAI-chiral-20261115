import YM.SatinExist.Stile
import YM.SatinExist.Shield
import YM.SatinExist.Cameo
import YM.SatinExist.Hall
import YM.SatinExist.Fence
import SatinThinRampart
import SatinThinAngle
import YM.SatinExist.Glacis
import SatinThinSegno

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
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
-- specialize now to OP height desk
open Aria Casting MacroGrid
variable (w:ℕ)(h:Watchdesk (f:=f) P j X w)(x:P.Spectrum0 3)
local notation "£" v:max=> P.longtruck w f v
local notation "κ!" Xp:max=> risingtruck P w (f:=f) (v:=Xp) h.w0
local notation "G" v:max=> P.deskCard j X w h v
local notation "B" v:max=> P.deskValue j X w h v
local notation "χ"=> P.advocate 3 x j
local notation "Φ"=> P.colorSpace j χ
local notation "υ" v:max y:max=>P.voxTest j v y
local notation "H₀"=> P.ColorHil j χ
local notation "ω"=> P.colorZero j χ
local notation "Η"=> P.physicalEnergy j χ
local notation "Λw"=>timeMesh P.par
local notation "K!"=> whenly (timeMesh P.par) f w
local notation "Y!" s:max=> P.visitOne s (P.clockPlate f s X)
private lemma algScaleT {α:Type*} [Semiring α][Algebra ℂ α][Star α](B':Hilbert)(U:α→⋆ₐ[ℂ] B'.Op)(x:α)(a:ℂ): U (a•x)=a• U x:= map_smul U a x
lemma class_subscale (x:P.Spectrum0 j)(a:ℂ)(u:P.Physical j):(P.colorSpace j x) (a•u)= a•P.colorSpace j x u:= algScaleT (P.ColorHil j x) (P.colorSpace j x) u a
private lemma algPlusT {α:Type*} [Semiring α][Algebra ℂ α][Star α](V:Hilbert)(U:α→⋆ₐ[ℂ] V.Op)(x y:α): U (x+y)=U x+U y:= map_add U x y
lemma class_subplus (x:P.Spectrum0 j)(u v:P.Physical j):(P.colorSpace j x) (u+v)= P.colorSpace j x u+P.colorSpace j x v:= algPlusT (P.ColorHil j x) (P.colorSpace j x) u v
include h
lemma isGreen : P.voxTest j s (G s).val∈ enclave W:= P.clock_colors (P.clockPlate f s X)
noncomputable abbrev headFirst (s:ℕ):P.Physical j:=P.door j s (P.longtruck w f s) (κ! s) (P.deskCard j X w h s) (P.isGreen j X w h)
noncomputable abbrev deskColor (s:ℕ):(H₀).Op:= (P.colorSpace j χ) (P.headFirst j X w h s)
local notation "◆" s:max=> P.deskColor j X w h x s
local notation "✓" Ix:max=> inner ℂ ω (Ix ω)
noncomputable abbrev spotDuty (s:ℕ):= (◆ s)- (✓ (◆ s)) • (Η).E (whenly (timeMesh P.par) f w)
local notation "◈" s:max=> P.spotDuty j X w h x s
lemma textileL : ✓ (◆ s)=P.singleState 3 s x (P.visitOne s (P.clockPlate f s X)):=by
 unfold deskColor headFirst; rw [P.attended j _ s (κ! s),P.view_scalar, P.single_agrees]; rfl
section comparison
variable (p:f ≤ s)(q:s ≤ v)
lemma wind_le (b:ℂ): ‖b • (◈ v) - (◈ s)‖ ≤ 2* ‖b • (B v) - B s‖:=by
 let t:= b • (◆ v) - ◆ s; let Q':= (Η).E (whenly (timeMesh P.par) f w); let τ:=b • P.headFirst j X w h v-P.headFirst j X w h s
 have hv:t=Φ τ:=by unfold t τ; rw [map_sub Φ, P.class_subscale j χ]
 have hu:‖t‖≤ ‖b • (B v)-B s‖:=by rw [hv]; exact NonUnitalStarAlgHom.norm_apply_le Φ τ
 have he: ‖✓ t‖ ≤ ‖t‖:= by apply le_trans (norm_inner_le_norm ..); rw [P.norms_color j χ,one_mul]; simpa only [P.norms_color,mul_one] using (t.le_opNorm ω)
 have hy:‖ (✓ t) • Q'‖ ≤ ‖t‖:=by rw [norm_smul]; exact (mul_le_mul he ((Η).shrinks _) (norm_nonneg _) (norm_nonneg _)).trans (mul_one _|>.le)
 have hx:b • (◈ v) - (◈ s) = t - (✓ t) • Q':=by unfold spotDuty t; simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply, inner_sub_right,inner_smul_right]; unfold Q'; module
 rw [hx]; exact (norm_sub_le ..).trans (by linarith only [hy,hu])
lemma solo_frame (s:ℕ): ‖◈ s‖ ≤ 2* ‖B s‖:=by
 have hv: ‖◆ s‖ ≤ ‖B s‖:= NonUnitalStarAlgHom.norm_apply_le Φ (P.headFirst j X w h s)
 have he: ‖(✓ (◆ s))‖ ≤ ‖◆ s‖:= by apply le_trans (norm_inner_le_norm ..); rw [P.norms_color j χ,one_mul]; simpa only [P.norms_color,mul_one] using ((◆ s).le_opNorm ω)
 let T:=(Η).E K!; have hp: ‖(✓ (◆ s)) • T‖ ≤ ‖◆ s‖:=by rw [norm_smul]; exact (mul_le_mul he ((Η).shrinks _) (norm_nonneg _) (norm_nonneg _)).trans (mul_one _|>.le)
 exact (norm_sub_le (◆ s) ((✓ (◆ s)) • T)).trans (by linarith only [hv,hp])
include p
lemma clock_pin : whenly (timeMesh P.par) s (P.longtruck w f s) = K! := by
 exact matchR Λw f s w p
lemma centBalances (F:P.Card j s (£ s))(hF:υ s F.val∈enclave W)
 (tF: P.voxTest j s F.val=P.centeredQ x s (P.clockPlate f s X)) : Φ (P.door j s (£ s) (κ! s) F hF) =(◈ s):=by
 let m:=£ s; let V:=P.deskCard j X w h s
 let A:= P.door j s m (κ! s) F hF; let Z₁:= P.door j s m (κ! s) V (P.isGreen j X w h); let X':=(✓ (◆ s))
 let V':= SlabMark.identity P.run P.large s j false m
 let hU: υ s V'.val ∈ enclave W:= (enclave W).one_mem
 let U:=P.door j s m (κ! s) V' hU
 have hp:P.voxTest j s F.val=P.voxTest j s V.val-X' • (1:P.Test):=by unfold X'; rw [P.textileL,tF]; rfl
 have he:F.val.val= -X' • V'.val.val + V.val.val :=by
    have h0:= congrArg Subtype.val hp; change F.val.val = V.val.val-X' • V'.val.val at h0; rw [h0]; module
 have hy:A= -X' • U+ Z₁:=Subtype.ext (Subtype.ext (box_linear P j s m (κ! s) V' V F _ he))
 change Φ A=_
 have he: (Η).E K! =Φ U:=by -- parse
    rw [← P.clock_pin j X w h p]; exact P.tubePulse j χ s _ (κ! s)
 have hX: Φ A = -X' • (Φ U)+ Φ Z₁:= (congrArg (⇑Φ) hy).trans ((P.class_subplus j χ (-X' • U) Z₁).trans (congrArg (· + Φ Z₁) (P.class_subscale j χ (-X') U)))
 refine hX.trans (show -X' • (Φ U)+ Φ Z₁ = Φ Z₁ - X' • (Η).E K! from ?_)
 exact (show -X' • Φ U+ Φ Z₁=Φ Z₁-X' • Φ U from (by module)).trans (congrArg (fun y:(P.ColorHil j χ).Op=> Φ Z₁-X' • y) he.symm)
-- centered stamp itself
variable (t:P.Apron)(y:Cover)(g:t.s ≤ s)(u:P.chartAll y (t.full P s)=P.centeredQ x s (P.clockPlate f s X))
local notation "κ"=> P.vtile s y
local notation "o"=>P.laysM (P.vtile s y)
include g u
lemma centPin (h':0 < Apron.time_panel P j (o) t)(u':Apron.time_edge P j (o) t < (K!:ℝ)):P.raze j χ t 0 (K!:ℝ) (κ) = (◈ s):=by
 let m:= P.longtruck w f s; let V:=P.deskCard j X w h s
 rw [← P.clock_pin j X w h p] at u' ⊢ -- also h RHS `◈` not unfolded
 obtain ⟨F,hF,tF,xF⟩:= P.shelf_door j χ t s m y g (κ! s) h' u'
 exact xF.trans (P.centBalances j X w h x p F hF (tF.trans u))
end comparison
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
