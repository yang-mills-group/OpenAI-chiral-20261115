import GaugeFieldConstruction.GreenPriceNX
import GaugeFieldConstruction.AurexR
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 130000
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
open Papal FrameP Fock.Flux Gleam BProof.PricePort Gleam.Guide Gleam.clocks
open Lead Designs
variable (P:Spine){n:ℕ}(A B:BeaconNX n)(i:ℤ)
open RosterJ BoonsθJ XGarden XGarden.MastTin XGarden.MastTin.ArtCart
variable (m:ℕ) {Q: Py.Rate.LocalLimit.Badge}{t:ℕ}{u: TintDemand}(H: LicensedHeight (tagged_B Q) t u P.par)
local notation "ξm"=> SportR P m
local notation "ρM"=> Richm_R P m
local notation "ζM"=> RootApR P
local notation "δπ"=> StallJ P ∘ RootApR P
local notation "ΓΧ"=> ScaleFlagNX P
local notation "θ"=> ruler P.calibration.B
noncomputable def StegaClockNX (P:Spine)(m i:ℕ):ℤ:= (GrowJ P i (SportR P m i):ℤ)*(LfloorR P (deltaR P i/2) i+1)
local notation "Δm" => StegaClockNX P m
lemma pullRootApNX (j:ℕ): P.stampPin (SportR P m j) (StegaClockNX P m j)=(RootApR P j).val:=HeightGlove P j (SportR P m j) (SportR.hop ..) _ -- tune
lemma sovereignPNX (P:Spine)(m j:ℕ):0<StegaClockNX P m j:=by
 apply lt_of_not_ge; intro x
 have h:=(minted_le P (SportR P m j) _ _).2 x
 rw [show _=_ from pullRootApNX P m j] at h -- tune
 have he:0 < StallJ P (RootApR P j):=(RootApR P j).property
 rw[show (↑(P.stampPin _ 0):ℝ)=0 from ?h] at h
 exact he.not_ge h
 case h=> unfold stampPin; rw [notch_zero]; rfl
lemma ArkSlimNX : Tendsto (fun i=> (Richm_R P m i)⁻¹ * ↑(ruler P.calibration.B* (Δm i):ℤ)) atTop (𝓝 (1/2)):=by
 apply (RootAling P).congr; intro i
 let M:= P.mellow (ξm i)
 have he: 0<M:=P.mellow_good _
 change StallJ P _/deltaR P i=_
 unfold StallJ; rw [← pullRootApNX P m i,P.mellow_firm,← Richm_peck P]; field_simp; rw [mul_div_cancel_left₀ _ (P.mellow_good _).ne']; rfl -- tune
abbrev ProngNX (P:Spine)(A:BeaconNX n)(m i:ℕ)(σ τ:PermWallJ P):P.Slabs 3:= costΞJ P 3 0 (SportR P m i) σ τ (P.SunPlateNX A m i)
lemma SunBayNX (j:ℕ): P.SunPlateNX A m j∈bay P.calibration A.1.patio true:=by
 unfold SunPlateNX CenterBudgetR; let S:= bay P.calibration A.1.patio true; exact S.sub_mem (S.smul_mem (P.useFootPNX A.1 A.2.1 A.2.2.1 A.2.2.2) _) (S.smul_mem S.one_mem _) -- tune order
private lemma qualifiedPadNX:∀ᶠ i in atTop,P.Marrow 3 (SportR P m i) (-StallJ P (ζM i)) (StallJ P (ζM i)) A.1.patio:=by
 let α:=RootApR P; let Z(i):= P.mellow (ξm i); let T:=δπ
 let U:= deltaR P
 have he:Tendsto (fun i=>T i/U i) atTop (𝓝 (1/2)):=RootAling P
 have hx(c:ℝ):∀ᶠ i in atTop, Z i*c ≤ T i:=by
    have ht:Tendsto (fun i=>Z i*c/U i) atTop (𝓝 0):=by
       refine (show Tendsto (fun i=> c/Richm_R P m i) atTop (𝓝 0) from tendsto_const_nhds.div_atTop (Richm_lit ..)).congr fun i=>?_ ; rw [show U i= Z i*Richm_R P m i from (Richm_peck P m i).symm]; field_simp [(show 0 < Z i from P.mellow_good _)]; rw[mul_div_cancel_right₀ _ (show Z i≠0 from (show 0 < Z i from P.mellow_good _).ne')]
    filter_upwards [ht.eventually_lt he (by norm_num)] with i p; exact (div_le_div_iff_of_pos_right (show 0<U i from deltaR_good ..)).1 p.le
 have hf(x:Cover):∀ᶠ i in atTop,-T i ≤ Z i*((x 3:ℝ)-P.calibration.ℓ) ∧ Z i*((x 3:ℝ)+P.calibration.ℓ) ≤ T i:=by
    let c:= (x 3:ℝ) - P.calibration.ℓ; apply Eventually.and _ (hx _); filter_upwards [hx (-c)] with i h; rw[mul_neg] at h; exact neg_le_of_neg_le h -- tune
 exact (eventually_all_finset A.1.patio).mpr (fun x _=> hf x)
abbrev withPaceNX (P:Spine)(m i:ℕ):ℕ:= (2* StegaClockNX P m i).toNat
lemma tickP_NX (j:ℕ):(-Δm j+(P.withPaceNX m j:ℤ))=Δm j:= by unfold withPaceNX; rw [Int.toNat_of_nonneg (Int.mul_nonneg (by decide) ((sovereignPNX P m j).le))]; ring
lemma Learned_1NX : ∀ᶠ i in atTop, let j:= P.withPaceNX m i; let F:=P.shifts 3 (Δm i) (P.SunPlateNX A m i)
 P.BEntry 3 j F∧ P.ProngNX A m i (ζM i) (ζM i)= P.HabBox 3 (SportR P m i) j F:=by
 filter_upwards[P.qualifiedPadNX A m] with i h j F
 let a:=Δm i; have hp: (-a+(j:ℤ))=a:= tickP_NX ..
 let n:=SportR P m i; let X:=ζM i; have hu:X.val=P.stampPin n a:= (P.pullRootApNX m i).symm
 have he:F=P.shifts 3 (- -a) (P.SunPlateNX A m i):=by rw[neg_neg]
 have hx:P.BEntry 3 j F:=by
    rw [he]; apply BEntry.mesh_frame (j:=3) (s:=n) (a:=-a) (w:=j) (P.SunBayNX A m i) (by have h:a>0:=sovereignPNX ..; omega)
    rw [hp,minted_neg,← hu]; exact h
 refine ⟨hx,?K⟩
 case K=>
   unfold ProngNX; refine ℓγHeard (P:=P) _ _ _ _ _ ?H
   case H=>
     have h0:(0:P.VMark) 3=0:=rfl
     unfold CallBoxJ; rw[h0,zero_add,zero_sub,hu, ← minted_neg, he]
     rw[he] at hx
     nth_rw 2 [←hp] -- risky occurrence in RHS Mark ... instead have exact
     exact Habitable.direct hx n -- tune
include H
lemma NobleΦNX : Tendsto (fun i=> inner ℂ (DotM_R P 3 (P.ProngNX A m i (ζM i) (ζM i))) (DotM_R P 3 (P.ProngNX B m i (ζM i) (ζM i)))) atTop (𝓝 (ArmΔScanNX A B)):=by
 refine (P.PadWinnerNX A B m _ (P.ArkSlimNX m) H).congr' ?_; filter_upwards[P.Learned_1NX A m,P.Learned_1NX B m] with i u v; exact (replica_L 3 _ u.1 v.1 u.2 v.2).symm
#print axioms NobleΦNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
