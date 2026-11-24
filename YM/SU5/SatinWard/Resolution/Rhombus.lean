import YM.SU5.SatinWard.Resolution.Cubist
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
open SatinWard
local notation "R"=> Option Tilted.Ramp
local notation "T"=> P.calibration
local notation "ι₀"=>Wage4
local notation "L"=> P.par.R.L
local notation "K"=> P.run
local notation "V"=> P.large
variable (X:R)
variable {s v g w:ℕ}(p:Cover)(e:Almanac P s w p)(h:s≤g)
local notation "Q" => P.calibration.ℓ
variable {f0:ℕ} {Z:ℕ→ℕ} {η:Type}[Fintype η]{C H A:ℝ}
variable (pZ:Tendsto Z atTop atTop)(W:Calendrical P C H A f0 η Z){Wq:Bool→ Coords Wage4} {Uq:ℕ→ Bool→ Coords Wage4} {F:ℕ→ℕ}(WX:CriticalClock P C H A g f0 η Wq F Z Uq) (b: Bool)
include pZ W WX h
local notation "Yt" => (sprintCost L)
local notation "k▶" i:max => P.engine ((Z ∘F) i)
local notation "j▶" i:max => P.nomadic ((Z ∘ F) i)
omit W WX pZ h
open Worth Pays BProof Aria Casting MacroGrid
open Selected
local notation "ζ"=>P.sidesPerTick
-- Annotated center. translate with the REAL home clock (not simplified half). Pose Hc later.
variable (M:P.par.R.L.val %16 =1) (k:P.NightCop) (j:Axis)(x:P.Spectrum0 j)
variable {a: Cover} (qa:ResidualPermit a) (y:Coords Wage4) (q:payable P v 2) {u d:ℝ}
variable (f:ℕ)(g₀:f ≤ v)
local notation "τ" i:max=> P.macroStep i
local notation "W₀" => choirWidth P
variable (ρ:Piano P f0 C H A η Z)
local notation "θ"=>psIndex P ρ
local notation "δ"=>psScale P ρ
local notation "μ"=>sprintCost P.par.R.L
local notation "ℓ" i:max=> moonClock P i
local notation "β₁" i:max=>4*ageBudget P η A C H i
local notation "β₄" i:max=> (β₁ s)*(μ^(i-s))⁻¹
local notation "Φ"=> complect P M j x qa ρ
local notation "𝒢" => rawSolo P M j x qa
local notation "ξ"=> P.physicalEnergy j x
local notation "ν"=> P.seasons j x
-- convergence lemma
noncomputable def rawPSE (l r:ℝ): (P.ColorHil j x).Op := limUnder atTop (fun i=> Φ i l r)
local notation "℘"=> rawPSE P M j x qa ρ
include ρ k qa pZ
-- show f0 prices eventual scale limiting.
omit k qa pZ in
lemma small_clock : Tendsto (moonClock P) atTop (𝓝 0):=by
 have ht:= ρ.loans f0 le_rfl; let L':= fun k : ℕ=> (moonClock P f0)* (1/2:ℝ)^((k-f0):ℕ)
 have hp:Tendsto L' atTop (𝓝 0):=by simpa only [L',Function.comp_apply,mul_zero] using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1/2:ℝ)<1)).comp (show Tendsto (fun k:ℕ=> k-f0) atTop atTop from tendsto_atTop.2 fun i=> (eventually_ge_atTop (i+f0)).mono fun _ _=>by omega)).const_mul (moonClock P f0)
 exact squeeze_zero' (Eventually.of_forall fun i=>(clockP P i).le) ((eventually_ge_atTop f0).mono fun i h=>(ht i h).trans_eq (mul_comm ..)) hp
lemma psePresence (hu:0<u)(hd:0<d): Tendsto (fun i=> Φ i u d) atTop (𝓝 (℘ u d)):=by
 obtain ⟨i,e,w,z⟩:= ((eventually_ge_atTop f0).and ((small_clock P ρ).eventually (inter_mem (gt_mem_nhds hu) (gt_mem_nhds hd)))).exists; exact (brush P pZ M k j x qa ρ (s:=i) (u:=u) (d:=d) e (le_of_lt w) (le_of_lt z) (Nat.lt_succ_self _)).1 -- `Filter.inter` (Member intersection func vs indicator) adjust
variable (q':f0 ≤ s) (p':s < v) (gu:moonClock P s ≤ u) (gd:moonClock P s ≤ d)
include q' p' gu gd
-- rename arguments `p` for adj.Linear
lemma psLimit (q:payable P v 2)(f:f0 ≤ v): ‖(↑(δ v):ℂ)⁻¹ • ℘ u d-𝒢 pseV q f0 f u d‖ ≤2*(β₄ v):=by
 let A':= (↑(δ v):ℂ); have hv:A' ≠0:=Complex.ofReal_ne_zero.mpr (scale_psX P ρ v); have he:= (brush P pZ M k j x qa ρ q' gu gd p').2; rw [dist_comm,dist_eq_norm] at he
 rw [show (𝒢 pseV q f0 f u d)=A'⁻¹ • Φ v u d from by rw [cast_chime P M j x qa ρ f,inv_smul_smul₀ hv]]; unfold A'; rw [←smul_sub,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs]; refine (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (abs_nonneg _))).trans (le_of_eq ?_); generalize hh: |δ v| = r; have hr: r ≠0:=by rw [←hh]; exact (abs_pos.mpr (scale_psX P ρ v)).ne'
 rw [mul_comm 2 r, mul_assoc r,←mul_assoc,inv_mul_cancel₀ hr,one_mul]
omit gu gd q' p'
local notation "Dᵣ" i:max=> (choirWidth P:ℝ)*P.macroStep i
omit qa k pZ in
lemma windowLaw (h:f0≤ v): Dᵣ v+ τ v ≤ ℓ v:= by
 have h':0 ≤ Dᵣ v:=mul_nonneg (by positivity) (P.macroStep_pos v).le; linarith [ρ.pays v h,P.macroStep_pos v]
omit k pZ in
lemma pse_cap (h:f0≤v) : (ξ).Credits (ℓ v) (Φ v):=by
 intro a' b c d v₁ v₂ t w; have hc:=windowLaw P ρ h; have u:=abs_le.mp (home_room P qa v j); rw [cast_chime P M j x qa ρ h,cast_chime P M j x qa ρ h,raw_cap (u:=a') (d:=b) P M j x qa pseV _ _ _ (by linarith) (by linarith) t w,←map_smul]; rfl
lemma pse_lag : (ξ).Credits 0 ℘:= OS.Semigroup.Credits.earned (small_clock P ρ) ((eventually_ge_atTop f0).mono (fun i v=>pse_cap P M j x qa ρ v)) fun l u r v=> BSOT.fromNorm (psePresence P pZ M k j x qa ρ u v)
-- transfer to compression all lags. norm on real spacetime anchors.
local notation "ℛ"=> P.locate j x
local notation "κ"=> P.reprise j x
local notation "λ₀" => home P a f0
omit k pZ
noncomputable def pricedPSE (l r:ℝ): (P.ManyF j x).Op := ℛ (-home P a f0) (κ (℘ l r))
local notation "θ₀"=>pricedPSE P M j x qa ρ
noncomputable def annoFace (v:ℕ) (p:Vantage) (X:P.Apron) (l r:ℝ): (P.ManyF j x).Op:= ℛ (-p) (P.base j x X (l-p j) (r+p j)) -- `v` unused purposeful
local notation "Ξ" v:max=> annoFace P j x v (home P a v)
lemma pricing_p (v:ℕ)(z:Coords Wage4)(u:f0≤v)(q:payable P v 2)(a₁ b:ℝ):
 ℛ (-home P a f0) (κ (𝒢 z q f0 u a₁ b))=(Ξ v) (soloV P v q a qa z) a₁ b:=by rw [rawTicket, P.reprise_charter,P.locate_sum,P.reprise_rawBase,seated, show -(home P a f0)+(home P a f0-home P a v)=- home P a v from by abel]; rfl
include q' p' gu gd k pZ
lemma pricedRankLimit (q:payable P v 2): ‖(↑(δ v):ℂ)⁻¹ • θ₀ u d- (Ξ v) (soloV P v q a qa pseV) u d‖ ≤ 2*(β₄ v):=by
 have h:f0≤v:=q'.trans p'.le
 rw [←pricing_p P M j x qa ρ v pseV h q]; unfold pricedPSE; rw [←P.locate_smul,←P.reprise_smul, ← P.locate_sub, P.locate_cost,←P.reprise_sub]; exact (P.reprise_pay ..).trans (psLimit P pZ M k j x qa ρ q' p' gu gd q h)
omit q' p' gu gd
lemma priced_lag : (ν).Credits 0 θ₀:= by intro u v w z a' b h t; have hp:(℘ w z)=(ξ).sand (℘ u v) (w-u) (z-v):= pse_lag P pZ M k j x qa ρ a' b h t; unfold pricedPSE; rw [hp,P.reprise_sand,P.locate_sand]
#print axioms pricedRankLimit
#print axioms priced_lag
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
