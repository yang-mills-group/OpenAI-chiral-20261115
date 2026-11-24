import YM.SU5.SatinWard.Resolution.Gabbro
import YM.SU5.SatinWard.Resolution.Marconi
import YM.SU5.SatinWard.Resolution.Rachis
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
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
namespace Internal

open Preparation.Tabletop Harmonic CasaF Signboard Ceremo LitCurrent LitCurrent.Chamber
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
local notation "σ" v:max=> P.macroStep v
local notation "ζ"=> P.jump128
open Motet SoulField Verdance Mezzo SatinWard.Installment
namespace Imperial

/- Lining incidence, with E estimator small-step. Keep exactly compressed-prices
 in this stage. (Adjoint tests have separate qualification through actual lease.) -/
variable {D:ℕ→ℕ}(η:Type)[Fintype η]{v j f0:ℕ}{a b H A φ:ℝ} (q:Cover)(p:ResidualPermit q) (M:P.par.R.L.val%16=1)(k:Axis)(t:Fin 8)
local notation "ρ" => P.par.block.val
local notation "κ" => ζ -- macro
local notation "LH"=> liner k t
local notation "Yt" b:max=> castY t b
local notation "So" t:max=> CLine q k t
local notation "Y" v:max=> home P (So t) v
local notation "Zt" b:max v:max=> home P (So (Yt b)) v
local notation "Pt" t:max=> lifeC q p k t
local notation "p*t"=> lifeC q p k t -- tokens
variable (U:Soul)(vo:Axis)
local notation "VBar" i:max z:max => JpriceApp P (So i) M (Pt i) z vo v
local notation "Top" b:max=> (VBar (Yt b) U)
local notation "UV" z:max=> cloakF P M (Pt t) (substar (v:=v) (j:=ρ) P vo k z) v
local notation "Εw" k:max => Motet.dewy P.par k
local notation "Ε" k:max=> (↑(Εw k):ℂ)
local notation "UR" b:max=> (P.chartAll (liner k t b) (VBar (Yt b) U).F)
variable {s:ℕ} (i:Axis)(x:P.Spectrum0 i)(hp:f0 ≤ v){l r:ℝ}
local notation "tₖ" i:max u:max => P.tock v ((u:Cover) i)
local notation "Q₀"=> home P (So t) v i
local notation "𝔤"=> P.Grips i x v (-(l-Q₀)) (r+Q₀)
local notation "ℛ"=>P.charter i x
local notation "Σ★"=> P.locate i x
local notation "Hσ" A:max => (fun l r=> P.rawBase i x A (l-home P (So t) v i) (r+home P (So t) v i))
local notation "𝒵" b:max => galley P i x v (liner k t b) (Hσ (Top b)) l r
local notation "δ₀"=>moonClock P s
variable {o: Cover}(uv:StretchClock P P.par.block.val s v (CLine q k t) o)
variable (W:HeartClock P f0 H A a b φ P.par.block.val M D η)(ht7:f0 ≤ s)
variable (hl:2*moonClock P s ≤ l)(hr:2*moonClock P s≤ r)
variable (K:P.NightCop)(lι:Wage3){U':Soul}{D':ℕ→ℕ} (Hχ: Velas P η A H f0 v P.par.block.val vo k lι U D')(Hd:Tendsto D' atTop atTop)
-- MotionLap on those projected transfers
local notation "Kℓ" => ShapeLab.leg lι
local notation "Φv" u:max=> annoFace P i x v (Y v) (VBar t u)
local notation "Φℓ" b:max=> Beam P q k t v b
local notation "φ🌸" z:max=> (fun (t:Fin 8)=> annoFace P i x v (home P (So t) v) (VBar t z))
local notation "γb" b:max z:max=> bead P q k t i x v (φ🌸 z) l r b
local notation "μ" => sprintCost P.par.R.L
local notation "Ψε" b:max => bondMonth P η A s b
local instance (priority:=high)(P:Spine)(i:Axis)(x:P.Spectrum0 i) : NormedSpace ℝ (P.ManyF i x).Op:= opRn (P.ManyF i x)
variable (c:s<v) (pT:Tendsto D atTop atTop)(e:Melodic P η A f0 D) (R:Resonant P η A H f0 P.par.block.val)[Nonempty η] {a₁ b₁ φ' :ℝ}(Wa:HeartClock P f0 H A a₁ b₁ φ' P.jump128 M D η)
local notation "Z₀" i:max=> trueKey P pT e K i
local notation "Ψ𝓡" b:max=> (priceX P pT e vo (So b) M K (Pt b) i x)
local notation "Φ" z:max => fun b:Fin 8=> priceX P pT e vo (So b) M K (lifeC q p k b) i x z
local notation "βQ" b:max z:max=> bead P q k t i x v (Φ z) l r b
local notation "δη" z:max=> spindle P q k t i x v (Φ z) l r -- clock frontier
open SatinWard
open OS.Semigroup OS.Semigroup.Marble PSE MarbleFace MezzoBill Velas OS.Semigroup.BasinWake Treaty Choreographer OS.Semigroup.Gear
variable {C' d₀:ℝ} {t' β Wp} {R':P.Register} (T₁:CouncilGrant P R' d₀ C' t' D Wp β) (H': PublicKernel P D Wp) (a₀:Axis)(x₁:P.Spectrum0 a₀)(J:P.Ellis a₀ x₁)
local notation "Lx"=> P.par.R.L
variable (Lh:64≤ P.par.R.L.val) (Ra: Resonant P η A H f0 P.jump128)
local notation "Zc" τ:max=> (poleLens P η K pT e R τ vo k)
include W K T₁ H' J Wa pT e Lh R Ra
namespace Lighthouse -- open Imperial parent
local notation "WAW"=> P.ManyF a₀ (P.advocate a₀ x₁ a₀)
local notation "Fx" t0:max z:max=> (priceX P pT e vo (CLine q k t0) M K (Pt t0) a₀ (P.advocate a₀ x₁ a₀) z)
include p in
lemma waves : Tendsto (fun v:ℕ=> (Zc v) U) atTop (𝓝 ((2:ℝ) • U)):=by
 let x0:= P.advocate a₀ x₁ a₀; obtain ⟨v,D0,h,D1⟩:= Rachis.pledge P M K a₀ W.tally T₁ H' a₀ x₁ J W e vo (CLine q k) (fun i=>lifeC q p k i) Lh; let d:= 10*moonClock P (corridorHeight P v); have hd:0<d:=mul_pos (by norm_num) (clockP ..)
 let I:= Fin 8; let F(t:Fin 8) := contoBill P pT e vo _ M K (lifeC q p k t) a₀ x0 W hd hd; let T:Soul→ₗ[ℝ] (WAW).Op:=∑ i:Fin 8,F i; let v'(v:ℕ):= (Zc v) U; let g t:= fun v:ℕ=> F t (v' v); let a:=(2:ℝ) • U; have he(i:Fin 8): Tendsto (g i) atTop (𝓝 (F (i+1) U+F (i-1) U)):= av_plate P η q p M k i U vo a₀ x0 W K pT e R Wa T₁ H' a₀ x₁ J Lh Ra hd hd
 have hM(z:Soul): T z=∑ i:Fin 8,F i z:= LinearMap.sum_apply ..; have hA:T a=∑ i:Fin 8, (F (i+1) U+F (i-1) U):= by rw [hM]; unfold a; simp_rw [map_smul]; rw [← smul_sum]; exact (GarnetAct.circle_sum _).symm
 have hx: Tendsto (fun n=>T (v' n)) atTop (𝓝 (T a)):=by simp_rw [hA,hM]; exact tendsto_finsetSum univ (fun i _=>he i)
 let hx0 := (tendsto_iff_norm_sub_tendsto_zero.mp hx).const_mul D0; rw [mul_zero] at hx0; refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_; apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) _ hx0; filter_upwards with n; change ‖v' n-a‖≤ _; rw [←map_sub T,hM]; exact D1 _ -- T.map_sub may work? use map_sub.
variable (p':0<l)(q':0<r)
local notation "E◇" t:max=> priceX P pT e vo (CLine q k t) M K (Pt t) i x U l r
include p' q'
theorem lap : (Ψ𝓡 (t+1)) U l r+(Ψ𝓡 (t-1)) U l r=(2:ℝ) • (E◇ t):=by
 let Y1:=contoBill P pT e vo (CLine q k t) M K (Pt t) i x W p' q'; let S:=Y1.toContinuousLinearMap; let g:=(waves P η q p M k U vo W K pT e R Wa T₁ H' a₀ x₁ J Lh Ra); let v0 := (S.continuous.tendsto ((2:ℝ) • U)).comp g; have h:=tendsto_nhds_unique (av_plate P η q p M k t U vo i x W K pT e R Wa T₁ H' a₀ x₁ J Lh Ra p' q') (show Tendsto (fun n=> (Ψ𝓡 t) ((Zc n) U) l r) atTop (𝓝 (S ((2:ℝ) • U))) from v0); exact h.trans (map_smul S (2:ℝ) U)
theorem pareil (s: Fin 8): (E◇ t)=(E◇ s):=by
 let F(t:Fin 8):= E◇ t; let E(i₀:Fin 8):= GarnetAct.spiralDay F (fun t'=> lap P η q p M k t' U vo i x W K pT e R Wa T₁ H' a₀ x₁ J Lh Ra p' q') i₀; exact (E t).trans (E s).symm
lemma transverse : priceX P pT e vo q M K p i x U l r=E◇ t:=by
 obtain ⟨a,e0⟩:= named q p k; let L(γ:credential):=priceX P pT e vo γ.val M K γ.property i x U l r; -- `congr` issue: comparing a to q cost might Whnf overflow because proof fields. Use explicit discharges. 
 have h: (E◇ a)=priceX P pT e vo q M K p i x U l r:=by
    change L ⟨CLine q k a,lifeC q p k a⟩=L ⟨q,p⟩; rw [show (⟨CLine q k a,lifeC q p k a⟩:credential)=⟨q,p⟩ from (Subtype.ext e0)]
 exact h.symm.trans (pareil P η q p M k a U vo i x W K pT e R Wa T₁ H' a₀ x₁ J Lh Ra p' q' t)
lemma aliasJ (u:credential): priceX P pT e vo q M K p i x U l r=priceX P pT e vo u.val M K u.2 i x U l r:= linkage (fun u:credential=>priceX P pT e vo u.val M K u.2 i x U l r) (fun u k t=> transverse P η _ u.2 M k t U vo i x W K pT e R Wa T₁ H' a₀ x₁ J Lh Ra p' q') ⟨q,p⟩ u
#print axioms aliasJ
end Lighthouse
end Imperial
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
