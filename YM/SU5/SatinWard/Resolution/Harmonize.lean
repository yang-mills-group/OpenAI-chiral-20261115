import YM.SU5.SatinWard.Resolution.Imperial
import YM.SU5.SatinWard.Resolution.GlowX
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
lemma commodities : (UV U).F= Ε v • (UR true+UR false):=by
 let w:= tauprint P M (lifeC q p k t); have e(b:Bool): UR b= chapterFoot P (letterShape (J:=P.calibration) (Λ:=P.par) vo v U) (w+pmZ ρ k b):= by
    unfold w; rw [balance P q p k t b M]; exact calendar_moves P _ _ _ -- order
 rw [e,e]; rfl
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
include uv
lemma hor_6 : 6*P.macroStep v ≤ moonClock P s :=by linarith only [restTick P uv.ph,uv.enough,P.macroStep_pos v]
include hl hr
lemma echoS : (Hσ (UV U)) l r= Ε v • (𝒵 true + 𝒵 false):=by
 have ht:=abs_le.mp (home_room P (Pt t) v i); let d:=moonClock P s; have Θ:= hor_6 P q k t uv
 have h₁ :𝔤 (UV U).F ((Hσ (UV U)) l r):=by
    have hz: (UV U).realWidth P i≤ d:= by rw [real_cloak]; linarith only [clockP P s,uv.fit (show 2*ρ≤rentWidth P ρ v from (by unfold rentWidth; omega))]
    exact P.grasp_fixed i x (UV U) (a:=l-Q₀) (by linarith only [Θ,hz,hl,P.macroStep_pos v, ht.2]) (b:=r+Q₀) (by linarith only [Θ,hz,hr,P.macroStep_pos v, ht.1])
 have h₂(b:Bool) : 𝔤 (UR b) (𝒵 b):=by
    have hq:(VBar (Yt b) U).realWidth P i≤ d:= by unfold JpriceApp; rw [real_cloak]; linarith only [clockP P s,uv.fit (Nat.zero_le _)]
    have te:=abs_le.mp (geo_line P k t b v i); refine gripsH (l:=l) (r:=r) P i x (So t) (Top b) (liner k t b) (h:=rfl) ?_ ?_
    all_goals linarith only [te.1,te.2,Θ,hq,hl,hr,ht.2,ht.1,P.macroStep_pos v]
 apply h₁.unique; rw [commodities P q p M k t U vo]; exact ((h₂ true).add (h₂ false)).smul _
omit uv hl hr
noncomputable abbrev Beam (v:ℕ) (b:Bool): Vantage:= -(home P (So t) v)+ (P.laysM (P.vtile v (liner k t b)))+ home P (CLine q k (castY t b)) v
local notation "Φℓ" b:max=> Beam P q k t v b
variable (bK:Bool)
local notation "vxi"=> Beam P q k t v bK i
lemma Beam_meter (j:Axis) : (Φℓ bK) j= P.tock v (liner k t bK j)+ home P (So (castY t bK)) v j-home P (So t) v j:=by change -(home P (So t) v j)+P.tock v (liner k t bK j) + home P (So (castY t bK)) v j=_; ring
include p in
lemma Beam_paid : |(Φℓ bK) i| ≤ 3*P.macroStep v := by rw [Beam_meter]; have t1:=abs_le.mp (home_room P (lifeC q p k (castY t bK)) v i); have t2:=abs_le.mp (home_room P (lifeC q p k t) v i); have t3:=abs_le.mp (geo_line P k t bK v i); rw [abs_le]; constructor<;> linarith only [t1,t2,t3]

local notation "GΘ" b:max=> (Top b)
lemma Bea (l r:ℝ): P.locate i x (-(home P (CLine q k t) v)) (P.reprise i x (galley P i x v (liner k t bK) (Hσ (Top bK)) l r))=
 P.locate i x (Beam P q k t v bK) (annoFace P i x v (Zt bK v) (Top bK) (l+(Φℓ bK) i) (r-(Φℓ bK) i)):=by
 unfold galley annoFace; rw [P.reprise_charter,P.locate_sum,P.locate_sum,Beam_meter]; dsimp only; let z:= tₖ i (liner k t bK); let V:= (Zt bK v) i; rw [show l + (z + V-Q₀)-V=l+z-Q₀ by abel, show r-(z+V-Q₀)+V=r-z+Q₀ from by abel,P.reprise_rawBase]; unfold Beam; rw [add_neg_cancel_right] -- might rewrite `Beam_meter` only first occurrence? rw [Beam_meter] all
noncomputable abbrev bead (v:ℕ)(A:Fin 8→ P.LagOp i x)(l r:ℝ)(b:Bool) := P.locate i x (Beam P q k t v b) ((A (Yt b)) (l+Beam P q k t v b i) (r-Beam P q k t v b i))
local notation "φ🌸" z:max=> (fun (t:Fin 8)=> annoFace P i x v (home P (So t) v) (VBar t z))
local notation "γb" b:max z:max=> bead P q k t i x v (φ🌸 z) l r b
include uv hl hr
lemma prism : annoFace P i x v (Y v) (UV U) l r= Ε v • (γb true U+γb false U):=by
 let F(b:Bool):= 𝒵 b -- local
 have w(b:Bool): P.locate i x (-(Y v)) (P.reprise i x (F b))= γb b U:= by exact Bea P q p M k t U vo i x b l r
 rw [←w,←w]; unfold annoFace; rw [←P.reprise_rawBase, show P.rawBase .. =_ from echoS P q p M k t U vo i x uv hl hr, P.reprise_smul,P.reprise_add,P.locate_smul,P.locate_add] -- goal w. annoFace hσ
omit uv
variable (K:P.NightCop)(lι:Wage3){U':Soul}{D':ℕ→ℕ} (Hχ: Velas P η A H f0 v P.par.block.val vo k lι U D')(Hd:Tendsto D' atTop atTop)
-- MotionLap on those projected transfers
local notation "Kℓ" => ShapeLab.leg lι
local notation "Φv" u:max=> annoFace P i x v (Y v) (VBar t u)
include W Hχ Hd ht7 K in
lemma panorama (w:s<v) : ‖Ε v • (γb true Kℓ+γb false Kℓ)- annoFace P i x v (Y v) (VBar t U) l r‖ ≤ θx P η s v A H vo:=by
 obtain ⟨o,h⟩:= W.tally.poses s ht7 (CLine q k t) (Pt t); let uv:= W.stamps s v _ o ht7 w.le (Pt t) h; obtain ⟨x',z⟩:= placement_m P M s v o
 let u:=clockP P s; let h':=ht7.trans w.le; rw [←prism P q p M k t Kℓ vo i x uv hl hr]
 let tβ:= clock_x P o x' z Hd K i w ht7 W.living.1 W.living.2.1 η _ M (lifeC q p k t) x uv (by linarith only [u,hl]:moonClock P s≤l) (by linarith only [u,hr]:moonClock P s ≤ r) h' vo k lι Hχ (healthy P M W ht7); rw [←encodeFront P i _ M x h' _ l r rfl,←encodeFront P i _ M x h' _ l r rfl,←P.locate_sub,P.locate_cost, ←P.reprise_sub]; exact (P.reprise_pay ..).trans tβ
#print axioms Beam_meter
#print axioms panorama
end Imperial
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
