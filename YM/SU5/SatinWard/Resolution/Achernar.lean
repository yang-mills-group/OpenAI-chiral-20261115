import YM.SU5.SatinWard.Resolution.Diva
import YM.SU5.SatinWard.Resolution.Resin
import YM.SU5.SatinWard.Resolution.MaySong
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
local notation "Y"=> P.run
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
local notation "σ" v:max=> P.macroStep v
local notation "ζ"=> P.jump128
variable {D:ℕ→ℕ}(η:Type)[Fintype η]{v j f0:ℕ}{a b H A φ:ℝ} {Z:Visit→ Cover → Family P.calibration} {χ:Division}{d:PitchZ}
variable (E:Ceremo P η v P.jump128 f0 a b φ H A χ D Z d)(q:Cover)(p:ResidualPermit q) (M:P.par.R.L.val%16=1)
local notation "Ξ" u:max=> cloakF P M p (E.earnedZ P η u) v
local notation "Δ"=> cloakF P M p (logStarCore P η E) v
local notation "X" v:max=> hat P.par.R.L P.par.x v
local notation "Yw" v:max=> (hueW P.par.R.L (X v))
local notation "h★" v:max=> (↑(Yw v):ℂ)
local notation "h△" v:max=>(↑(qHull P.par.R.L (X v)):ℂ)
local notation "h❖" v:max=>(↑(jHull P.par.R.L (X v)):ℂ)
local notation "TΔ" i:max=> Ξ (some i)
open Motet SoulField Verdance Mezzo SatinWard.Installment
variable (U:Soul)(vo ti:Axis)
local notation "Vx" i:max z:max => JpriceApp P q M p z i v
local notation "UV" z:max=> cloakF P M p (roseDiv (v:=v) (j:=ζ) P z) v
local notation "Εw" k:max => Motet.dewy P.par k
local notation "Ε" k:max=> (↑(Εw k):ℂ)
local notation "UR" i:max b:max=> (P.chartAll (incMove i b) (Vx i U).F)
noncomputable abbrev currentBill (U:Soul):P.Test:=(UV U).F
lemma stocked_div : currentBill (v:=v) P q p M U= Ε v • (∑ j:Axis,(UR j true-UR j false)):=by
 let w:= tauprint P M p; have he(i:Axis)(b:Bool): UR i b= chapterFoot P (letterShape (J:=P.calibration) (Λ:=P.par) i v U) (w+pmZ ζ i b):=by
    change P.chartAll _ (chapterFoot P (letterShape (J:=P.calibration) (Λ:=P.par) i v U) w)=_; rw [calendar_moves,show ζ • (incMove i b)= pmZ ζ i b from ?_]; unfold incMove pmZ; cases b<;>simp
 apply Subtype.ext; change busker P v P.jump128 U w= Ε v • (((∑ j:Axis,(UR j true-UR j false)):P.Test):Family P.calibration); simp_rw [he]; unfold busker; rw [Complex.coe_smul]; simp only [Pi.smul_apply,Finset.sum_apply,Pi.sub_apply]; rfl
variable {s:ℕ}
variable (i:Axis)(x:P.Spectrum0 i)(hp:f0 ≤ v){l r:ℝ}
local notation "tₖ" i:max u:max => P.tock v ((u:Cover) i)
local notation "Q₀"=> home P q v i
local notation "𝔤"=> P.Grips i x v (-(l-Q₀)) (r+Q₀)
local notation "ℛ"=>P.charter i x
local notation "Hσ" A:max => (fun l r=> P.rawBase i x A (l-home P q v i) (r+home P q v i))
local notation "𝒵" j:max b:max => galley P i x v (incMove j b) (Hσ (Vx j U)) l r
local notation "δ₀"=>moonClock P s
variable {o: Cover}(uv:StretchClock P P.jump128 s v q o)
variable (W:HeartClock P f0 H A a b φ P.jump128 M D η)(ht7:f0 ≤ s)
variable (hl:2*moonClock P s ≤ l)(hr:2*moonClock P s≤ r)
include uv
include hl hr
-- keep clues α coherence at physical operator.
lemma awakeD : (Hσ (UV U)) l r= Ε v • (∑ j:Axis,(𝒵 j true-𝒵 j false)):=by
 have ht:=abs_le.mp (home_room P p v i); let d:=moonClock P s; let Θ:3*P.macroStep v≤ d:= hor_3 P q uv
 have h₁ :𝔤 (UV U).F ((Hσ (UV U)) l r):=by
    have hz: (UV U).realWidth P i≤ d:= by rw [real_cloak]; linarith only [clockP P s,uv.fit (show 2*P.jump128≤rentWidth P P.jump128 v from (by unfold rentWidth; omega))]
    exact P.grasp_fixed i x (UV U) (a:=l-Q₀) (by linarith only [Θ,hz,hl,P.macroStep_pos v, ht.2]) (b:=r+Q₀) (by linarith only [Θ,hz,hr,P.macroStep_pos v, ht.1])
 let h₂(ti:Axis)(b:Bool) : 𝔤 (UR ti b) (𝒵 ti b):=by
    have hq:(Vx ti U).realWidth P i≤ d:= by unfold JpriceApp; rw [real_cloak]; linarith only [clockP P s,uv.fit (Nat.zero_le _)]
    have t:=abs_le.mp (inc_wallet (v:=v) P i ti b); refine gripsH (l:=l) (r:=r) P i x q (Vx ti U) (incMove ti b) (h:=rfl) ?_ ?_ -- notation works? binders implicit terms all goals below
    all_goals first | rfl | linarith only [t.1,t.2,Θ,hq,hl,hr,ht.2,ht.1,P.macroStep_pos v]
 apply h₁.unique; change 𝔤 (currentBill (v:=v) P q p M U) _; rw [stocked_div]; apply Grips.smul; apply Grips.sum; intro j _; rw [sub_eq_add_neg (UR j true), sub_eq_add_neg (𝒵 j true),← neg_one_smul ℂ (UR j false),←neg_one_smul ℂ (𝒵 j false)]; exact (h₂ j true).add ((h₂ j false).smul _) -- `Vel.`
local notation "Txn" j:max z:max=> lined P M i x f0 q hp (Vx j z)
local notation "Hμ" j:max z:max=> charm P q M j p i x hp z
lemma coSpread : frontPrice P i q M p x hp (roseDiv (v:=v) (j:=ζ) P U) l r=Ε v • evdiv P i x (fun j:Axis=>Hμ j U) v l r:=by
 change ℛ (chair P M q hp) ((Hσ (UV U)) l r)= _; rw [awakeD P q p M U i x uv hl hr,P.charter_smul,P.charter_list]; apply congrArg; unfold evdiv; refine sum_congr rfl (fun j _=>?_); rw [P.charter_sub]; let C:= chair P M q hp
 have h(b:Bool): ℛ C (𝒵 j b)= galley P i x v (incMove j b) (Hμ j U) l r:=by unfold galley charm lined; simp only; rw [P.charter_sum,P.charter_sum]; unfold C; rw [add_comm (P.vtile _ _)]; rfl
 exact congrArg₂ (·-·) (h true) (h false)
#print axioms coSpread
omit hl hr uv
variable {g:UNI SU.Slot} (hg:Mezzo.Concert g) (V: ChargeRes P η A H f0 P.jump128){DΘ:Coords Wage4} {f:ℕ→ℕ}(HV: VelourQ P η A H f0 v P.jump128 U DΘ f) (qΘ:Tendsto f atTop atTop) (k:P.NightCop)
local notation "ℛX" x:max => rotor hg.gate x
noncomputable abbrev Ψbody (F:Soul)(l r:ℝ):= evdiv P i x (fun j:Axis=> (Txn j F)) v l r -- as used before point cost.
local notation "Kσ" t:max => rawSolo P M i x p pseV t f0 hp
local notation "bV" z:max=> Ψbody P q p M i x hp z l r
variable (Q:Exposure P f0)
noncomputable abbrev tΡ:= gatherG DΘ -- noncomp Universe local conflict
include W Q HV qΘ k ht7 hl hr
set_option maxHeartbeats 310000 in
theorem sweeping (f':s<v)(u:payable P v 2) : ‖ Ε v • bV (ℛX U) -(↑(gatherG DΘ):ℂ) • (Kσ u) l r‖ ≤ wageMonth P η A H s v:=by
 obtain ⟨o,h⟩:= W.tally.poses s ht7 q p; let T:=W.stamps s v q o ht7 f'.le p h; let f:=coSpread P q p M (ℛX U) i x hp T hl hr
 change ‖Ε v • evdiv P i x _ v l r- _‖ ≤ _; change _ = Ε v • evdiv P i x (fun j=> Txn j (ℛX U)) v l r at f; rw [←f]
 obtain ⟨t,rT⟩:= placement_m P M s v o; let hq:= clockP P s; exact angleFrame P o t rT qΘ k i f' ht7 W.living.1 W.living.2.1 η q M p x T (by linarith only [hq,hl]) (by linarith only [hq,hr]) hp u U HV hg Q (healthy P M W ht7) -- implicit w,v0? check
#print axioms sweeping
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
