import YM.SU5.SatinWard.Resolution.Harmonize
import YM.SU5.SatinWard.Resolution.Puncheon
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
private theorem nimbusSt {M:Type*}[NormedAddCommGroup M][NormedSpace ℝ M] (b v w h:ℝ)(x y u z:M)(p:0<b)(hy:‖b • u-y‖ ≤ h)(hz:‖y-z‖≤ v)(hu:‖u-x‖ ≤ w): ‖x-b⁻¹ • z‖ ≤ w+(v+h)*b⁻¹:=by
 refine (norm_sub_le_norm_sub_add_norm_sub _ u _).trans (add_le_add (by rw [norm_sub_rev]; exact hu) ?_)
 have ht:‖b • u-z‖ ≤ h+v:=(norm_sub_le_norm_sub_add_norm_sub _ y _).trans (add_le_add hy hz)
 rw [← smul_inv_smul₀ p.ne' z] at ht; rw [←smul_sub, norm_smul,Real.norm_of_nonneg p.le] at ht; rw [mul_comm] at ht
 rw [←div_eq_mul_inv]; exact (le_div_iff₀ p).2 ((add_comm h v) ▸ ht)
local notation "Φℓ" b:max=> Beam P q k t v b
noncomputable abbrev spindle (v:ℕ)(A:Fin 8→ P.LagOp i x)(l r:ℝ):= bead P q k t i x v A l r true+ bead P q k t i x v A l r false
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
open Velas
local notation "Τζ"=> torrid P vo A H
include p hl hr ht7 W in
lemma adjacentP (u:s≤v)(t':Bool) : δ₀ ≤ l+(Φℓ t') i ∧ δ₀ ≤ r-(Φℓ t') i:=by
 obtain ⟨o,h⟩:= W.tally.poses s ht7 (So t) (Pt t); have hx:= hor_6 P _ k t (W.stamps s v _ o ht7 u (Pt t) h); have hb:= abs_le.mp (Beam_paid (v:=v) P q p k t i t'); constructor <;> linarith only [hb,hl,hr,clockP P s,hx]
include W K ht7 hl hr c
include Hχ Hd Wa in
lemma trail : ‖(δη ((Z₀ v).symm Kℓ))- (Ψ𝓡 t) ((Εw v)⁻¹ • (Z₀ v).symm U) l r‖ ≤ dayNum P η s v vo A H:=by
 have u:0<δ₀:= clockP P s; have p':δ₀ ≤ l:= by linarith only [hl,u]
 have q':δ₀ ≤ r:=by linarith only [hr,u]
 let z':= (Εw v); let G:= dayNum P η s v vo A H; let A':=(Z₀ v).symm Kℓ; let F':=δη A'; let Yβ (b:Bool):= γb b Kℓ; let Tβ (b:Bool):= βQ b A'; let vq:= panorama P η q p M k t U vo i x W ht7 hl hr K lι Hχ Hd c
 let D (ζ1:Soul) := (Ψ𝓡 t) ζ1 l r; let Y₀:=Yβ true+Yβ false; let F₀:=(φ🌸 U) t l r; let Ω:= (Ψε v); have he(z:Soul)(r:ℝ):D (r • z)=r • D z:=map_smul (contoBill P pT e vo (So t) M K (Pt t) i x W (u.trans_le p') (u.trans_le q')) _ _ -- order U.
 have ht(b:Bool):‖Yβ b- Tβ b‖≤2*Ω:=by
    obtain ⟨hb,hv⟩:= adjacentP P η q p M k t i W ht7 hl hr c.le b; unfold Yβ  Tβ bead; rw [←P.locate_sub,P.locate_cost,norm_sub_rev]; let d:=price_cost P pT e vo _ M K (Pt (Yt b)) i x Kℓ Wa ht7 hb hv c; rw [leg_norm,mul_one] at d; exact d
 have d0:‖Y₀ - F'‖ ≤ 4*Ω:=by rw [show Y₀-F'= (Yβ true - Tβ true)+(Yβ false - Tβ false) from (by unfold Y₀ F' Yβ Tβ spindle; abel)]; exact (norm_add_le ..).trans ((add_le_add (ht true) (ht false)).trans (by linarith))
 let z:=D ((Z₀ v).symm U); have hu:‖F₀-z‖ ≤ (2*Ω) * |Τζ|:=by
    rw [norm_sub_rev]; refine (price_cost P pT e vo _ M K (lifeC q p k t) i x U Wa ht7 p' q' c).trans ?_; rw [mul_right_comm]; exact mul_le_mul_of_nonneg_left ((Velas.tempered P _ _ _ _ _ _ Hχ).trans (le_abs_self _)) (by exact mul_nonneg zero_le_two (wbal P M Wa ht7 v).le)
 change ‖F' - D _‖ ≤ _; rw [he]; exact nimbusSt _ _ _ _ F' F₀ Y₀ z (intLive _) vq hu d0
end Imperial
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
