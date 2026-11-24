import YM.SU5.SatinWard.Resolution.MarginalJ
import YM.SU5.SatinWard.Resolution.ReclaimJ
import YM.SU5.SatinWard.Resolution.CasterH
/- Aperture comparator at *actual elected* budgets. For all columns (not just unit vectors). `trueKey^-1` in our measures accounts for treatment at THIS w. Readers shouldn't assert exact reform at all cutoffs.Take w sufficiently late separately from estimator witness. Comparator is complex-valued as applied BOTH charges (no star implicit, can also do star by the purchased charge rules above). -/
set_option autoImplicit false
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
namespace MezzoBill
open Internal

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
open Worth Pays BProof Aria Casting MacroGrid Selected
open SoulField Verdance SatinWard.Installment
variable (M:P.par.R.L.val%16=1)(k:P.NightCop) {η:Type}[Fintype η] {A H C d c a b φ:ℝ} {Z:ℕ→ℕ} {β:ℕ→ℝ}{Q:ℕ→HorizonLens→HorizonLens→ℝ}{m f:ℕ} {r:P.Register} {T:ℕ→ℝ}
variable (κ:CouncilGrant P r d c T Z Q β) (Θ:PublicKernel P Z Q)
variable (χ:HeartClock P f H A a b φ m M Z η)(ρ:Piano P f C H A η Z)
variable (Teds:Melodic P η A f Z) -- status packages live in Loyalty
open SoulField Verdance SatinWard.Installment Orchid
local notation "ℓ" i:max=> moonClock P (corridorHeight P i)
local notation "Ψ" i:max=> vigorΩ P.par i
local notation "τ"=> fun v:ℕ=>10*moonClock P (corridorHeight P v)
noncomputable abbrev estimates_line_st (i m:Axis)(x y:ZKey)(d:Gaia):ℂ:=gaugeKin i (rangeHue x) m (rangeHue y) d
noncomputable abbrev censusSeamSt (a₀:Axis)(z:P.Spectrum0 a₀)(p:Bool→ Vantage)(b:Bool)(O:Bool→ Cover) (tp:∀ i:Bool,ResidualPermit (O i))(j i m:Axis)(v:ℕ) (x y:ZKey) :ℂ:= duetCX P M k j (P.advocate a₀ z j) κ p b O Teds tp i m v ((τ) v) x y
local notation "Δ" => censusSeamSt P M k κ Teds
local notation "tx" => estimates_line_st
private def fVertSt (x y:ZKey)(g:ℝ)(i j:Wage3):ℝ:= ‖x i*y j‖*g
lemma bridgeDuty_st (x y:ZKey)(g:ℝ)(q:0≤g): dutyM x y g ≤ ‖x‖*‖y‖*(324*g):=by
 let D:=‖x‖*‖y‖*g; have hx (i j:Wage3):fVertSt x y g i j ≤ D:=by unfold fVertSt; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (mul_le_mul (norm_le_pi_norm x i) (norm_le_pi_norm y j) (norm_nonneg _) (norm_nonneg _)) q
 unfold dutyM; apply le_trans (sum_le_sum (g:=fun i=>∑ _j:Wage3,D) (fun i _=> sum_le_sum (fun j _=> hx i j))); simp only [sum_const,card_univ,Orchid.spanMeter,nsmul_eq_mul]; apply le_of_eq; unfold D; push_cast; ring
private lemma pDuty (δ g R:ℝ)(h:0<δ)(q:0≤g)(r:0<R)(t:324*g/δ≤ R)(x y:ZKey): dutyM x y g / R≤ δ*(‖x‖*‖y‖):=by
 refine (div_le_div_of_nonneg_right (bridgeDuty_st x y g q) r.le).trans ((div_le_iff₀ r).mpr ((mul_le_mul_of_nonneg_left ((div_le_iff₀ h).mp t) (by positivity: 0≤‖x‖*‖y‖)).trans_eq (?_)))
 ring
structure MeterPurchaseSt (v:ℕ)(δ:ℝ) :Prop where
 portrait : ∀ (a₀:Axis)(x:P.Spectrum0 a₀)(E:P.Ellis a₀ x)(p:Bool→ Vantage)(b:Bool)(O:Bool→ Cover) (tp:∀ i:Bool,ResidualPermit (O i))
   (j i m:Axis)(y z:ZKey), (Breezeway p (moonClock P (corridorHeight P v)) 60 3700) → Ordered p j b (60*moonClock P (corridorHeight P v)) →
   ‖censusSeamSt P M k κ Teds a₀ x p b O tp j i m v y z-estimates_line_st i m y z (loomDay (p b-p (!b)) (moonClock P (corridorHeight P v)))‖ ≤ δ*(‖y‖*‖z‖)
include χ κ Θ k ρ
lemma purchases_st (pL:64≤ P.par.R.L.val)(δ:ℝ)(h:0<δ) : ∀ᶠ v:ℕ in atTop,MeterPurchaseSt P M k κ Teds v δ:=by
 let μ0:=4*(P.sidesPerTick:ℝ)
 let Q0:ℝ:=2*3700
 have pq:20≤ Q0:=by unfold Q0; norm_num
 have pw: 0≤ Q0:=by linarith
 have l':0≤ μ0:=by unfold μ0; positivity
 obtain ⟨U,vW,K⟩:=starBank P k ρ κ Θ pL Q0 μ0 pw l'
 obtain ⟨_,_,t⟩:= bank_e P k ρ κ Θ pL Q0 μ0 pw l'
 let E:=fee_cherub U P.sidesPerTick
 have hE:0≤ E:=by unfold E fee_cherub; positivity
 filter_upwards [K,t,(polish_late P).eventually_ge_atTop (324*E/δ), reachTrue P ρ] with v p qz g Cq; have ht:0<polishQ P v:=zero_lt_one.trans_le (faderP ..)
 constructor; intro a₀ x J Y b O tp j i m y z hw ho; let Φ:=qz.1; let vQ:payable P v 2:= (ρ.date.stock _ (Φ.money.1.trans Φ.money.2.le)).2
 exact (Carnot P M k j vQ ρ κ p Φ l' pq Y b a₀ x J O le_rfl ((by unfold Q0; exact le_rfl): 2*3700 ≤ Q0) hw χ Teds tp ho i m y z Cq).amount.trans (pDuty δ E _ h hE ht g y z)
#print axioms purchases_st
omit χ κ Θ k ρ
open LitCurrent LitCurrent.AuroraX
#check @spoke_here
private def activeOrbSt (b:Bool)(x:Fin 3)(i:SU.Slot):ℂ:= if i.1=x∧SU.charge i∈sectF b then 1 else 0
noncomputable abbrev huePSt (b:Bool)(g:Fin 3):ZKey:= silenceE (phaseI b g)
lemma hue_meetsSt (b:Bool)(g:Fin 3): rangeHue (huePSt b g)=orbitalI b g:=by rw [huePSt,←giveY,spoke_here]
#print axioms hue_meetsSt
lemma active_idem_st (b:Bool)(g:Fin 3)(i:SU.Slot):activeOrbSt b g i*activeOrbSt b g i= activeOrbSt b g i:=by
 unfold activeOrbSt; split<;> simp
private lemma tax₀_st (b c:Bool)(g h:Fin 3): puBand (orbitalI b g) (orbitalI c h)= ∑ i:SU.Slot, activeOrbSt b g i*activeOrbSt c h i:=by
 unfold puBand; rw [Fintype.sum_prod_type]; refine sum_congr rfl ?_; intro i hi; rw [sum_eq_single i]; · simp only [orbitalI,Matrix.diagonal_apply,↓reduceIte]; rfl
 · intro j u v; simp [orbitalI,Matrix.diagonal_apply, v, Ne.symm v]
 simp
lemma tax₁_st (b:Bool)(g:Fin 3):puBand (orbitalI b g) (orbitalI b g)=(if b then 10 else 5):=by
 rw [tax₀_st]; simp_rw [active_idem_st]; rw [Fintype.sum_prod_type,Finset.sum_eq_single g]
 · unfold SU.Sheet; cases b<;> rw [Fintype.sum_sum_type] <;> simp [activeOrbSt, SU.charge, sectF, SU.pairs,SU.F]
 · intro j _ v; simp [activeOrbSt,v]
 simp
private lemma active_g_st (b c:Bool)(g h:Fin 3)(i:SU.Slot)(p:(b,g)≠(c,h)) : activeOrbSt b g i*activeOrbSt c h i= 0:=by
 by_cases h':g=h
 · subst h; have h':b≠c:= fun t=> p (by rw [t]); rcases i with ⟨g',u'⟩; cases b <;> cases c <;> simp at h'; all_goals by_cases z:g=g' <;> cases u' <;> simp [activeOrbSt,SU.charge, sectF,z, Ne.symm] at *
 by_cases g':i.1=g<;> simp [activeOrbSt,g', h']
lemma tax₂_st (b c:Bool)(g h:Fin 3)(v:(b,g)≠(c,h)):puBand (orbitalI b g) (orbitalI c h)=0:=by rw [tax₀_st]; exact sum_eq_zero fun i _=> active_g_st b c g h i v
noncomputable abbrev kinLedgerSt (i:Axis)(d:Gaia)(b c:Bool)(g h:Fin 3):ℂ:=if (b,g)=(c,h) then (↑(64*kinCost i d*(if b then 10 else 5):ℝ):ℂ) else 0
lemma kinCharges_st(i:Axis)(d:Gaia)(b c:Bool)(g h:Fin 3): estimates_line_st i i (huePSt b g) (huePSt c h) d=kinLedgerSt i d b c g h:=by
 rw [estimates_line_st,hue_meetsSt,hue_meetsSt,gaugeKin,boutique,polKernel]; by_cases u:(b,g)=(c,h)
 · obtain ⟨rfl,rfl⟩:= Prod.mk.inj u; unfold kinLedgerSt; rw [if_pos u,tax₁_st]; cases b<;> norm_num <;> ring
 unfold kinLedgerSt; rw [if_neg u,tax₂_st b c g h u,mul_zero,mul_zero]
#print axioms kinCharges_st
end MezzoBill
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
