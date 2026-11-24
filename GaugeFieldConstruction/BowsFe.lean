import GaugeFieldConstruction.MeterΛ
import GaugeFieldConstruction.GlitchFe
import GaugeFieldConstruction.PartyD
import GaugeFieldConstruction.GravelFe
import GaugeFieldConstruction.Gaufer
import GaugeFieldConstruction.SingingT
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
open BrentFe
open YM.GaugeFieldConstruction Flavor -- potential namespace collision
open BluffV BluffV.Fables
variable (g:Flavor)

variable {X:Cover}{d:ℕ}
abbrev mortFe(X:Cover)(d:ℕ):Equiv.Perm (mort X d):= Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (clanPerm g))
abbrev jFe(X:Cover)(d:ℕ):Equiv.Perm (jungle X d):= Equiv.optionCongr (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (mortFe g X d) (mortFe g X d)))
lemma here_fe (n:Side)(i:jungle X d): hereV n (jFe g _ _ i)=clanWFe g n (hereV n i):=by cases i <;> rfl
lemma ftri_fe(n:Side)(i:jungle X d):feeV n (jFe g _ _ i)=feeV n i:=by cases i <;>rfl
lemma pζFe(n k:Side)(V:Paper n):pR k (Pvi n X d (TribePFe g V))=TribePFe g (pR k (Pvi n X d V)):=by
 let Q:= TribePFe g V; funext i v; obtain ⟨z,rfl⟩:= (clanWFe g k).surjective i; rw [carrierQ,cone_p,cone_p,← Fee_mulfe, mul_sum]; rw [←Equiv.sum_comp (jFe g X d)]; apply sum_congr rfl; intro i' _; simp only [here_fe, Equiv.apply_eq_iff_eq]
 by_cases h:hereV k i'=z; swap; · simp [h]
 subst z; simp only [ftri_fe,if_true]; unfold Pvi; rw [ftri_fe,here_fe, carrierQ, show tollFe g (hereV k i')=tollFe g (hereV n i') from ?_]; swap; · cases i'<;>rfl
 rw [← Fee_mulfe]; ring
lemma Bush_root_fe (k:Side)(x:Cover)(u:0<h)(l:p.power≤3)(S:p.order≤6)(V:Waves): pR k (BushRoot M p h x (SpinFe (chipUFe g) V))= TribePFe g (pR k (BushRoot M p h x V)):=by unfold BushRoot; rw [Moon_fe M g _ (by norm_num [Reifier]) u l S,pζFe]
lemma Beacon_markfe (V:Paper n)(U:Pane n): marketD (TribePFe g V) U= twist (quantU (TVfe n g)) (marketD V U):=by
 let X:= αLines V U; exact Eq.symm (exportD (TVfe n g) false false X) -- Lot uses twist
lemma motto_Fe (k:Side)(x:Cover)(u:0<h)(l:p.power≤3)(S:p.order≤6)(V:Waves)(b:ℝ)(U:Pane k): showTop (BushRoot M p h x (SpinFe (chipUFe g) V)) k b U= twist (quantU (TVfe k g)) (showTop (BushRoot M p h x V) k b U):=by
 unfold showTop; split; · rw[Bush_root_fe M g k x u l S, Beacon_markfe]
 symm; exact map_zero _
#print axioms motto_Fe
end YM.CF.XGarden.MastTin.ArtCart
end
