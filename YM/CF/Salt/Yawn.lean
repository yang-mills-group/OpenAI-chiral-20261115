import YM.CF.Salt.Rider
import YM.CF.Salt.Stone
import YM.CF.Salt.Piers
import YM.CF.Haro.Tacit
import YM.CF.Salt.Milk
import YM.CF.Salt.Desk
import YM.CF.Plume.Wager
import YM.CF.Haro.Silk
import YM.CF.Salt.Felt
import YM.CF.Tye.Wheel
import YM.CF.Salt.Dial
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre Tye Skye RG Pressure Next.SectorChange Planned.AtomRegular Girt Spire
open Eire Skye Levier Scion Urn Pastry Rill Kennel Pec
open Eire Girt Tulip Spire Proa RG Pressure Stilo Scree Palot Tye Cour Broc Hive Hake
open Esti Forge AnalyticBridge.Annulus1AD Ac AnalyticBridge.GaussianFieldAlignment Tensor Locations Push.SectorMeasure.Oriented
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Precision Tree
open Push.SectorMeasure Slate Atala
variable {P N B:Side}{G:Ratio (mid N B) (mid P B)}(S:StepData (Domain N B) (Domain P B))(x:ℝ)(t:S.ratio=ratio G)(s:Sweep (mid N B))(A:Stores S)(V:Pane (mid P B))(X:Support (Domain P B))
local notation "ζ"=> shiftFaces s.s (S.ratio.embed (Facet.pasta s))
local notation "T"=> reSweep G s
variable (β d:ℝ)(D: Tube SU.group S)(q:Chi)(M: Monk SU.group S)(l:ℕ)(R:GramM (mid P B))(U:Ids (mid P B))(I:Ids (mid N B))(g: Seat (mid N B)→ SU.E)
local notation "Ω"=> (constantGauge g S.ratio)
local notation "ζ'"=> (gauge Ω)
local notation "Wv"=> M.sent x D q d l R.beta
variable (h:(Slate.shiftZ g M).sent x D q d l R.beta= Lattice.gauge (constantGauge g S.ratio) (M.sent x D q d l R.beta))
include h
local notation "μ"=> paintR false false (tradew (mid P B) (constantGauge g S.ratio))
local notation "Q"=> (Slate.shiftZ g M)
set_option maxHeartbeats 750000 in
lemma glowZ (p: Support (Domain P B)) : guardB S x R Q D q d l p=guardB S x R M D q d l p ∧ (warmY S R Q p↔ warmY S R M p):=by
 have ht(i:Cell _):Pressure.toll ((Slate.shiftZ g M).sent x D q d l R.beta) i=Pressure.toll Wv i:=by rw [h,toll_gauge]
 have hp(i:Cell _)(p:i∈ M.key.costs): Pressure.toll (chillB Q) i=Pressure.toll (chillB M) i:=by rw [←pageB Q D x q d l R.beta i p, ←pageB M D x q d l R.beta i p]; exact ht _
 constructor; · exact prod_congr rfl fun i v=> congrArg (fun x:ℝ=> q.read ((x/(R.p.threshold/2))^4)) (ht i)
 have he:∀ i∈M.key.costs,i∈inspectD p→ (Pressure.toll (chillB Q) i<R.p.threshold↔Pressure.toll (chillB M) i<R.p.threshold):=fun i v t=> by rw [hp i v]
 constructor
 · intro v i t w; apply (he i t w).mp; exact v i t w
 intro v i t w; have ht:i∈M.key.costs:=t; exact (he i ht w).mpr (v i ht w)
lemma tune_g (A:Finset (Rust (mid P B)))(p: Copies R): lure S x R Q (threadG Ω U) D q d l A= μ (Eire.lure S x R M U D q d l A):=by
 unfold Eire.lure; rw [map_prod]; refine prod_congr rfl fun j _=>?_ ; rcases j with i|i
 · let D':= i.1.val.2; obtain ⟨hx,hg⟩:= glowZ S x d D q M l R g h D'; unfold OpK; dsimp only [Sum.elim_inl]; unfold Eire.sheer; dsimp only; rw [show warmY S R Q _↔ _ from hg]; split; swap; · rw [map_zero]
   letI: NormedAlgebra ℚ (Cipher (mid P B)):= NormedAlgebra.restrictScalars ℚ ℝ _; rw [h,show guardB S x R _ _ _ _ _ _= _ from hx,map_smul,map_sub,map_one, map_exp μ ((μ).toLinearMap.continuous_of_finiteDimensional)]; split
   · obtain ⟨a,b,v⟩:=p.capital i.1; rw [v.gaugeV]
   obtain ⟨a,b,v⟩:=p.heritage i.1; rw [v.gaugeV]
 unfold OpK; dsimp only [Sum.elim_inr]; unfold shineK; dsimp only; obtain ⟨hx,hg⟩:= glowZ S x d D q M l R g h (i.val.1.val.2 \ i.val.2); rw [hg]; split; obtain ⟨a,b,v⟩:= p.forced i; rw [hx,map_smul,h,v.gaugeV]; rw [map_zero]
end YM.CF.Salt
