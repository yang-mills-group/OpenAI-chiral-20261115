import YM.SU5.Interaction.Source.Flux
import YM.SU5.Interaction.Rate

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

namespace Preparation
open FullBill Window Marks
open Pitching Focus QuadClock
variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}(Y:Course P F)

/- # M3. The local source at interior level (still PRE truncation).

 Eq.125--127 and symbolic operator to be used in paying that insertion.
 This is ALWAYS on the actual data reading. Use at ANY block length r, hence also on the true
 pose separation ticks in the test. Does not pay yet their costs in L/Power.
 -/
open YM.CF.StressExchange
variable (i k s : ℕ)(p:s < Y.uv k) (r:ℕ)
variable (x:Site (P.Ctor (Y.ir i) s)) (b0:Orbit (P.Ctor (Y.ir i) s))
-- Important! Keep peg at that very parameter. Not even projecting all-Flags.
lemma projects_here : IsStarProjection (spar P.K.j (RootBook Y i k s).J.M (((Y.voyage i).CapeT s) b0)) ∧ Sea (spar P.K.j (RootBook Y i k s).J.M (((Y.voyage i).CapeT s) b0)) (changeM P.U (((Y.voyage i).CapeT s) b0) (RootBook Y i k s).J.M) := by
 let hq:= P.J.gran.trans ((Y.voyage i).ownership s).size; let W:=(((Y.voyage i).ownership s).paid.paid b0).shrink P.J.hr.le
 exact ⟨(P.U.broadness _ hq _).projection _ W, sea_g hq _ W _⟩
-- of the `Locus` ket before exponent/board; L of the delivery to use.
-- Greek Nι and Lπ fixed on this s, phantom argument in notations
local notation "Rsκ" β:max => (RootBook Y i β s)
local notation "Nι" β:max => (P.Ctor (Y.ir i) s)
local notation "Lπ" β:max => ((Y.voyage i).CapeT s)
local notation "uχ" β:max => ((Lπ β) β)
local notation "Aσ" β:max => (tickA (Nι β))
local notation "Sχ" β:max => (spar P.K.j (Rsκ k).J.M (uχ β))
local notation "Cχ" β:max => (capT (Sχ β) ((Rsκ k).J.P.den (uχ β)))
local notation "Zκ" β:max => (Zcharge (Sχ b0) (Aσ β) (Cχ b0) (roomW β r))
local notation "Jδ" β:max => (StressExchange.toll r (Sχ β) (Cχ β))
local notation "Kχ" β:max => (relV P.U (Rsκ k).J (uχ β))
include p x b0 r in

lemma freeDriver : let g:=projects_here Y i k s b0 |>.1
 let L:= Sault.ballL (nursery (Sχ b0) g) (Kχ b0); IsStarProjection (Aσ x) ∧ acts (Zκ x) (Kχ b0)=0 ∧ (∀ y, L (acts (coinZ (Sχ b0) (roomW x r)) y)=acts (Zκ x) (L y)) ∧ (Zκ x)=legTax (Sχ b0) (Aσ x) (roomW x r) • 1+dg (∑ a:Axis,((Jδ b0) a (x+r•(Lattice.step a))- (Jδ b0) a (x-r• (Lattice.step a))))-(dg (roomW x r)-((Aσ x)*(roomW x r)).trace • 1) ∧
    (inhibit (Sχ b0) (Cχ b0) (roomW x r))=(∑ a:Axis,((Jδ b0) a (x+r• (Lattice.step a))- (Jδ b0) a (x-r• (Lattice.step a)))) ∧ (∀ y:Phys (Nι x),inner ℂ (mateK (Nι x)) (acts (preJ (Aσ x) (inhibit (Sχ b0) (Cχ b0) (roomW x r))) y)=inner ℂ (mateK (Nι x)) (acts (dg (inhibit (Sχ b0) (Cχ b0) (roomW x r))) y))∧ acts (star (dg (roomW x r)- ((Aσ x)*(roomW x r)).trace • 1)) (mateK (Nι x))=0∧∀ K:Op (Single (Nι x)), (∀ I:Finset (Single (Nι x)),cutM I*K*cutM I=K→Reed.Fine (Tset (Nι x)) I false (preJ (Aσ x) K)):=by
 intro g L; let h:=g; have ht:TagG (Sχ b0) (Cχ b0):=tag_g _ h; have hp:IsStarProjection (Aσ x):=by rw [touchP]; exact cutM_idp _
 let x0:= changeM P.U (uχ b0) (Rsκ k).J.M; have hv:= (projects_here Y i k s b0).2; let t0:=StressExchange.Eq126 g ht r x; refine ⟨hp,Zvoid (roomW x r) (Aσ x) ht h x0 hv,fun u=>truncZ (roomW x r) (Aσ x) ht h x0 hv _,?_,t0,fun y=>bra_price (inhibit (Sχ b0) (Cχ b0) (roomW x r)) hp (mateK (Nι x)) (tickB (Nι x)) y, ?_, fun K I w=>?_⟩
 · rw [← t0]; rfl
 · rw [star_sub, star_smul,star_one,act_sub,act_smul,act_one,sandwichV (roomW x r) hp (rooms_pay x r) (mateK (Nι x)) (tickB (Nι x)),sub_self]
 rw [touchP]; exact inSector K _ _ w
-- also exact on full Board (not zero assertion). hypotheses will NOT suffice to let another Mark travel *over* the untruncated (inhibit (Sχ b0) (Cχ b0) (roomW x r)).
include p x b0 r in
lemma earns_tip :
 let q:=projects_here Y i k s b0 |>.1
 let X:=(Rsκ k).board b0; let L:= Sault.ballL (nursery (Sχ b0) q) (Kχ b0)
 acts (Zκ x) (denZ (Rsκ k) P.U ((Y.voyage i).CapeT s) b0)=Complex.exp ((Rsκ k).betaL ((Y.voyage i).CapeT s) b0) • (L (acts (coinZ (Sχ b0) (roomW x r) * X.val) (vacuum _))):=by
 intro g X L; let h:acts (tank (Sχ b0) X) (Kχ b0) = L (acts X.val (vacuum _)):= (Sault.loaf (nursery (Sχ b0) g) (Kχ b0) _ |>.symm)
 rw [denZ, map_smul,act_mul]; change Complex.exp _ • (acts (Zκ x) (acts (tank (Sχ b0) X) (Kχ b0)))= _; rw [h,(freeDriver Y i k s p r x b0).2.2.1]
#print axioms freeDriver
#print axioms earns_tip
end Preparation
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.StressExchange.voidCoin
#print axioms YM.CF.StressExchange.notFar
#print axioms YM.CF.StressExchange.flux_pay
#print axioms YM.CF.StressExchange.inhibit_nullTrace

