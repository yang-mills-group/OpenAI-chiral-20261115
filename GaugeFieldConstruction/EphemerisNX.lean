import GaugeFieldConstruction.IonianFareNX
import GaugeFieldConstruction.Diro
import GaugeFieldConstruction.MindFrameNX
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
open scoped YM.CF.Mew
open Fock.Flux Girt TableF TableF.Lenten.Layout Gleam.Guide CF.XGarden CF.XGarden.MastTin ArtCart Zpress ScopeU Buffered
open FrameP
open Violets ProbabilityTheory Regis.Head Regis.Head.Brecht
open Gleam.Guide.Pitcher Coins Pacts Prims
-- notation state.
open Lamour.Bridge.Celeste (liftMoney)
open Vale.Veins Exterior Matrix
open Ballad Window Afterglow Lifted
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Cauchy
variable (s i k:ℕ)
variable {n:ℕ}(X U:BeaconNX n)(V:Side)
local notation "N'"=> count Y s i
lemma echoQuadNX (v: Kea.Pad 4 (count Y s i))(x y p q:Wφ): QfloatNX Y s i k (stormBNX N' x y * stormBNX N' p q)= LearnerNX Y s i k x y*LearnerNX Y s i k p q-LearnerNX Y s i k x q*LearnerNX Y s i k p y:=by
 unfold stormBNX; rw [Matrix.smul_mul,Matrix.mul_smul,map_smul,map_smul]
 let M₁:= (gram Y s i k).J.M
 rw[show QfloatNX Y s i k _= _ from arrowα (token_V v (by decide) M₁) (baseP v M₁) (seaNx_Q Y s i k) (sewC N' x y) (sewC N' p q)]
 let Z:= boardC N' 4 M₁; let L:=pinShift N' 4 M₁; let R':=pinBack N' 4 M₁
 have h(x y p q: Wφ): QueenP Z L R' (sewC N' x y) (sewC N' p q)= QueenP Z L R' (sewC N' x q) (sewC N' x q):=rfl -- tune
 rw[h x y p q,h p q x y]
 unfold LearnerNX Pcω Violets.seamK; simp only [smul_eq_mul]; unfold Z L R' M₁; ring -- tune
lemma payFirstNX(v: Kea.Pad 4 (count Y s i))(p:s≤Y.uv k): allotΩ Y s i k (rayVNX _ [X]) p= quoteP_NX X (LearnerNX Y s i k):=by
 rw[TrueFlagNX Y s i k]; unfold rayFNX; rw [show actWork _ _ _ =WhiteC_NX N' X 1 from mul_one _]; rw[staffP_NX X N', map_sum]; unfold quoteP_NX; apply sum_congr rfl; intro i h; rw[map_smul]; exact congrArg (_ • ·) (lockNx_Q Y s _ _ v _ _) -- tune helper
lemma paySecondNX(v: Kea.Pad 4 (count Y s i))(p:s≤Y.uv k):allotΩ Y s i k (rayVNX _ [X,U]) p= quadP_NX X U (LearnerNX Y s i k):=by
 rw[TrueFlagNX Y s i k]; unfold rayFNX; rw[show actWork _ _ _ =WhiteC_NX N' X 1* WhiteC_NX N' U 1 from (by unfold actWork; simp)]; rw[staffP_NX X N',staffP_NX U N',sum_mul,map_sum]
 unfold quadP_NX; apply sum_congr rfl; intro v0 h; rw [mul_sum, map_sum]; apply sum_congr rfl; intro w u
 rw[Matrix.smul_mul,Matrix.mul_smul,map_smul,map_smul]; simp only [smul_eq_mul]; rw[echoQuadNX Y s i k v,←_root_.mul_assoc]; try ring
lemma solidEra1NX (a b:ℕ→ℕ)(p:Tendsto a atTop atTop)(u:Tendsto b atTop atTop): Tendsto (fun j=> QfloatNX Y s (a j) (b j) (rayFNX _ [X] 1)) atTop (𝓝 (quoteP_NX X κF)):=by
 refine (show Tendsto (fun j=>quoteP_NX X (LearnerNX Y s (a j) (b j))) atTop _ from (tendsto_finsetSum _ fun x h=> (Swalin Y s a b p u (poleBNX X x.1) (poleDNX X x.2)).const_mul _)).congr' ?_
 filter_upwards [(pad_T Y s a p),(Y.uv_grows.tendsto_atTop.comp u).eventually_ge_atTop s] with j q r; exact (payFirstNX Y s (a j) (b j) X q r).symm.trans (TrueFlagNX ..)
lemma solidEra2NX (a b:ℕ→ℕ)(p:Tendsto a atTop atTop)(u:Tendsto b atTop atTop): Tendsto (fun j=> QfloatNX Y s (a j) (b j) (rayFNX _ [X,U] 1)) atTop (𝓝 (quadP_NX X U κF)):=by
 have H:Tendsto (fun j=>quadP_NX X U (LearnerNX Y s (a j) (b j))) atTop (𝓝 (quadP_NX X U κF)):=by
   unfold quadP_NX; apply tendsto_finsetSum _; intro v _; let F:= LearnerNX Y s; refine tendsto_finsetSum _ (fun w _=> ?_)
   exact ((((Swalin Y s a b p u (poleBNX X v.1) (poleDNX X v.2)).mul (Swalin Y s a b p u (poleBNX U w.1) (poleDNX U w.2))).sub ((Swalin Y s a b p u _ _).mul (Swalin Y s a b p u _ _))).const_mul _)
 refine H.congr' ?_; filter_upwards [pad_T Y s a p,(Y.uv_grows.tendsto_atTop.comp u).eventually_ge_atTop s] with j q r; exact (paySecondNX Y s (a j) (b j) X U q r).symm.trans (TrueFlagNX ..)
#print axioms solidEra1NX
#print axioms solidEra2NX
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
