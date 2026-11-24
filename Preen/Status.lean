import GlazeS.PrismL
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open Py.Rate.Pitching.Focus (Morn)
open _root_.YM.Preen
variable (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(M:Morn P.par.K)(p:∀ s,F ≤ s → Accordance P M F s (C s) (D s))(T:RobeRoad P F C D x)
local notation "H"=>P.ColorHil 3 x
local notation "W"=>P.ManyF 3 x
local notation "Ω"=>P.heaven 3 x
local notation "U"=>P.cartage 3 x
local notation "S"=>P.seasons 3 x
local notation "ζ"=>P.wealth 3 x
local notation "B"=>paster (Ω)
private lemma tall(t:ℝ≥0)(y:H):P.wealth 3 x ((P.physicalEnergy 3 x).E t y)=(P.seasons 3 x).E t (P.wealth 3 x y):=P.bankHeat ..
include T p
lemma core_c (j:ℕ)(q:F ≤ j): ∃ y:W,
 Tendsto (fun i=>ζ (recoup P F C D x i j)) atTop (𝓝 y) ∧
 ∀ (o:Vantage),tidal P F j<o 3 → pointT P F C D x o=U (o-crest P F) ((S).E ((o 3-tidal P F j).toNNReal) y):=by
 obtain ⟨z,h⟩:= cauchySeq_tendsto_of_complete (advances P F C D x M p T q)
 refine ⟨ζ z,(ζ).continuous.continuousAt.tendsto.comp h,?_⟩
 intro o t
 have h': atom P F C D x (o 3)= (P.physicalEnergy 3 x).E ((o 3-tidal P F j).toNNReal) z :=
     tendsto_nhds_unique (hailE P F C D x M p T j q (o 3) t) (((P.physicalEnergy 3 x).E _).continuous.continuousAt.tendsto.comp h)
 rw [pointT,h',tall]
abbrev idle(j:ℕ):Prop:= Tendsto (fun s:ℕ=>B (ζ (recoup P F C D x s j))) atTop (𝓝 (0))
omit p T in
private lemma cart_paster (y:W)(t:Vantage):B (U t y)=U t ((B) y):=by
 rw [pasted _ (P.stone_norm 3 x),pasted _ (P.stone_norm 3 x),map_sub,map_smul,P.cart_empty,←P.inner_pay 3 x t (Ω) y,P.cart_empty]
lemma cloud_born (j:ℕ)(q:F ≤ j)(e:¬idle P F C D x j)(t:Vantage)(h:tidal P F j<t 3): B (pointT P F C D x t)≠ 0:=by
 obtain ⟨y,r,rh⟩:=core_c P F C D x M p T j q
 have b:B y≠0:=by
    have u:Tendsto (fun s:ℕ=> B (ζ (recoup P F C D x s j))) atTop (𝓝 (B y)):= (B).continuous.continuousAt.tendsto.comp r
    intro he; rw [he] at u; exact e u
 let t':Vantage:= t-crest P F; let v:= (t 3-tidal P F j).toNNReal
 have hW:(S).E v ((B) y)≠0:= fun h=>b ((S).heat_alive _ (h.trans (map_zero _).symm))
 rw [rh t h,cart_paster,← keep_heat _ (P.stone_norm ..) (S) (P.heaven_hot 3 x)]
 intro g
 have hg:= congrArg (fun z:(W)=>‖z‖) g
 rw [P.cart_norm,norm_zero] at hg
 exact hW (norm_eq_zero.mp hg)
/-- witness in Vantage space with support of normalized test. Positive time >1 for support. continuous surrogate on *all* Vantage. -/
lemma actual_local (j:ℕ)(q:F ≤ j):∃ Z:Vantage→(W).space,Continuous Z ∧ ∀ t:Vantage, tidal P F j< t 3→pointT P F C D x t=Z t:=by
 obtain ⟨y,r,rh⟩:=core_c P F C D x M p T j q
 refine ⟨_,P.caravan 3 x (fun t:Vantage=>t-crest P F) (fun t:Vantage=> (S).E ((t 3-tidal P F j).toNNReal) y) (continuous_id.sub continuous_const) (((S).continuousE _).comp (continuous_real_toNNReal.comp ((continuous_apply 3).sub continuous_const))),rh⟩
#print axioms cloud_born
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
