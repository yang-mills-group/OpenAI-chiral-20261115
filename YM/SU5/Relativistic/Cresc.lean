import YM.SU5.FiniteGaugeData.Pannier.Vintage
import YM.SU5.Relativistic.Tropics
import YM.SU5.FiniteGaugeData.Pannier.FoyerSeat
import YM.SU5.FiniteGaugeData.Marked.Journey.Wake
/-! # Purchases, keeping track of M horizon; checking real estimate on the chosen course. Includes raw power bill. -/

set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.ScreeV
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
variable {A δ ε γ h R κ e a:ℝ} {w d t q l0:ℕ} -- λ' inner

lemma tide_M (s i:ℕ): Tendsto (fun k=> (gram Y s i k).J.M.val.val) atTop atTop:=by
 let f (s i k:ℕ):=(gram Y s i k).J.M
 have hp (s i k:ℕ)(v:s < Y.uv k): f s i k= upMale P.R.L P.R.odd_side (f (s+1) i k):=by
    let X:= (Y.voyage i).X (Y.uv k); change (X.gram s).J.M=upMale P.R.L P.R.odd_side (X.gram (s+1)).J.M
    rw [← (X.pull.owns s v.le).taste,← (X.pull.owns (s+1) v).taste]; exact ((P.W.arm _ (Y.uv k)).pass s v).grown
 refine tendsto_atTop.2 fun b=>?_ ; filter_upwards [Y.uv_grows.tendsto_atTop.eventually_ge_atTop (s+b)] with k u; change b ≤ (f s i k).val.val
 induction b generalizing s with
 | zero=> simp
 | succ b ih=>
    have hv:= ih (s+1) (by omega); rw [hp s i k (by omega)]; change b+1 ≤ P.R.L.val*(f (s+1) i k).val.val
    have he:= P.R.coarse; let X:=(f (s+1) i k).val.val; have p:0<X:=(f (s+1) i k).val.property
    change b≤X at hv; change _ ≤ _ * X; have ht:= Nat.mul_le_mul_right X he; omega
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.tide_M
