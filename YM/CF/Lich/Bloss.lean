import YM.CF.Lich.Mars
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne
open Vol
-- preserve long lens by footprint
abbrev SightT:= Palot.leaf (Site (Domain N B))
def parcel {c':Side}(f:Site c'→Site (Domain N B))(u:ℕ)(i:Site c')(P':Atom SU.group n):Palot.leaf (Site (Domain N B)):= ⟨halo u ((insert i (P'.footprint i)).image f),⟨f i,(halo_subset u _ ) (mem_image_of_mem _ (mem_insert_self ..))⟩ ⟩
-- eliminate E
variable (s:Signed)
local notation "X₀"=>(turnStore s U.key).costs
local notation "K₁"=> traceZ (turnStore s U.key).flags
local notation "U₀"=> pull s 0 F
local notation "V₀"=> pull s 0 U.V
local notation "m"=> Domain N B
local notation "m'"=> Domain P B
local notation "V'"=> A.phaseLow.threshold
local notation "U'"=> A.phaseUp.threshold
local notation "b₀"=> Stores.till x
local notation "b'"=> b₀/S.patch.L.val
variable (k:ℕ)(L:Palot.leaf (Site (Domain N B)))
def crop(z:ℕ→Palot.leaf (Site (Domain N B)))(f:ℕ→ℝ):= ∑' i:ℕ, if z i=L then f i else 0
-- stencils halo of signed anchor (uses s.act since pull definition)
abbrev shoreS(i:Site m)(u: Atom SU.group n):Palot.leaf (Site m):=parcel (fun j':Site m=>s.act j') k i u
abbrev shoreH(i:Site m')(u:Atom SU.group n):Palot.leaf (Site m):= parcel (fun j':Site m'=>s.act (S.ratio.parent j')) k i u
abbrev extU(i:Site m')(Z:ℕ→ Atom SU.group n):= crop L (fun x'=>shoreH (S:=S) s k i (Z x')) (fun h=>lush_k q (Z h) X₀ U' i U₀)
abbrev extV(i:Site m)(Z:ℕ→ Atom SU.group n):= crop L (fun x'=>shoreS s k i (Z x')) (fun h=>peer_k (Z h) K₁ V' i V₀)
-- exact
abbrev sapC(i:Site m):= crop L (fun j'=>shoreS s k i (rod T.down b' j')) (fun h=>sleeve (rod T.down b' h) K₁ T.low i V' V₀)
abbrev sapU(i:Site m'):= crop L (fun j'=>shoreH (S:=S) s k i (rod T.up b₀ j')) (fun h=>sleeve (rod T.up b₀ h) X₀ T.high i U' U₀)
local notation "Δ"=> (α+γ)
def river(i:Site m'):= β*(sapU A U s k L i + (extU A U s k L i (haste b₀ T.up.cubic) + extU A U s k L i (haste b₀ T.up.quartic))) + extU A U s k L i (haste b₀ T.up.loop)
def flows(i:Site m):=(β+Δ)*(sapC A U s k L i + (extV A U s k L i (haste b' T.down.cubic)+extV A U s k L i (haste b' T.down.quartic)))+extV A U s k L i (haste b' T.down.loop)+ Δ*(extV A U s k L i (batch T.down.cubic b')+extV A U s k L i (batch T.down.quartic b'))
def shardy := -averaged (fun s=> (∑ i,river A U s k L i) - ∑ i,flows A U s k L i)
lemma storyW(z:ℕ→Palot.leaf (Site (Domain N B)))(f:ℕ→ℝ)(h:Summable f): ∑ i,crop i z f=∑' i,f i:=by
 unfold crop; have hp(i:Palot.leaf (Site (Domain N B))): Summable (fun j':ℕ=>if z j'=i then f j' else 0):= by rw [show (fun j':ℕ=>if z j'=i then f j' else 0)={x|z x=i}.indicator f from funext fun u=> by simp [Set.indicator]]; exact h.indicator _
 rw [← Summable.tsum_finsetSum (fun i _=>hp i)]; refine tsum_congr fun i=>by simp
end Muster
end YM.CF.Lich
