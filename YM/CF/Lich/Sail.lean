import YM.CF.Lich.Dive
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
local notation "Δ"=> (α+γ)
variable(k:ℕ){W': Monk SU.group S}{X:Support (Domain N B)}(H:Duo SU.group S U W' X)(p:Ready T x)(hp:1000≤ radiusB x)
local notation "P'"=> W'.sent x T q θ l β
local notation "P₁"=>pull s 0 P'
local notation "B₀"=> radiusB x
open Work.E03
variable (hk: (A.post+90)*radiusB x ≤ k) -- binder issues notation
variable (L:Palot.leaf (Site (Domain N B)))(hf:L.val ⊆ X)
lemma crop_eq{f g:ℕ→ℝ}{z:ℕ→Palot.leaf (Site m)}(p:∀ i,z i=L→f i=g i): crop L z f=crop L z g:=tsum_congr fun i=>by split_ifs with t; exact p i t; rfl
include H p hp hk hf s
lemma sail_c (i:Site m')(P:ℕ→ Atom SU.group n) : extU A U s k L i P=extU A W' s k L i P:= crop_eq _ fun z v=>eastV A U s k H p hp hk _ _ (v.symm ▸ hf)
lemma sail_k(i:Site m)(P:ℕ→ Atom SU.group n) :extV A U s k L i P=extV A W' s k L i P:= crop_eq _ fun z v=>eastW A U s k H p hp hk _ _ (v.symm ▸ hf)
lemma feast_s(i:Site m')(hv:U'=fiery SU.group x S.patch.L)(ht:spanO T x):river A U s k L i=river A W' s k L i:=by unfold river; simp only [sail_c A U s k H p hp hk L hf]; have he:sapU A U s k L i=sapU A W' s k L i:=crop_eq _ fun z v=> sleeves_f A U s k H p hp hk i _ (v.symm ▸ hf) hv ht; rw [he]
lemma feast_v (i:Site m)(hv:V'=temp x) : flows A U s k L i=flows A W' s k L i:=by unfold flows; simp only [sail_k A U s k H p hp hk L hf]; have he:sapC A U s k L i=sapC A W' s k L i:= crop_eq _ fun z v=> sleeves_v A U s k H p hp hk _ _ (v.symm ▸ hf) hv; rw [he]
omit s in
lemma hulk(hv:V'=temp x)(hg:U'=fiery SU.group x S.patch.L)(ht:spanO T x): shardy A U k L=shardy A W' k L:=by unfold shardy; refine congrArg (-averaged ·) (funext fun i=>congrArg₂ (·-·) (sum_congr rfl fun z _=>feast_s A U i k H p hp hk L hf _ hg ht) (sum_congr rfl fun z _=>feast_v A U i k H p hp hk L hf _ hv))
end Muster
end YM.CF.Lich
