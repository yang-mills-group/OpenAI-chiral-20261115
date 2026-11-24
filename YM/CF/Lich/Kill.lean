import YM.CF.Lich.Line
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
-- pack defect probes preserving anchors
local notation "m"=> Domain N B
local notation "sB"=> Domain P B
abbrev Sat(S:StepData m sB):=Cell sB ⊕ Bond m ⊕ Bond sB
local notation "K₁"=> U.key
local notation "f₁"=> locals U.key U.key x U.park ((j+104)*radiusB x)
def boon(w:Bond sB)(M:Monk SU.group S): ℝ:=if h:∃ i∈(locals M.key M.key x M.park ((j+104)*radiusB x))ᶜ,i.val.val=w then broad q θ (tape (M.fuel x T q θ l β) h.choose) else 1
variable(t d':ℝ)
def portF: Sat S→ℝ:= Sum.elim (fun i=> if i∈(nearFace S (U.key.dome ((j+110)*radiusB x)))ᶜ then tokenF U.key q x F i else 1)
 (Sum.elim (fun i=> if i∈(nearNoise (U.key.dome ((j+100)*radiusB x)))ᶜ then tidal U.key x t d' q F U.V U.k i else 1) (fun w=> boon A w U)) -- tune token ambiguity
lemma boundB : (∏ i,A.portF U t d' i)=Qen T x q θ l U β t d' j:=by
 let f:= f₁; let P:=fun i:Cell sB=> tokenF U.key q x F i; let Z:=tidal U.key x t d' q F U.V U.k; have hg{ι:Type}[Fintype ι](X:Finset ι)[DecidableEq ι](F':ι→ℝ) : (∏ i, if i∈X then F' i else 1)=∏ i∈X,F' i:=by rw [←prod_filter]; simp
 let g(i:Active U.key x U.park): Bond sB:= i.val.val
 have hz:(∏ i∈ fᶜ,broad q θ (tape (U.fuel x T q θ l β) i))= ∏ i:Bond sB,boon A i U:=by
    have he:Injective g:=fun _ _ h=>Subtype.ext (Subtype.ext h); apply prod_of_injOn g he.injOn (fun i _=> mem_univ _) ?_ ?_
    · intro a _ h; exact dif_neg (fun ⟨i,v,e⟩=>h ⟨i,v,e⟩) -- for A polarity magic
    intro b v; unfold boon; let p:∃ i∈fᶜ,i.val.val=g b:= ⟨b,v,rfl⟩; rw [dif_pos p,he (p.choose_spec.2)]
 rw [Fintype.prod_sum_type,Fintype.prod_sum_type]; unfold portF; dsimp only [Sum.elim_inl,Sum.elim_inr]; rw [hg _ P,hg _ Z]; rw [←hz]; unfold Qen Reine.moist f P Z; ring
end Muster
end YM.CF.Lich
