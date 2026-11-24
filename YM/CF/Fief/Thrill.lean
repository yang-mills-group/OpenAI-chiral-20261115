import YM.CF.Fief.Feast
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Jet Push.AbsoluteSums
local notation "G₅"=> SU.group
variable {c f n N X B:Side}{S:StepData (Domain N B) (Domain X B)}{G:Ratio (mid N B) (mid X B)}{a b e C H D:ℝ}{k l j:ℕ}
open Lich.Muster Font
attribute [local instance] opCStarAlgebra
local notation "ε_"=> Domain N B
local notation "μ_"=> Domain X B
variable{x:ℝ}
section sigma
lemma applause (L:Side)(a ε:ℝ)(hp:0<a) (k:ℕ) :∀ᶠ x in atTop,2*ε*tileN k ≤ a/2*(L.val:ℝ)*radiusB x:=by
 have he:0<a/2*(L.val:ℝ):=by positivity
 exact ((tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto).const_mul_atTop he).eventually_ge_atTop _ -- tune
end sigma
section stock
variable {Φ:nomA N X B→ℂ}{θ:nomA N X B→ Op (Single (mid N B))} {v w u t b' η:ℝ} {T:Tube G₅ S}{A:Muster G S x e T}
variable (P: Ratio (Domain N B) (Domain X B))
structure Scute (M:Muster G S x e T)(K J L H:ℝ)(b v:ℝ)(n k:ℕ)(σ σ' ε:ℝ)(Φ:nomA N X B→ℂ)(θ:nomA N X B→ Op (Single (mid N B)))(V:mSeal X B→ℝ)(W:mSeal X B→ Toll (Single (mid N B))):Prop where
 mote: ∀ i, Flash (dressL G e) (LineE n G K e) n i (M.LawQ i) (V i)
 clan: Ledger σ' W v
 spin(y:Site (Domain X B)): hitE σ V y ≤ b
 clanV: ∀ i,Filer G i (W i) J n (M.Fame i)
 fare(y:Site (Domain N B)):(∑ i:Bit (Site (Domain N B)),tallyL y i ε (radiusB x)*potR (x:=x) (S:=S) V (k*radiusB x) i) ≤ L
 fuel(y:Site (Domain N B)):(∑ i:Bit (Site (Domain N B)),tallyL y i ε (radiusB x)*ledgerV (potQ (S:=S) (x:=x) W (k*radiusB x) i))≤ H
lemma questT (Q:Patch)(n k:ℕ)(K J b v σ σ' ε:ℝ)(p:0<σ)(g:0<σ')(h:0 ≤ b)(hc:0≤v)(hp:0≤ ε):∃ L H:ℝ→ℝ,sizeK Q.L 3 L∧sizeK Q.L 3 H∧∀ᶠ x in atTop,∀{N X B:Side}{e:ℝ}{G:Ratio (mid N B) (mid X B)}{S:StepData (Domain N B) (Domain X B)}{T:Tube G₅ S}(A:Muster G S x e T)(Φ:nomA N X B→ℂ)(θ:nomA N X B→ Op (Single (mid N B)))(s:ℝ),S.ratio=ratio G→ Odd G.count.val →S.patch=Q→ Tally A.LawQ Φ s K σ b n→ Ind G A.Fame σ' v J n θ→∃ V W,Scute A K J (L x) (H x) b v n k σ σ' ε Φ θ V W:=by
 let Y:= price_g Q.L (σ'/2) ε (lampQ σ'*v) k; let F(x):=2*price_g Q.L σ ε b k x; refine ⟨F,Y,(invest_g (v:=b) k 3 p Q.L).scale _,invest_g k 3 (half_pos g) Q.L,?_⟩
 filter_upwards [applause Q.L σ ε p k, applause Q.L (σ'/2) ε (half_pos g) k, Work.E01.radiusB_tendsto.eventually_gt_atTop 0] with x hz hr he N X B e G S T A φ ψ α t p' q L ρ
 obtain ⟨V,f,J'⟩:=L.members; obtain ⟨W,z,K'⟩:=ρ.port; refine ⟨V,W,f,K',J',z,fun i=> ?_,fun i=> ?_⟩
 · have hx:2*ε*tileN k ≤ σ/2*S.patch.L.val*radiusB x:=by rw [q]; exact hz
   have hh:=tallS (S:=S) k he f J' h p hp hx i; rw [q] at hh; exact hh
 have hx:2*ε*tileN k ≤ σ'/2/2*S.patch.L.val*radiusB x:=by rw [q]; exact hr
 have hh:= tallA k he p' t z K' g hp hx i; dsimp only at hh; rw [q] at hh; exact hh
end stock
end YM.CF.Fief
#print axioms YM.CF.Fief.tallA
#print axioms YM.CF.Fief.tallS
#print axioms YM.CF.Fief.cache_l
#print axioms YM.CF.Fief.terms
#print axioms YM.CF.Fief.questT
#print axioms YM.CF.Fief.filled_L
