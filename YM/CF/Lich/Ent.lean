import YM.CF.Lich.Stare
import YM.CF.Lich.Temp
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
variable (r r' k b:ℕ)
open Font
local notation "T₀"=> mapV A b
local notation "Zc"=> Site (Domain N B)
local notation "Sol"=> Words S
variable (t w L:ℝ)
def hue :Hos S r→ Cipher (mid N B):= rootK (senseC (r:=r) A U t w L) (onyx r A U V W r') (hush r A V r')
def elk :Words S→Cipher (mid N B):= sweetK (steerC A U t w) (A.Xb U V W r' k) (A.Fa U V r' k) -- order params Temp r'? k
section
variable{a d' c v v' z y:ℝ}{a' :ℕ}{J: nomA N P B→ Op (Single (mid N B))}{Φ:nomA N P B→ℂ}
variable{M:Monk SU.group S}{V' W': Rent0 G e}{X:Support (Domain N B)}
variable(p:Gard (n:=n) (a:=a) (a':=d') (C:=c) (D:=v) (c:=v') (v:=z) (Z:=y) (J:=J) (Φ:=Φ) (R₁:=a') A r r' b k)(h: Muster.Post A U M V W V' W' k X)
local notation "K₀"=> (A.mapV b)
local notation "D₀"=> elk A U V W r' k t w
include p h
lemma roofH(i:Hos S r)(v:stem S i ⊆ X): hue A U V W r r' t w L i= hue A M V' W' r r' t w L i := by
 unfold hue rootK senseC; obtain ⟨f,z⟩:= A.vital_g U V W p h i v; rw [f,z,birth_h A U h.duo p.ash p.ages t w L i (Subset.trans (farther p.trial) v) p.forwards p.tilt] -- tune order
lemma roofX(i:Sol)(v:(K₀ i).val ⊆ X): D₀ i=elk A M V' W' r' k t w i:=by
 rcases i with i|i|i
 · unfold elk sweetK; simp only [Sum.elim_inl, steerC]; rw [payF A U t w h.duo p.ash p.ages p.forwards _ v]
 · obtain ⟨u,u'⟩:= vital_l A U V W p h i v; unfold elk sweetK Xb Fa; simp only [Sum.elim_inr,Sum.elim_inl,u,u']
 obtain ⟨u,u'⟩:= vital_r A U V W p h i v; unfold elk sweetK Xb Fa; simp only [Sum.elim_inr, Sum.elim_inl,u,u']
-- habitat even
omit h p
lemma primed(D:Support (Domain N B))(V:Op (Single (mid N B)))(u:Hop V D)(a:ℂ): Flour (camp D) (hollow a*exp (boat V)).val:= Flour.mul (Flour.grainE.smul _) (flourish (flourish_b _ _ u))
lemma malt(D:Support (Domain N B))(V:Cipher (mid N B))(p: Flour (camp D) V.val): Flour (camp D) (V-1).val:= by change Flour _ (V.val-1); rw [sub_eq_add_neg,← neg_one_smul ℂ]; exact Flour.add p (Flour.grainE.smul _)
include p
lemma nice_r(i:Hos S r): Flour (camp (stem S i)) (hue A U V W r r' t w L i).val :=primed _ _ (warmth_c A V p i) _
lemma nice_v(i:Sol) : Flour (camp (K₀ i).val) (D₀ i).val :=by
 rcases i with i|i|i
 · exact malt _ _ (Flour.grainE.smul _)
 · exact malt _ _ (primed _ _ (existH A U V p i) _)
 exact malt _ _ (primed _ _ (farB A V p i) _)
end
-- Axiom staples
end Muster
end YM.CF.Lich
