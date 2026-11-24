import YM.CF.Lich.Ent
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
-- actual energy recipe certificate
variable(r r' b k:ℕ)(t w L:ℝ)
local notation "Ta"=> mid N B
local notation "L'"=> blip S U.key r
local notation "S₀"=> senseC (r:=r) A U t w L
local notation "Z₀"=> steerC A U t w
local notation "Q₀"=> Qen T x q θ l U β t w j
local notation "P₀"=> heirI T x U q θ l β A.phaseUp A.phaseLow r j (α+γ) A.muK A.mup A.vita t w L
local notation "O"=> Xb A U V W r' k
local notation "S₁"=> Fa A U V r' k
variable(Φ:nomA N P B→ℂ)(F₁: nomA N P B→ Op (Single (mid N B)))
def claspC:= (∏ i∈L',hue A U V W r r' t w L i)*∏ i:Words S,(1+elk A U V W r' k t w i)
variable {s c l'' d Z E:ℝ}{α' k1:ℕ}
section
lemma boots(L M:Op (Single Ta)): boat L+boat M=boat (L+M):=by apply Subtype.ext; change faceD true false L+faceD true false M=_; simp only [boat,faceD,twinD,Matrix.add_apply,add_smul,sum_add_distrib]
lemma verdict {C D c' w' t' η:ℝ}(p:T.up.Bounds T.high C D c')(Pp:T.down.Bounds T.low w' t' η)(hr:r'≤ r)(hk:(j+104)*radiusB x+10≤r)(hx:Ready T x)(ht:1000 ≤ radiusB x)(h:Portus A U)(hK: Ind G A.Fame s c l'' n F₁)(u:(P₀:ℂ)*Complex.exp (-Φ V.val)= ((Q₀ * (∏ i∈L',S₀ i):ℝ):ℂ)*Complex.exp (plaza A U V W r-Φ (1,1)) ):
 ((P₀:ℂ)*Complex.exp (-Φ V.val)) • (exp (boat (F₁ V.val))).val=Complex.exp ((arcD T x U:ℂ)-Φ (1,1)) • (claspC A U V W r r' k t w L).val:=by
 let f:=plaza A U V W r-(arcD T x U:ℂ); refine sect (U:=S₀) (V:=Z₀) (X:= onyx r A U V W r') (B:=O) (Yw:=hush r A V r') (Z:=S₁) (S:=Single Ta) L' _ _ f _ ?_ ?_ ?_ -- tune implicit argument names
 · rw [boats,boats,boots,Fintype.sum_sum_type]; congr 1; unfold Fa; dsimp only [Sum.elim_inl,Sum.elim_inr]; rw [← add_assoc, laus r A U V k r' hr hK]
 · rw [Fintype.sum_sum_type]; unfold Xb; dsimp only [Sum.elim_inr,Sum.elim_inl]; rw [←add_assoc, highness r A U V W k r' hr hk p Pp hx ht h] -- tune ab.assoc
 rw [u,Muster.steerC, boundB]; unfold f; congr 2; abel
end
end Muster
end YM.CF.Lich
