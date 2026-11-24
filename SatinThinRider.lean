import YM.CF.Salt.Rider
import YM.CF.Pso.Pick
/-! relative version Salt/Rider -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre Tye Skye RG Pressure Next.SectorChange Planned.AtomRegular Girt Spire
open Eire Skye Levier Scion Urn Pastry Rill Kennel Pec
open Eire Girt Tulip Spire Proa RG Pressure Stilo Scree Palot Tye Cour Broc Hive Hake
open Esti Forge AnalyticBridge.Annulus1AD Ac AnalyticBridge.GaussianFieldAlignment Tensor Locations Push.SectorMeasure.Oriented
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure Slate Atala
variable {P N B:Side}{G:Ratio (mid N B) (mid P B)}(S:StepData (Domain N B) (Domain P B))(x:ℝ)(t:S.ratio=ratio G)(s:Sweep (mid N B))(A:Stores S)(V:Pane (mid P B))(X:Support (Domain P B))
local notation "ζ"=> shiftFaces s.s (S.ratio.embed (Facet.pasta s))
local notation "T"=> reSweep G s
variable (β d:ℝ)(D: Tube SU.group S)(q:Chi)(M: Monk SU.group S)(l:ℕ)
variable (R:GramM (mid P B))(U:Ids (mid P B))(I:Ids (mid N B))
local notation "Wv"=> M.sent x D q d l R.beta
variable (hT:(rot s M).sent x D q d l R.beta=flashA (reSweep G s) (M.sent x D q d l R.beta))
include hT t

variable (S0 S1:RegBudget (mid P B))(Y0:ForceBudget (mid P B))
local notation "R_alt" => (Oise.color_b R R.beta S0 S1 Y0 R.v)
lemma step_hymn (X:Finset (Rust (mid P B)))(hF:∀ (i:Scree.Hub (mid P B))(V:Pane (mid P B)),S0 (moveHub T i) (flashA T V)=thunder T (R.F i V))(hS:∀ (i:Scree.Hub (mid P B))(V:Pane (mid P B)),S1 (moveHub T i) (flashA T V)=thunder T (R.slip i V))(hA:∀ (i:Force (mid P B))(V:Pane (mid P B)),Y0 (moveForce T i) (flashA T V,bun T U)=thunder T (R.K i (V,U))) : lure S x R_alt (rot s M) (bun T U) D q d l (X.image (rave T))= thunder T (lure S x R M U D q d l X):=by
 unfold Eire.lure; rw [prod_image (rave T|>.injective.injOn),map_prod]; refine prod_congr rfl fun j _=> ?_; rcases j with i|i
 · unfold OpK; dsimp only [Sum.elim_inl]; -- change
   change Eire.sheer S x R_alt (rot s M) D q d l ((lapT T i.1),i.2)=_ ; unfold Eire.sheer; dsimp only; let K':=i.1.val.2; let V':= lapT T i.1; obtain ⟨hx,hg⟩:= rudd S x t s d D q M l R hT K'; by_cases g:warmY S R M i.1.val.2; swap; · rw [if_neg g, if_neg (show ¬ warmY S R_alt (rot s M) V'.val.2 from mt hg.mp g),map_zero]
   rw [if_pos g, if_pos (show warmY S R_alt (rot s M) V'.val.2 from hg.mpr g), map_smul,map_sub,map_one]; letI: NormedAlgebra ℚ (Cipher (mid P B)):= NormedAlgebra.restrictScalars ℚ ℝ _
   rw [map_exp (thunder T) ((thunder T).toLinearMap.continuous_of_finiteDimensional), show guardB S x R_alt _ _ _ _ _ ((lapT T i.1).val.2)=_ from hx, hT]; split; exact congrArg (fun c:Cipher (mid P B)=> guardB S x R M D q d l K' • (exp c-1)) (hF ..); exact congrArg (fun c:Cipher (mid P B)=> guardB S x R M D q d l K' • (exp c-1)) (hS ..) -- tune
 unfold OpK; dsimp only [Sum.elim_inr]; change shineK S x R_alt (rot s M) _ _ _ _ _ (moveForce T i)=_ ; unfold shineK; dsimp only; let H:= i.val.1.val.2 \ i.val.2; obtain ⟨hx,hg⟩:= rudd S x t s d D q M l R hT H; have he: actY T H=(moveForce T i).val.1.val.2 \ (moveForce T i).val.2:= map_sdiff ..
 rw [←he,show (Eire.warmY S R_alt (rot s M) (actY T H)) ↔ _ from hg]; split; rw [map_smul,show guardB S x R_alt (rot s M) D q d l (actY T H)=_ from hx, hT]; congr 1; rw [hA]; rw [map_zero]
end YM.CF.Salt
end
