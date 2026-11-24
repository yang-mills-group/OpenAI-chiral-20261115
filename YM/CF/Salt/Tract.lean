import YM.CF.Salt.Rider
import YM.CF.Stake.Loom
import YM.CF.Salt.Stone
import YM.CF.Salt.Piers
import YM.CF.Haro.Tacit
import YM.CF.Salt.Milk
import YM.CF.Salt.Desk
import YM.CF.Plume.Wager
import YM.CF.Haro.Silk
import YM.CF.Salt.Felt
import YM.CF.Tye.Wheel
import YM.CF.Salt.Dial
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
open Lich Lich.Muster Stake Tarn Forge Hake Laic
variable (i:Words S)(r k:ℕ){Y: Tube SU.group S}{Z:ℝ}(C:Muster G S x Z Y)
local notation "Λ"=> luckP G S s r
lemma dol (i:Sat S): (domeQ r i).val=actY s (domeQ r (satR S s.s (Facet.pasta s) i)).val:=by
 have hx(X Y:Support (Domain N B))(p:X.image (chart s)=Y): halo r X=actY s (halo r Y):=by subst Y; rw [←walkA,actY,← sit_k]; congr 1; rw [map_eq_image,image_image,show ⇑(chart s).symm.toEmbedding ∘ ⇑(chart s)= id from funext fun i=> (chart s).symm_apply_apply i,image_id]
 rcases i with i|i|i
 · exact hx _ _ (start_map s.s (Facet.pasta s) (S:=S) i).symm
 · exact hx _ _ (pin_map s.s (Facet.pasta s) i).symm
 change halo r (grove S i)=actY s (halo r (grove S _)); apply hx; apply Finset.coe_injective; rw [Finset.coe_image, grove_x,grove_x]; exact (Tensor.moves_points ..).symm
lemma heed (i:Words S): (C.mapV r ((rock s).symm i)).val= actY s (C.mapV r i).val:=by
 obtain ⟨j,rfl⟩:=(rock s).surjective i; rw [Equiv.symm_apply_apply]; rcases j with j|j|j; exact dol S s ((C.loft+C.post+200)*radiusB x) j
 · change halo r {j}= actY s (halo r {chart s j}); rw [←walkA,actY,←sit_k]; congr 1; rw [map_singleton]; simp
 change _= actY s (j.val.image (affine s.s (Facet.pasta s))); rw [actY,←sit_k]; let z:=chart s; change j.val= (j.val.image z).map z.symm.toEmbedding; rw [map_eq_image,image_image,show ⇑z.symm.toEmbedding ∘ ⇑z=id from funext fun i=> z.symm_apply_apply i,image_id]
lemma vane : (vast (k:=k) C ((rock s).symm i)).val=actY s (vast (k:=k) C i).val :=by change halo _ (halo _ (C.mapV (k+2) ((rock s).symm i)).val)=_; rw [heed,walkA,walkA]; rfl
variable (l:ℕ)(U:Ride S)(K:Troupe S r (Words S))(i':Folk S r (Words S))
abbrev fieldT(G:Ratio (mid N B) (mid P B))(s:Sweep (mid N B)):Equiv.Perm (Folk S r (Words S)):=Equiv.sumCongr (luckP G S s r) (Equiv.sumCongr (rave (reSweep G s)) (rock s).symm)
local notation "Χ"=> (fieldT S r G s)
local notation "Ξ"=> (BranchX S (r:=r) (vast (k:=k) C) l)
lemma heyK{v:Side}(s:Sweep v)(i:Rust v) : (rustL _ (rave s i)).val.2=actY s (rustL v i).val.2:=by cases i<;> rfl
include t
lemma aught(i:Folk S r (Words S)): (Ξ (Χ i)).val=actY s (Ξ i).val:=by
 rcases i with i|i|i; · change halo l (Eire.frameP S (Λ i))=_; rw [lamp_k G S t, walkA]; rfl
 · change halo l (hatY S (inspected (rustL _ (rave T i)).val.2))= _; rw [heyK, lantern S t,peg_k G S t,walkA]; rfl
 exact vane S x s i k C
lemma found : Palot.fits Ξ (K.image Χ) (quill (chart s) U)↔ Palot.fits Ξ K U:=by
 have hp(i:Folk S r (Words S)):(quill (chart s)) (beamH (Ξ i).val)=beamH (Ξ (Χ i)).val:=by rw [aught S x t, runV, sit_k] -- tune
 constructor; · intro h i v; apply (quill _).le_iff_le.mp; exact (hp i).symm ▸ h (Χ i) (mem_image_of_mem _ v)
 intro h i v; obtain ⟨j,p,rfl⟩:=mem_image.mp v; exact (hp j) ▸ (quill (chart s)).monotone (h j p)
end YM.CF.Salt
