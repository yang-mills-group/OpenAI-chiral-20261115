import YM.SU5.FiniteGaugeData.Pannier.Chinks
/-! # Roof effect on flags and local orientation. -/

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
namespace Pannier
variable {n:Side}{u d t:ℝ}{r:ℕ}{P:Orbit n→Pane n}
-- From tolerance-p flags on direct input; even if sampler uses larger grant threshold `u`.
theorem fledged (p:Roof n u d r P) (S:Support (More n)) (X:Orbit n)(l:t≤u)(h:Disjoint (halo r S) (flags t X.1)) : Agrees S (P X) X.1 := by
 intro i e v
 apply p.lamp X.1 X.2 i
 apply Finset.disjoint_left.mpr; intro j hj he
 obtain ⟨k,y,w⟩:= halo_spec.mp he
 have hp : k∈ S:=by
    rcases (show k=i.1 ∨ k=i.1+step i.2 from (by simpa [Skye.ends] using y)) with rfl|z
    · exact e
    rwa [z]
 exact Finset.disjoint_left.mp h (halo_spec.mpr ⟨k,hp,w⟩) ((flags_spec ..).mpr <| have hh:= (flags_spec ..).mp hj; by obtain ⟨i,w,e⟩:=hh; exact ⟨i,w,l.trans_lt e⟩)

lemma seep (p:Roof n u d r P)(l:t≤u)(X:Orbit n) : flags t (P X) ⊆ halo (r+4) (flags t X.1):=by
 intro i b
 obtain ⟨k,hk,v⟩:= (flags_spec ..).mp b
 by_contra! h
 suffices hp : Disjoint (halo r (touched k)) (flags t X.1) by
    rw [show faceValue (P X) k=faceValue X.1 k from WilsonStartup.face_local k _ _ (fledged p _ _ l hp)] at v; exact h (halo_subset (r+4) _ ((flags_spec ..).mpr ⟨k,hk,v⟩))
 apply Finset.disjoint_left.mpr; intro j hj H; apply h; obtain ⟨y,e,q⟩:= halo_spec.mp hj
 have hg : separation j y ≤ r := (separation_comm ..).trans_le q
 apply halo_spec.mpr; refine ⟨j,H,(separation_triangle j y i).trans ?_⟩
 have he:= separation_triangle y k.1 i; have hz:= Work.E01.sep_touched k i hk; have hx:=Work.E01.sep_touched k y e; rw [separation_comm y k.1] at he; omega

lemma flag_coat (P:Pane n)(t:ℝ): (flags t P).card≤ (roughness t P).card*4:=by
 apply le_trans (card_le_card (show flags t P ⊆ (roughness t P).biUnion touched from ?_)); swap
 · intro i e; obtain ⟨q,v,l⟩:= (flags_spec ..).mp e; exact mem_biUnion.mpr ⟨q,mem_filter.mpr ⟨mem_univ _,l⟩,v⟩
 exact card_biUnion_le.trans ((sum_le_sum (g:=fun _=>4) fun i _=> Work.E01.touched_card i).trans_eq (by simp))
lemma grease_f (p:Roof n u d r P)(X:Orbit n)(v:t≤u)(b:ℕ)(s:Signed) : (halo b (flags t (pull s 0 (P X)))).card ≤ ((roughness t X.1).card*4*((r+4)*2+1)^4)* (b+b+1)^4:= by
 apply le_trans (Corona.halo_size ..); apply Nat.mul_le_mul_right
 have ht:(flags t (pull s 0 (P X))).card=(flags t (P X)).card:=by rw [←Work.H03.flags_send s 0 t (P X),card_image_of_injective _ (WilsonStartup.aff_inj s 0)]
 rw [ht]; apply (card_le_card (seep p v X)).trans ((Corona.halo_size ..).trans ?_); gcongr; exact flag_coat ..; omega
end Pannier
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.Pannier.grease_f
