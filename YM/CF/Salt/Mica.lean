import YM.CF.Salt.Rider
import YM.CF.Jade.Lease
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
open Rue
variable (t:ℝ){n:Side}(D A':Support (More n))(T:Sweep n)(U₀:Pane n) -- tune
lemma glowA : pingS t (actY T D) (flashA T U₀) ↔ pingS t D U₀:=by
 rw [revoke]; let s:=T.s; let b:=(assembly n).embed T.b; let U:Config SU.group (More n):= Lattice.pull s b U₀ -- Config ns.
 let Z:=shiftFaces s b; have hx(i:Cell (More n)):Pressure.toll ((polarT T.charge) ∘ U) i=Pressure.toll U₀ (Z i):=by
    have he: Pressure.toll U i=Pressure.toll U₀ (Z i):=Face.send_price U₀ i s b _ SU.group.chord_inv fun u w=> SU.group.chord_conj w u
    cases h:T.charge; exact he; exact (Rink.mint_b U i).trans he
 have ht(i:Cell (More n)): touched i=actY T (touched (Z i)):=by
    rw [actY,show touched (Z i)=(touched i).map (boxA T).toEmbedding from ?_]; ext j; simp
    rw [map_eq_image]; refine Eq.trans (Work.H03.touched_send s b i) ?_; refine image_congr fun x _=> (sitA ..).symm
 constructor
 · intro p i g; obtain ⟨i,rfl⟩:=Z.surjective i; change Pressure.toll _ _< _; rw [←hx]; apply p; rw [ht]; exact fun u=> g (Finset.disjoint_map _|>.mp u)
 intro p i g; change Pressure.toll ((polarT T.charge) ∘ U) i <_; rw [hx]; rw [ht] at g; exact p (Z i) fun u=>g (Finset.disjoint_map _|>.mpr u)
lemma lights_C: flashA T U₀∈Rue.litres t (actY T D) (actY T A') ↔ U₀∈Rue.litres t D A':=by
 unfold Rue.litres; simp only [Set.mem_setOf]; rw [←show actY T (D\A')=actY T D \ actY T A' from map_sdiff ..,glowA, flagsA]; exact and_congr_right fun _=> map_subset_map
lemma lights_V : Rue.Gates (Rue.litres t (actY T D) (actY T A')) (actY T D) (flashA T U₀) ↔ Rue.Gates (Rue.litres t D A') D U₀:=by
 constructor
 · rintro ⟨U,v,p⟩; obtain ⟨Z,rfl⟩:=(show Surjective (flashA T) from fun x=> ⟨flashA T⁻¹ x, by rw [lights,inv_mul_cancel,rev1]⟩) U; refine ⟨Z,(lights_C ..).mp v,?_⟩; let f:=T⁻¹; have he:Agrees D (flashA T⁻¹ (flashA T U₀)) (flashA T⁻¹ (flashA T Z)):=flashD f _ _ D (show Agrees _ _ _ from by unfold f; rw [sitU]; exact p); rwa [revB,revB] at he
 rintro ⟨X,u,p⟩; refine ⟨flashA T X,(lights_C ..).2 u, flashD T _ _ _ ?_⟩; rw [show (actY T D).map (boxA T).toEmbedding=D from by ext; simp [actY]]; exact p
end YM.CF.Salt
