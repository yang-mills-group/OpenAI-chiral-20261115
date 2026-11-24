import YM.CF.Lich.Venus
import YM.CF.Cloak.Quest
import YM.CF.Yaw.Quartz
import YM.CF.Siete.Lights
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Iva
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
variable {N P B:Side}{G:Ratio (mid N B) (mid P B)}{S:StepData (Domain N B) (Domain P B)}{x β R e a b:ℝ} {n m l k:ℕ}
local notation "G₅"=> SU.group
variable{T:Tube G₅ S}(Z:Muster G S x e T)(M:Monk G₅ S){w t u C D:ℝ}
local notation "l_"=> Z.post
local notation "q_"=> Z.trot
local notation "Ba"=> radiusB x
local notation "Wa"=> (fun y=>M.atop y x)
local notation "W"=> M.sent x T q_ Z.room l_ Z.beta
lemma probe_nil{A:Type}[NormedAddCommGroup A][NormedSpace ℝ A]{x:A} (h:1≤u): Cloak.Probe (fun _:A=>(1:ℝ)) x u k:=by
 refine ⟨Jet.allows_const x (norm_one.trans_le h),fun _=>?_⟩; simp only [sub_self]; exact Jet.allows_const x norm_zero.le
open Next.Fluctuations
lemma stamp_b (i:Bond (Domain P B))(v:∃ j∈ (locals M.key M.key x M.park ((Z.loft+104)*Ba))ᶜ,j.val.val=i):portF Z M w t (.inr (.inr i))= Next.SectorChange.broad q_ Z.room (M.rich x T q_ Z.room l_ Z.beta v.choose):=by
 dsimp only [portF, Sum.elim_inr,Lich.Muster.boon]; rw [dif_pos v]; rfl
lemma steal_b (i:Bond (Domain P B))(v:¬∃ j∈ (locals M.key M.key x M.park ((Z.loft+104)*Ba))ᶜ,j.val.val=i):portF Z M w t (.inr (.inr i))=1:=by dsimp only [portF, Sum.elim_inr,Lich.Muster.boon]; rw [dif_neg v]
lemma probes (U V H L:ℝ)(p:1 ≤ L)(h:U≤L)(hV:V ≤ L)(hH:H≤L)(hp:∀ i:Cell _,Cloak.Probe (fun x'=> tokenF M.key q_ x ((Wa x').sent x T q_ Z.room l_ Z.beta) i) 0 U k)(ht:∀ i:Bond (Domain N B), Cloak.Probe (fun t'=>tidal M.key x w t q_ ((Wa t').sent x T q_ Z.room l_ Z.beta) (Wa t'|>.V) M.k i) 0 V k)(hv:∀ i: Active M.key x M.park, Cloak.Probe (fun u=>Next.SectorChange.broad q_ Z.room ((Wa u).rich x T q_ Z.room l_ Z.beta i)) 0 H k):∀ i:Sat S,Cloak.Probe (fun t'=>portF Z (Wa t') w t i) 0 L k:=by
 rintro (i|i|i)
 · let X:=nearFace S (M.key.dome ((Z.loft+110)*Ba)); by_cases v:i∈ Xᶜ
   · rw [show (fun x'=>portF Z (Wa x') w t (.inl i))=fun x'=> tokenF M.key q_ x ((Wa x').sent x T q_ Z.room l_ Z.beta) i from funext fun x'=>if_pos v]; exact ⟨(hp i).pays.mono h,(hp i).flat⟩
   rw [show (fun x'=>portF Z (Wa x') w t (.inl i))=fun _=>1 from funext fun x'=>if_neg v]; exact probe_nil p -- tune inferred motive
 · let Y:= nearNoise (M.key.dome ((Z.loft+100)*Ba)); by_cases v:i∈Yᶜ
   · rw [show (fun t'=>portF Z (Wa t') w t (.inr (.inl i)))=fun t'=>tidal M.key x w t q_ ((Wa t').sent x T q_ Z.room l_ Z.beta) (Wa t'|>.V) M.k i from funext fun x'=>if_pos v]; exact ⟨(ht i).pays.mono hV,(ht i).flat⟩
   rw [show (fun x'=>portF Z (Wa x') w t (.inr (.inl i)))=fun _=>1 from funext fun x'=>if_neg v]; exact probe_nil p
 let C:= locals M.key M.key x M.park ((Z.loft+104)*Ba); let Y :Prop:= ∃ j∈ Cᶜ,j.val.val=i; by_cases v:Y
 · rw [show (fun t'=>portF Z (Wa t') w t (.inr (.inr i)))=fun t'=>Next.SectorChange.broad q_ Z.room ((Wa t').rich x T q_ Z.room l_ Z.beta v.choose) from funext fun x0=>stamp_b Z (M.atop x0 x) i v]; exact ⟨(hv v.choose).pays.mono hH,(hv v.choose).flat⟩
 rw [show (fun x'=>portF Z (Wa x') w t (.inr (.inr i)))=fun _=>1 from funext fun x0=>steal_b Z (M.atop x0 x) i v]; exact probe_nil p
local notation "oracle" => Siete.gateX G₅ S.patch.L l_ n x u
open Siete PhysicalNext.JointLoad
lemma late_l (V V':BudgetPoint)(v:V.threshold=temp x)(hv:V'.threshold=fiery G₅ x S.patch.L)(h:M.key.flags=RG.flags V.threshold M.V)(u_:‖M.z‖ ≤ oracle)(hq: Cloak.readyJ M T q_ l_ x Z.room t Z.beta w)(hx:1000 ≤Ba)(hk:l_ ≤ Z.loft)(hL:∀ i:Site (Domain P B),∀ Y:Support (Domain N B),Healthy V.threshold Y M.V→∀ (H:Heir.Museum M.park x M.key {i} Y (PlaceZ M.park {i} M.key x)), (∀ j∈coZ H,‖(M.bell x) j‖ ≤ Siete.gateX SU.group S.patch.L Z.post n x u) → Dawn V V' i {i} Y M.V (recent T Z.beta M.k Z.trot Z.room Z.post M.U (M.bell x)) k l_ T S.patch.L R a b):∀ i:Sat S,portF Z M w t i=1:=by
 rintro (i|i|i)
 · let A:= nearFace S (M.key.dome ((Z.loft+110)*Ba)); unfold portF; simp only [Sum.elim_inl]; split
   next v =>
     let o:=S.ratio.parent i.1; let Y:= Lattice.halo (90*radiusB x) {o}; let X:Support (Domain P B):={i.1}; have he:Disjoint (startPos S i) (M.key.dome ((Z.loft+110)*Ba)):=not_not.mp fun p=> mem_compl.mp v (mem_filter.mpr ⟨mem_univ _,p⟩); have hz:o∈ startPos S i:= mem_image_of_mem _ (Work.E01.base_touched i)
     have hu:Disjoint M.key.place Y:=by apply disjoint_left.mpr; intro z p t; obtain ⟨a,l,w⟩:= halo_spec.mp t; rw [mem_singleton.mp l] at w; exact disjoint_left.mp he hz (halo_spec.mpr ⟨z,p,(separation_comm ..).trans_le (by simp_rw [Nat.add_mul]; omega)⟩)
     have hP(p:Site (Domain P B))(hp:p∈inspected X): halo (Heir.reach x+4) {S.ratio.parent p} ⊆ Y :=by
        apply aroundBk _ (show Beat.shadows (o:=o) Y _ from Subset.refl _); have hh:=Work.E04.parent_separation S.ratio i.1 p; obtain ⟨z,l,u⟩:= halo_spec.mp (Yaw.touchK _ hp); rw [mem_singleton.mp l] at u; unfold Heir.reach o; omega
     have ht:= (hL i.1 Y (Disjoint.mono_right (by rw [←h]; exact subset_union_right) hu.symm) (museZ X Y M.park M.key x hu hP) (fun x p=> (norm_le_pi_norm M.z x.val.val).trans u_)).hi -- binder
     have hh:Healthy (fiery G₅ x S.patch.L/4) {i.1} W:= by rw [hv] at ht; exact ht
     unfold tokenF AnalyticBridge.Annulus1AD.profile; rw [if_neg]; apply Cloak.token_g _ _ (SU.group.chord_nonneg _); · apply le_of_not_gt; intro z; exact disjoint_left.mp hh (mem_singleton_self _) ((flags_spec ..).mpr ⟨i,Work.E01.base_touched _,z⟩)
     · rw [←hv]; exact div_pos (V'.threshold_pos) (by norm_num)
     exact fun g=> disjoint_left.mp he hz (halo_subset _ _ (mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨i,g,hz⟩))))
   rfl
 · unfold portF; simp only [Sum.elim_inr,Sum.elim_inl]; split
   next v=> exact hq.1 i fun z=>mem_compl.mp v (mem_filter.mpr ⟨mem_univ _,fun t=>disjoint_left.mp t (mem_insert_self ..) ((farther (Nat.mul_le_mul_right _ (by omega))) z)⟩)
   rfl
 unfold portF Lich.Muster.boon; simp only [Sum.elim_inr]; split
 next v=> exact hq.2 v.choose fun z=> mem_compl.mp v.choose_spec.1 (mem_filter.mpr ⟨mem_univ _, Or.inl (farther (Nat.mul_le_mul_right _ (by omega)) z)⟩)
 rfl
end YM.CF.Iva
