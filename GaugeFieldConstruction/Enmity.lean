import GaugeFieldConstruction.Ovation
import YM.CF.Roots.East
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
variable {I:Type}[LinearOrder I][Fintype I]{J:Type}[DecidableEq J](σ:I→J)(C:I→ I→ℂ)
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]{s:List I}
abbrev Fluid (σ:I→J)(A:Finset I→ E)(z:Key I):= ∑ i∈ realm_C σ,Mew.pine i z • A i
lemma Fluid_p(A:Finset I→E)(p:ψS σ s): tipI (Fluid σ A) s=A s.toFinset:=by
 have hp:= tip_bank (realm_C σ) _ (fun i h=> lift_b i (A i)); rw [show Fluid σ A=(fun z=>∑ i∈realm_C σ,pine i z • A i) from rfl,hp.2]; simp_rw [tip_tape s (uS_b σ p)]; rw [Finset.sum_ite_eq]; exact if_pos (show s.toFinset∈realm_C σ from mem_filter.mpr ⟨mem_univ _,pays_z σ p⟩)
def streamArc (F:Key I→E)(σ:I→J)(C:I→I→ℂ): Finset I→ E:= fun i=>if i∈realm_C σ then gemI ((palm_R F σ) ∘ (toV_C σ C)) i else 0
lemma Ūm {s':Finset I}(h:s'∈realm_C σ): ψS σ (Mew.Cue I s'):=by
 let L:= Mew.Cue I s'; have H:L.Nodup:= s'.sort_nodup ..
 have H': L.toFinset=s':=by simp [L,Mew.Cue]
 have hx:(L.map σ).toFinset= s'.image σ:=by rw [←H']; ext i; simp
 change (L.map σ).Nodup; apply (Multiset.toFinset_card_eq_card_iff_nodup (m:=((L.map σ):Multiset J))).mp; change (L.map σ).toFinset.card=(L.map σ).length
 rw [hx,List.length_map, ←List.toFinset_card_of_nodup H, H',Finset.card_image_iff.mpr (mem_filter.mp h).2]
lemma stream_C (F:Key I→E)(u:River F)(p:ψS σ s) : Law_C σ C s F (Fluid σ (streamArc F σ C)):=by
 have he:Fluid σ (streamArc F σ C)=palm_R ((palm_R F σ) ∘ (toV_C σ C)) σ:=by
    funext z; unfold Fluid streamArc palm_R seedΞ; exact Finset.sum_congr rfl (fun i x=>by simp only [if_pos x])
 have hv:= κEmit σ C u p; rw [he]; refine ⟨u,(tip_bank (realm_C σ) _ fun i _=> lift_b i (gemI _ i)).1,fun i v=>?_⟩; exact (spark_U σ hv.1 ((v.map σ).nodup p)).trans (hv.2 i v)
lemma fluid_Z (F:Key I→E)(h:River F)(L:Finset I)(u:L∈realm_C σ):streamArc F σ C L= fuelΦ σ C F (Mew.Cue I L):=by unfold streamArc; rw [if_pos u]; exact (κEmit σ C h (Ūm σ u)).2 _ (List.Sublist.refl _)
lemma hush_z (S:Finset J)(F:Key I→E)(p:River F)(v:Hush σ S F)(i:I)(hx:i∈s)(q:σ i ∉ S):fuelΦ σ C F s=0:=by refine (rer σ C s (fun k t=>?_)).trans (women σ C s (E:=E)); obtain ⟨j,h,g⟩:= (List.mem_map.mp (show σ i∈k.map σ from t.symm ▸ List.mem_map_of_mem hx)); exact husht_B σ S F v p k j (by rwa [g]) h
abbrev TidyK (S:Finset J)(F:Finset I→E):Prop:=∀ i,F i≠0→i∈realm_C σ∧∀ j∈i,σ j∈ S
lemma stream_A (F:Key I→E)(S:Finset J)(p:River F)(v:Hush σ S F): TidyK σ S (streamArc F σ C):=by
 intro i h; have H:i∈realm_C σ:=Classical.not_not.mp fun p=>h (by unfold streamArc; rw [if_neg p]); refine ⟨H,fun j t=>Classical.not_not.mp fun e=>h ?_⟩; exact (fluid_Z σ C F p i H).trans (hush_z σ C S F p v j (by simpa [Mew.Cue] using t) e)
lemma empty_Φ (F:Key I→E)(h:River F): streamArc F σ C ∅=F 0:=by
 have he: ψS σ []:=by unfold ψS; simp
 rw [fluid_Z σ C F h ∅ (by exact pays_z _ he |> fun t=>mem_filter.mpr ⟨mem_univ _,by simpa using t⟩)]; unfold Mew.Cue; simp only [sort_empty]; rfl
lemma meta_one (i:I): ({i}:Finset I)∈realm_C σ:=mem_filter.mpr ⟨mem_univ _,show Set.InjOn σ _ from (by rw [coe_singleton]; exact Set.injOn_singleton _ _)⟩
lemma Dtip (F:Key I→E)(h:River F)(i:I): streamArc F σ C {i}=∑ j∈ Roots.pipe_ζ σ i,C j i • tipI F [j]:=by
 rw [fluid_Z σ C F h _ (meta_one σ i)]; unfold Mew.Cue; rw [Finset.sort_singleton]; unfold fuelΦ; rw [Roots.snow]; rfl
end
section
open CoeffArc
variable {N:Side}
abbrev Bus1 (F:Key I→ RegBudget N) (σ:I→J)(C:I→I→ℂ) (T:Finset I): RegBudget N:=fun i u=> streamArc (fun z=>F z i u) σ C T
abbrev Bus2 (F:Key I→ ForceBudget N)(σ:I→J)(C:I→I→ℂ) (T:Finset I): ForceBudget N:= fun i u=> streamArc (fun z=> F z i u) σ C T
abbrev WritV {E:Type}[AddCommMonoid E][Module ℂ E](F:Finset I→E)(x:Key I):=∑ i∈realm_C σ,Mew.pine i x • F i
lemma bus_P (F:Key I→ RegBudget N)(X:Scree.Hub N)(x:Pane N)(i:Key I): WritV σ (Bus1 F σ C) i X x=Fluid σ (streamArc (fun z=>F z X x) σ C) i:=by unfold WritV; simp_rw [Finset.sum_apply]; rfl
lemma bus_K (F:Key I→ ForceBudget N)(X:Force N)(x:Orbit N)(i:Key I): WritV σ (Bus2 F σ C) i X x=Fluid σ (streamArc (fun z=>F z X x) σ C) i:=by unfold WritV; simp_rw [Finset.sum_apply]; rfl
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
