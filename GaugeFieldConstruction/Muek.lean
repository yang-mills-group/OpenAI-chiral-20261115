import GaugeFieldConstruction.Ran
import GaugeFieldConstruction.Uber
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
set_option maxHeartbeats 240000
variable (I:Type)[LinearOrder I][Fintype I]
open SeasonH
variable (σ:I→Seat n)(V:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
variable (t:Finset I)(e:Vulcan I n)(S:Hubber n)(Q:Boke n I)
-- raw Lattice supports.Z cut zeta
variable (i:I)
abbrev Cull (Q:Boke n I) : Boke n I:= Q.filter fun e=>decide (e.keys=[i])
lemma Incζ_U : Incζ I σ {i} e ↔ e.keys=[i]:=by
 constructor
 · intro h; have k:= List.Nodup.of_map _ h.2; have ht:e.keys.length=1:=(List.toFinset_card_of_nodup k).symm.trans (by rw [h.1, card_singleton])
   rcases L:e.keys with _|⟨j,l⟩; simp [L] at ht
   rcases l with _|⟨g,l⟩; have hp:=h.1; rw [L] at hp; simp at hp; simp [hp]; simp [L] at ht
 intro h; constructor <;> simp [ψS,h]
lemma Cull_S :skimQ I σ {i} Q=Cull I i Q:=by unfold skimQ Cull; simp_rw [Incζ_U]
-- Availability when unique labels.Separate even if two at group.
variable (x:Scree.Hub n)
lemma sage_f (v: stabH F)(L:List I)(h:L.Nodup)(hs:stampK M L):Cull I i (Keeps F r M L)=if i∈ L then topL F r [] (M i) else []:=by
 have h0:∀Q:Boke n I,Cull I i Q=Cull I i (Q.filter SmallF):=by
    intro Q; induction Q with
    | nil=> rfl
    | cons a V ih=>
       unfold Cull at *; by_cases u:a.keys=[i] <;> by_cases w:SmallF a<;> simp [u,w,ih] <;> simp [SmallF,u] at w
 have hx(j:I)(h:j∈ L)(k)(t:k∈topL F r [] (M j)): k.keys=[j]:=by
    obtain ⟨x,g,s⟩:=List.mem_flatMap.mp t; exact grow_Stamp _ _ _ _ (hs j h x g) v j List.mem_cons_self k s
 rw [h0,Keep_sage r F M v L hs]
 unfold Cull
 -- induction as reverse. Use ih requires hy unaffected.
 induction L with
 | nil=> simp
 | cons j L ih=>
    have hh:stampK M L:= fun i u=> hs i (List.mem_cons_of_mem _ u)
    have hz:=List.nodup_cons.mp h; have hu:= ih hz.2 hh (fun j p=> hx j (List.mem_cons_of_mem _ p)) -- tune if order removed
    rw [List.reverse_cons,List.flatMap_append,List.flatMap_singleton,List.filter_append,hu]; by_cases w:j=i
    · subst j; rw [if_pos List.mem_cons_self,if_neg hz.1, List.nil_append]; exact List.filter_eq_self.mpr (fun l s=> decide_eq_true (hx i List.mem_cons_self l s))
    rw [List.filter_eq_nil_iff.mpr ?_,List.append_nil]; · split_ifs <;> first| rfl| next w0 h=>simp_all
    intro l k; simp [hx _ List.mem_cons_self l k,w]
lemma steam_K (q:darkH F)(U:Boke n I): foli (topL F r [] U)=(foli U).map (durW r):=by
 unfold foli topL; rw [filterA]; induction U with|nil=>rfl|cons i l h=> rw [List.filter_cons,List.flatMap_cons,h]; change foli (growL F r [] i)++_= _; rw [Pure_P r F i q]; split<;>simp -- tune uses by_cases
lemma dur_κ (Y:Vulcan I n): (durW r Y).seat=Y.seat ∧ PinInk (durW r Y)=PinInk Y:=by
 unfold durW; split; simp; exact ⟨rfl, rfl⟩
lemma foli_cull (V:Boke n I): Cull I i (foli V)=foli (Cull I i V):=by
 unfold Cull foli; rw [List.filter_filter,List.filter_filter]; apply List.filter_congr; intro i t; exact Bool.and_comm ..
lemma Ink_sageY (v:stabH F)(z:darkH F)(L:List I)(h:L.Nodup)(hs:stampK M L)(e:i∈L) : cacheS I σ {i} S (foli (Keeps F r M L))= Lee (pre_g I S (foli (M i))) PinInk:=by
 unfold cacheS; simp_rw [Cull_S,foli_cull,sage_f I M F r i v L h hs, if_pos e]; rw [steam_K _ F r z] -- tune order
 unfold pre_g; simp_rw [List.filter_map,show (fun q: Vulcan I n=> decide (q.seat=S))∘durW r = fun q=>decide (q.seat=S) from funext fun x=>by simp_rw [Function.comp_apply,(dur_κ I r x).1]]
 rw [mapA]; apply paidA; intro i _; exact (dur_κ I r i).2
#print axioms Ink_sageY
end MastTin
end YM.CF.XGarden
end
