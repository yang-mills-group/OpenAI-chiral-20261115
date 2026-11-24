import GaugeFieldConstruction.HopeQ
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 100000
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
variable {I:Type}[LinearOrder I][Fintype I]{N B:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]{p: BudgetPoint}
variable (σ:I→ Seat (mid N B))(C:I→ I→ℂ)
abbrev TurnArc (F:Key I→ E):= Fluid σ (streamArc F σ C)
variable {F G:Key I→E}
lemma Arc_cong (t:Set.EqOn F G (hill I))(p:River F):TurnArc σ C F=TurnArc σ C G:=by
 have hu:= River.cong p t.symm; funext i; refine sum_congr rfl fun j v=>congrArg (_ • ·) ?_
 rw [fluid_Z _ _ F p j v,fluid_Z _ _ G hu j v]; exact rer _ _ _ (fun k _=>lace_C k t roots) -- tune
lemma Arc_const (E':E) : TurnArc σ C (fun _=> E')=fun _=>E':=by
 funext i; unfold TurnArc Fluid; rw [sum_eq_single_of_mem (s:=realm_C σ) (∅:Finset I) (mem_filter.mpr ⟨mem_univ _,by simp⟩)]; · rw [empty_Φ _ _ _ (zeroR _)]; unfold Mew.pine; rw [Finset.prod_empty, one_smul]
 intro j v p; rw [fluid_Z _ _ _ (zeroR _) _ v, ← constant_C σ C (s:=Mew.Cue I j) E' _ (List.Sublist.refl _)]; suffices he:tipI (fun _:Key I=>E') (Mew.Cue I j)=0 by rw [he,smul_zero]
 cases e: Mew.Cue I j with
 | nil=>have he: 0=j.card:= (congrArg List.length e).symm.trans (length_sort ..); exact False.elim (p (card_eq_zero.mp he.symm))
 | cons i l=>exact Roots.proper ..
lemma Arc_add (p: River F)(g:River G): TurnArc σ C (fun x=>F x+G x)= TurnArc σ C F+TurnArc σ C G:=by
 funext i; unfold TurnArc; rw [Pi.add_apply]; unfold Fluid; rw [←sum_add_distrib]; apply sum_congr rfl; intro j v; rw [←smul_add]; apply congrArg
 rw [fluid_Z _ _ _ (dub_V p g) _ v,fluid_Z _ _ F p j v,fluid_Z _ _ G g j v]; exact (rer σ C (Mew.Cue I j) fun i _=>tip_A p g _).trans (tally_ADD σ C _ _ _)
lemma Arc_Y {A:Type*}(T:Finset A)(F:A→ Key I→ E)(u:∀ i∈T,River (F i)): TurnArc σ C (fun z=>∑ i∈T,F i z)= ∑ i∈T,TurnArc σ C (F i):=by
 induction T using Finset.induction_on with
 | empty=> simp_rw [sum_empty]; exact Arc_const ..
 | @insert i t h ih=>
    have ht(j)(v:j∈t):= u j (mem_insert_of_mem v)
    simp_rw [sum_insert h]; rw [Arc_add σ C (u i (mem_insert_self ..)) (tip_bank t F ht).1,ih ht]
lemma Arc_map {T:Type}[NormedAddCommGroup T][NormedSpace ℂ T][CompleteSpace T](L:E→L[ℂ] T)(p:River F) : TurnArc σ C (L ∘ F) = L ∘ TurnArc σ C F:=by
 funext i; unfold TurnArc Fluid; rw [Function.comp_apply,map_sum]; apply sum_congr rfl; intro j v; rw [map_smul]; refine congrArg (fun x=>_ • x) ?_
 rw [fluid_Z _ _ _ (sc_V p _) _ v,fluid_Z _ _ _ p _ v]; exact (rer σ C _ (fun _ _=>sim_H p L _ roots)).trans (tally_l ..)
section
abbrev BusW (W:Key I→Vow.Pax (mid N B))(x:Finset I): Vow.Pax (mid N B):=Boats σ C W x
abbrev BusQ (Q:Key I→Vow.Cusp (mid N B))(x:Finset I): Vow.Cusp (mid N B):=fun i u p=> Boats σ C (fun z=>FlatQ (Q z)) x i (u,p)
lemma Bus_Q (Q:Key I→Cusp (mid N B))(x:Key I)(V:Aura (mid N B))(U:Support (Domain N B))(p:Orbit (mid N B)): WritV σ (BusQ σ C Q) x V U p= TurnArc σ C (fun z=>Q z V U p) x:=by
 unfold WritV; simp_rw [Finset.sum_apply]; rfl
lemma Bus_w (W:Key I→Vow.Pax (mid N B))(x:Key I)(V:Aura (mid N B))(p:Orbit (mid N B)):WritV σ (BusW σ C W) x V p=TurnArc σ C (fun z=>W z V p) x:=by unfold WritV; simp_rw [Finset.sum_apply]; rfl
lemma BurnX (T:Key I→RegBudget (mid N B))(u:∀ i v,River (fun z=> T z i v))(P: BudgetPoint)(X:Pane (mid N B)) :let F (z:Key I):=exponentL P (T z) X; River F ∧ TurnArc σ C F=fun z:Key I=>exponentL P (WritV σ (Bus1 T σ C) z) X :=by
 intro F; let Bb(i:Scree.Hub (mid N B)) (z:Key I):=numbE P.threshold i.val.2 (T z i) X
 have hR(i:Scree.Hub (Scree.mid N B)):River (Bb i):=by
    by_cases p: pingS P.threshold i.val.2 X; · unfold Bb numbE; simp_rw [Set.indicator_of_mem (show X∈{X|pingS P.threshold i.val.2 X} from p)]; exact u i X
    unfold Bb numbE; simp_rw [Set.indicator_of_notMem (show X∉{X|pingS P.threshold i.val.2 X} from p)]; exact zeroR _
 refine ⟨(tip_bank (univ) _ (fun i _=>hR i)).1,?_⟩
 rw [show F=fun z=>∑ i:Scree.Hub (mid N B), Bb i z from rfl,Arc_Y σ C univ Bb (fun i _=>hR i)]; funext i; rw [Finset.sum_apply]; unfold exponentL; apply sum_congr rfl; intro j _; by_cases p: pingS P.threshold j.val.2 X; · unfold Bb numbE; simp_rw [Set.indicator_of_mem (show X∈{X|pingS P.threshold j.val.2 X} from p)]; exact (bus_P ..).symm
 unfold Bb numbE; simp_rw [Set.indicator_of_notMem (show X∉{X|pingS P.threshold j.val.2 X} from p)]; rw [Arc_const]
lemma BurnW (W:Key I→Vow.Pax (mid N B))(u:∀ i v,River (fun z=>W z i v))(P: BudgetPoint)(X: Orbit (mid N B)) :let F(z:Key I):=coldE P (W z) X; River F ∧ TurnArc σ C F=fun z:Key I=>coldE P (WritV σ (BusW σ C W) z) X:=by
 intro F; refine ⟨(tip_bank _ _ (fun i _=>u i X)).1,?_⟩; unfold F coldE; rw [Arc_Y _ _ _ (fun i z=>W z i X) (fun i _=>u i X)]; funext x; rw [Finset.sum_apply]; apply sum_congr rfl; intro i _; exact (Bus_w ..).symm
lemma BurnQ (Q:Key I→Cusp (mid N B))(u:∀ i D v,River (fun z=>Q z i D v))(P:BudgetPoint)(X:Orbit (mid N B)):let F(z:Key I):=fuelV P (Q z) X; River F ∧ TurnArc σ C F=fun z:Key I=>fuelV P (WritV σ (BusQ σ C Q) z) X:=by
 intro F; let D:= flags P.threshold X.1; refine ⟨(tip_bank _ _ (fun i _=>u i (D∩i.val) X)).1,?_⟩; unfold F fuelV; rw [Arc_Y _ _ _ (fun i z=>Q z i (D∩i.val) X) (fun i _=>u i _ X)]; funext x; rw [Finset.sum_apply]; apply sum_congr rfl; intro i _; exact (Bus_Q ..).symm
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
