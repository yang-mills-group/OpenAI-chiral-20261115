import YM.CF.Oise.Held
import YM.CF.Stake.Loom
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oise
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
section
open Scroll Yaw Eire Girt
open Lich.Muster Vol
variable {N P B C:Side} {m k j:ℕ}{ι:Type}[MeasurableSpace ι] (V:ι→ Config SU.group N)(h:Measurable V){T:ℝ}
lemma tax_m(i:Cell N) :Continuous fun U: Config SU.group N=>toll U i:=SU.group.continuous_chord.comp (by unfold faceValue; fun_prop)
lemma mast_f {T:Type}[Countable T](X:ι→ T→Prop)(p:∀ i,MeasurableSet {x| X x i}): MeasurableSet {x|∀ i,X x i}:= Set.setOf_forall _ ▸ (show MeasurableSet (⋂ i,{x| X x i}) from MeasurableSet.iInter p)
lemma imp_m (p:Prop){h:ι→Prop}(hp:MeasurableSet {x|h x}):MeasurableSet {x|p→h x}:=by by_cases t:p;simp [t,hp]; simp [t]
include h
lemma pers_m (A:Clip)(i:Site N)(S: Finset (Cell N)): MeasurableSet {x| Esti.pers S A T (V x) i}:= by unfold Esti.pers; apply mast_f; intro i; exact imp_m _ (measurableSet_le ((tax_m i).measurable.comp h) measurable_const)
lemma peer_m (S:Support N)(K:Finset (Cell N)):MeasurableSet {x| Cloak.polP T (V x) S K}:= by unfold polP; apply mast_f; intro i; exact imp_m _ (measurableSet_le ((tax_m i).measurable.comp h) measurable_const)
lemma shut_m (q:Chi)(A: Finset (Cell N)): Measurable fun x=> Esti.shutters q T A (V x):= Finset.measurable_prod A fun i _=> q.smooth.continuous.measurable.comp ((((tax_m i).measurable.comp h).div_const T).pow_const (2:ℕ))
lemma park_m (I:Atom SU.group k)(s:Finset (Cell N))(q:Chi)(i:Site N): Measurable (fun x=> lush_k q I s T i (V x))∧ Measurable (fun x=> peer_k I s T i (V x)):=by
 let X:= I.footprint i; have hp : Measurable fun x=> I.unmasked (V x) i:=(I.unmasked_cont i).measurable.comp h; have ht:Measurable fun x=> Cloak.east q X s T (V x):= Measurable.ite (peer_m V h _ _) (shut_m V h q (Cloak.costA X\s)) measurable_const; exact ⟨ht.mul hp,Measurable.ite (peer_m V h _ _) hp measurable_const⟩
lemma hall_m (I:Atom SU.group k)(s: Finset (Cell N))(A:Clip)(i:Site N): Measurable (fun x=>Cloak.sleeve I s A i T (V x)):= Measurable.ite (pers_m V h A i s) ((I.unmasked_cont i).measurable.comp h) measurable_const
lemma plot_m (I: BudgetPoint)(X:PathData SU.group)(Z: Finset (Cell N))(T:Clip){σ C D:ℝ}(p:X.Bounds T σ C D)(k j:ℕ)(i:Cell N) : Measurable fun x=> Esti.king Z X T k j I.threshold (V x) i:=by
 let Y:=fun x=> toll (V x) i; have he:Measurable Y:=(tax_m i).measurable.comp h; have ht:Measurable fun x:ι=> Esti.hallP Z T (V x) i I.threshold:=by
    unfold Esti.hallP; split; · exact Measurable.ite (measurableSet_le he measurable_const) ((measurable_const.mul (he.pow_const (2:ℕ))).div_const _) (measurable_const.mul he)
    exact (continuous_const.mul (SU.group.continuous_price.comp (f:=fun V:Config SU.group N=>faceValue V i) (by unfold faceValue; fun_prop))).measurable.comp h
 have hp:Measurable (fun v=> Esti.taken Z X T k j I.threshold (V v) (i,true)):= by simp_rw [Esti.taken]; simp only [if_true]; exact Measurable.ite (pers_m V h _ _ _) ((plotted_cont p k j (i,true)).measurable.comp h) measurable_const
 exact ht.add ((hp.norm.pow_const (2:ℕ)).div_const _)
omit h
variable {S: StepData (Domain N B) (Domain P B)}{T':Tube SU.group S} {G:Ratio (mid N B) (mid P B)} {x e:ℝ}(H:Muster G S x e T')(M:ι→ Monk SU.group S)(A:Stores S)
-- syntax validity not needed
lemma walkZ(L: Unit)(X:Palot.leaf (Site (Domain N B)))(N':ℕ→Palot.leaf (Site (Domain N B)))(C:ℕ→ι→ℝ)(h:∀ i,Measurable (C i)):Measurable fun x=> Lich.Muster.crop X N' (fun i=>C i x):=by apply Measurable.tsum; intro i; split; exact h _; exact measurable_const -- crop only Domain N B
local notation "N0" => Domain N B
local notation "P0" => Domain P B
local notation "H1" => fun i=> (M i).sent x T' H.trot H.room H.post H.beta
local notation "H2" => H.phaseUp
local notation "H3"=> H.phaseLow
variable (p:∀ i,(M i).key=A)(hF: Measurable fun i=> (M i).V)(q: Measurable fun i=> (M i).sent x T' H.trot H.room H.post H.beta) -- binder notation
include hF q p A
lemma shards(i:Palot.leaf (Site (Domain N B)))(k:ℕ): Measurable fun x'=> shardy H (M x') k i:=by
 unfold shardy averaged; refine (measurable_const.mul (Finset.measurable_sum _ fun s _=>Measurable.sub (Finset.measurable_sum _ fun n _=>?_) (Finset.measurable_sum _ fun n _=>?_))).neg
 · let V(x'):= pull s 0 ((M x').sent x T' H.trot H.room H.post H.beta); have hV:Measurable V:=(Wilson.continuous_pull ..).measurable.comp q; unfold Muster.river extU sapU; simp_rw [p]
   have he{k:ℕ}(X:ℕ→Atom SU.group k)(D:ℕ→Palot.leaf (Site (Domain N B))): Measurable fun u=>crop i D (fun j=>lush_k H.trot (X j) (turnStore s A).costs H.phaseUp.threshold n (V u)):= walkZ () i _ _ fun j=> (park_m V hV _ _ _ _).1
   exact (measurable_const.mul ((walkZ () i _ _ fun j=> hall_m V hV _ _ _ _).add ((he _ _).add (he _ _)))).add (he _ _)
 let V(x'):= pull s 0 ((M x').V); have hV:Measurable V:=(Wilson.continuous_pull ..).measurable.comp hF; unfold Lich.Muster.flows extV sapC; simp_rw [p]; let P:= traceZ (turnStore s A).flags; have he{k:ℕ}(X:ℕ→Atom SU.group k)(D:ℕ→Palot.leaf (Site (Domain N B))): Measurable fun u=>crop i D (fun j=>peer_k (X j) P H.phaseLow.threshold n (V u)):= walkZ () i _ _ fun j=> (park_m V hV _ _ H.trot _).2
 exact ((measurable_const.mul ((walkZ () i _ _ fun j=> hall_m V hV _ _ _ _).add ((he _ _).add (he _ _)))).add (he _ _)).add (measurable_const.mul ((he _ _).add (he _ _)))
end
end YM.CF.Oise
