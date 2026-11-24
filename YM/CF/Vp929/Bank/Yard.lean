import YM.CF.Lilt.Chord
import YM.CF.Pso.Velt
import YM.CF.Vp929.Bank.Tail
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Plume.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Tarn Cay Slate Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Appel.Rate Lilt Girt
open scoped Topology ContDiff BigOperators InnerProductSpace NNReal ENNReal Classical
variable {N P B:Side} (S:StepData (Domain N B) (Domain P B)) {E:Type}
local notation "G₀"=> SU.group
local notation "Co"=> SU.group.Color
local notation "Fx"=> Domain P B
local notation "A_"=> Bond (Domain P B)
local notation "Ω"=> Cord S
abbrev yard (S:StepData (Domain N B) Fx) (μ:A_→ Measure Co):= silk S (Measure.pi μ)
local instance : IsProbabilityMeasure (Girt.suit S):= by unfold Girt.suit; infer_instance
abbrev Brink (S:StepData (Domain N B) Fx) (h:ℝ):Set (Cord S):={x|Fairy S h x}
instance yard_prob (μ:A_→ Measure Co)[∀ i,IsProbabilityMeasure (μ i)]: IsProbabilityMeasure (yard S μ):= by unfold yard silk; infer_instance
variable {S}
-- link law map
private abbrev rope (f:A_→ Co→ Co) (x:Cord S):= Lilt.zBox x (fun i=> f i (x.2.1.2 i))
section ledger
variable (μ ν:Bond (Domain P B)→ Measure Co)
lemma rope_mp [∀ i,IsProbabilityMeasure (μ i)][∀ i,IsProbabilityMeasure (ν i)] (f:A_→ Co→ Co)(hf:∀ i,MeasurePreserving (f i) (μ i) (ν i)): MeasurePreserving (rope f) (yard S μ) (yard S ν) :=
 by
 haveI : SigmaFinite (Girt.suit S):=by unfold Girt.suit; infer_instance
 haveI : SFinite (Girt.suit S):= by infer_instance
 exact (MeasurePreserving.id _).prod (((MeasurePreserving.id _).prod (measurePreserving_pi μ ν hf)).prod (MeasurePreserving.id _))
variable (L:Support (Domain N B))
def booths (L:Support (Domain N B))(S:StepData (Domain N B) Fx): Finset A_:= univ.filter fun i=> S.ratio.parent i.1∈ L
def Ground (S:StepData (Domain N B) Fx)(L:Support (Domain N B)) (μ ν:A_→ Measure Co)(i:A_):Measure Co:= if i∈ booths L S then μ i else ν i
instance ground_p [∀ i,IsProbabilityMeasure (μ i)][∀ i,IsProbabilityMeasure (ν i)] (i:A_) : IsProbabilityMeasure (Ground S L μ ν i):=by unfold Ground; split <;> infer_instance
lemma yard_reset_mp [∀ i,IsProbabilityMeasure (μ i)]: MeasurePreserving (fun x:Cord S=> yearT x L) (yard S μ) (yard S (Ground S L μ fun _=> Measure.dirac 0)):= by
 apply rope_mp μ _ (fun i x=> if S.ratio.parent i.1∈L then x else 0)
 intro i; unfold Ground; simp only [booths, mem_filter,mem_univ,true_and]; split
 · rename_i h; exact MeasurePreserving.id _
 rename_i h; exact ⟨measurable_const,by simp⟩
lemma ground_m (L:Support (Domain N B)):Measurable (fun x:Cord S=>yearT x L):= (yard_reset_mp (fun _=>Measure.dirac 0) L).measurable
lemma text_roots (L:Support (Domain N B))(x:Cord S) {u:ℝ}(hp:0 ≤ u): textP L x u ↔ Fairy S u (yearT x L) := by
 -- with u≥0
 refine ⟨fun h=>postB x L u h hp,?_⟩; intro h i p; rw [←(show (yearT x L).2.1.2 i=x.2.1.2 i from if_pos p)]; exact (norm_le_pi_norm _ i).trans h
lemma laid [NormedAddCommGroup E] [NormedSpace ℝ E] [∀ i,IsProbabilityMeasure (μ i)][∀ i,IsProbabilityMeasure (ν i)] (f:Cord S→E) (h: StronglyMeasurable f) (p:∀ x:Cord S, f x=f (yearT x L)):
    (∫ x,f x ∂yard S μ)=(∫ x,f x∂yard S (Ground S L μ ν)) := by
 let g(x:Cord S):=yearT x L; let B:= fun _:A_=>Measure.dirac (0:Co); let U (μ:A_→Measure Co) [∀ i,IsProbabilityMeasure (μ i)] : MeasurePreserving g (yard S μ) (yard S (Ground S L μ B)):= yard_reset_mp μ L
 have T (μ:A_→Measure Co) [∀ i,IsProbabilityMeasure (μ i)]: (∫ x,f x∂yard S μ)=∫ x,f x ∂yard S (Ground S L μ B):= by
   rw [← (U μ).map_eq, integral_map (U μ).measurable.aemeasurable h.aestronglyMeasurable]; exact integral_congr_ae (Eventually.of_forall p)
 rw [T μ,T (Ground S L μ ν),show Ground S L (Ground S L μ ν) B=Ground S L μ B from funext fun i=>by unfold Ground;split <;> rename_i h <;> simp [h]]
local notation "⌊" v "⌋" => yard S v
open Work
/-- Insert any factored real densities on inside links; no payment on spectator links. -/
theorem lay [∀ i,IsProbabilityMeasure (μ i)][∀ i,IsProbabilityMeasure (ν i)] (D:A_→ Co→ ℝ) (m:∀ i,Measurable (D i))(P:∀ i∈ booths L S, μ i=(ν i).withDensity (fun x=>ENNReal.ofReal (D i x))) :
    ⌊Ground S L μ ν⌋ = (yard S ν).withDensity (fun x=>∏ i∈ booths L S, ENNReal.ofReal (D i (x.2.1.2 i))) := by
 let F(i:A_)(x:Co):= if i∈ booths L S then ENNReal.ofReal (D i x) else 1
 have hm (i):Measurable (F i):= by by_cases h:i∈ booths L S <;> simp [F,h]; exact (m i).ennreal_ofReal
 have Q (i:A_) :(ν i).withDensity (F i)= Ground S L μ ν i:=by
   by_cases e:i∈ booths L S <;> simp [Ground,F,e]; exact (P i e).symm
 haveI V (i:A_):SigmaFinite ((ν i).withDensity (F i)):= Q i ▸ inferInstance
 have U(x:Directions G₀ Fx): (∏ i, F i (x i))= ∏ i∈ booths L S, ENNReal.ofReal (D i (x i)):=by
   rw [← prod_subset (subset_univ (booths L S)) (by intro i e h; simp [F,h])]; exact prod_congr rfl fun i h=> if_pos h
 let u(x: Directions G₀ Fx):=∏ i,F i (x i)
 have hu:Measurable u:= by unfold u; fun_prop
 let T (x:Config G₀ Fx × Directions G₀ Fx):= u x.2; let q:= suit S; let W(x:Cord S):= T x.2.1
 rw [show (fun x:Cord S=>∏ i∈ booths L S, ENNReal.ofReal (D i (x.2.1.2 i)))=W from funext fun x=>(U _).symm]; unfold yard silk; rw [show Ground S L μ ν=(fun i=>(ν i).withDensity (F i)) from (funext Q).symm,← F05.piDensity ν F hm, prod_withDensity_right hu,prod_withDensity_left (show Measurable (fun x:Config G₀ Fx × Directions G₀ Fx=> u x.2) from hu.comp measurable_snd)]; exact prod_withDensity_right ((hu.comp measurable_snd).comp measurable_fst)
local notation "D'[" x "]" => x
lemma rotate [NormedAddCommGroup E] [NormedSpace ℝ E] [∀ i,IsProbabilityMeasure (μ i)][∀ i,IsProbabilityMeasure (ν i)] (D:A_→ Co→ℝ) (m:∀ i,Measurable (D i)) (Q:∀ i∈ booths L S,∀ x, 0 ≤ D i x) (P:∀ i∈ booths L S, μ i=(ν i).withDensity (fun x=>ENNReal.ofReal (D i x))) (f:Cord S→E)(e:StronglyMeasurable f)(W:∀ x:Cord S, f x=f (yearT x L)):
   (∫ i,f i∂yard S μ)=(∫ i,(∏ j∈booths L S, D j (i.2.1.2 j)) • f i ∂yard S ν) := by
 rw [laid μ ν L f e W, lay μ ν L D m P, integral_withDensity_eq_integral_toReal_smul]
 · refine integral_congr_ae (Eventually.of_forall fun x=>?_); dsimp only; rw [← ENNReal.ofReal_prod_of_nonneg (by intro i v; exact Q _ v _),ENNReal.toReal_ofReal (prod_nonneg fun i v=> Q _ v _)]
 · exact Finset.measurable_fun_prod _ fun i _=> ((m i).comp ((measurable_pi_apply i).comp measurable_snd.fst.snd)).ennreal_ofReal
 exact Eventually.of_forall fun y=> (ENNReal.prod_ne_top (by intro i v; exact ENNReal.ofReal_ne_top)).lt_top
end ledger
lemma brink_m (v:ℝ):MeasurableSet (Brink S v):= measurableSet_le measurable_snd.fst.snd.norm measurable_const
abbrev posed (S:StepData (Domain N B) Fx) (t h:ℝ):Measure (Cord S):= yard S (fun i=> pitched SU.group t h)
variable {t h:ℝ}(ht:0<t)(hp:0<h)
include ht hp
lemma posed_mp: MeasurePreserving (dilC S ht).symm (plummy S (t*h)) (posed S t h):= by
 haveI:= feast_nn G₀ (mul_pos ht hp); haveI:=pitched_p (G:=G₀) ht hp; exact rope_mp (μ:=fun i=>feast G₀ (t*h)) (ν:=fun i=> pitched G₀ t h) _ (fun _=>pitched_mp_map)
lemma posed_p: IsProbabilityMeasure (posed S t h):= by haveI:=pitched_p (G:=G₀) ht hp; unfold posed; infer_instance
omit hp in
lemma brink_d (x:Cord S): dilC S ht x∈ Brink S (t*h) ↔ x∈ Brink S h:= by change ‖t • x.2.1.2‖ ≤ _ ↔ ‖_‖ ≤ _; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.le, mul_le_mul_iff_right₀ ht]
lemma posed_ae: ∀ᵐ x∂posed S t h,x∈ Brink S h:= by
 rw [← (posed_mp ht hp).map_eq]; refine (ae_map_iff (μ:=plummy S (t*h)) (posed_mp ht hp).measurable.aemeasurable (brink_m (S:=S) h)).2 (?_)
 filter_upwards [tone_p (S:=S) (mul_pos ht hp)] with x hx; apply (brink_d ht _).mp; rw [MeasurableEquiv.apply_symm_apply]; exact hx
end YM.CF.Plume.Rate
