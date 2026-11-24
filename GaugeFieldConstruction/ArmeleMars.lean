import GaugeFieldConstruction.TaloraMars
import GaugeFieldConstruction.StyriaRel.YM.Euclid.RPPeak
import GaugeFieldConstruction.StyriaRel.YM.Euclid.Pairing
/-!
 # complete formal derivative rows. Keep c and monomial prices explicit
# Extending RP values to tie configurations
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
-- directed reference masks paired without casts along append in downstream kernels
open NSF.Table.Pairing FirstPackMars
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C)(Y:AreaQc S)
local notation "T"=> BellTableMars p Y
variable (a:Axis)
open NSF.Table (PastTest)
open PlayArchiveMars
open scoped ComplexOrder
variable {p Y a}{J:Hilbert}(W:PlayArchiveMars p Y a J)
namespace PlayArchiveMars
variable (A:PatMars a n)(B:PatMars a m)(F:Fin n→ΧiMars)(G: Fin m→ΧiMars)
noncomputable def stitchπMars (x:Points n): J:= if h:x∈SimArchMars a n then W.emergeMars F ⟨x,h⟩ else 0
noncomputable def ImposeMars (x:Points n): J:= (A.test x:ℂ) • W.stitchπMars F x
lemma EraOfMars :ContinuousOn (W.stitchπMars F) (SimArchMars a n):= continuousOn_iff_continuous_restrict.mpr (by
 rw [show (SimArchMars a n).restrict (W.stitchπMars F)= W.emergeMars F from funext (fun x=> (by change W.stitchπMars F x.val=_; unfold stitchπMars; rw[dif_pos x.property]))]; exact (W.emergedMars F).1)
lemma FrameOfMars : support (W.ImposeMars A F)⊆ tsupport A.test:=by intro x hx; apply subset_closure; intro e; change A.test x=0 at e; exact hx (by unfold ImposeMars; rw [e,zero_smul])
lemma StageOfMars : Continuous (W.ImposeMars A F):=by
 apply continuous_iff_continuousAt.mpr; intro x; by_cases h:x∈SimArchMars a n
 · exact A.test.continuous.continuousAt.smul ((W.EraOfMars F x h).continuousAt ((openArchMars _ _).mem_nhds h))
 have ht:x∉tsupport A.test:= fun i=>h (A.east i); exact continuousAt_const.congr (((isClosed_tsupport _).isOpen_compl.eventually_mem ht).mono fun i p=>  Eq.symm (show W.ImposeMars A F i=0 from not_not.mp (fun y=>p (W.FrameOfMars A F y)))) -- maybe orientation
lemma DescentMars: Integrable (W.ImposeMars A F) := (W.StageOfMars A F).integrable_of_hasCompactSupport (A.test.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (W.FrameOfMars A F) (isClosed_tsupport _))) -- tune
noncomputable def PolePulseMars:J:= ∫ x,W.ImposeMars A F x
lemma PolePropMars (x:Points n)(y:Points m): inner ℂ (W.ImposeMars A F x) (W.ImposeMars B G y)=(PatentMars A B) (closedUp a x y)*TerraMars p Y (Fin.append (TurnupMars a ∘ F) G) (closedUp a x y) :=by
 rw [PatchHMars]; by_cases hx:x∈tsupport A.test; swap
 · rw [show W.ImposeMars A F x=0 from notMem_support.mp (fun u=> hx (W.FrameOfMars A F u)), image_eq_zero_of_notMem_tsupport hx]; simp
 by_cases hy:y∈tsupport B.test; swap
 · rw [show W.ImposeMars B G y=0 from notMem_support.mp (fun u=> hy (W.FrameOfMars B G u)), image_eq_zero_of_notMem_tsupport hy]; simp
 unfold ImposeMars stitchπMars; rw [dif_pos (A.east hx),dif_pos (B.east hy), inner_smul_left,inner_smul_right, W.emergentMars, mul_assoc]; rfl
lemma PulsePropMars : inner ℂ (W.PolePulseMars A F) (W.PolePulseMars B G)=(PatentMars A B).applyTo (TerraMars p Y (Fin.append (TurnupMars a ∘ F) G)):=by
 let f:= W.ImposeMars A F; let g:= W.ImposeMars B G; let y:=W.PolePulseMars B G; let Q:=PatentMars A B; let S:=TerraMars p Y (Fin.append (TurnupMars a ∘ F) G); let pIso:=pairIso (n:=n) (m:=m) a
 let V(q:Points n× Points m):= inner ℂ (f q.1) (g q.2)
 have he(x:Points (n+m)): V (pIso x)=Q x*S x:=by have h:= W.PolePropMars A B F G (pIso x).1 (pIso x).2; exact show _ from (by rwa [show closedUp a (pIso x).1 (pIso x).2=x from pIso.symm_apply_apply x] at h)
 have hv:Integrable V:= ((volume_split (n:=n) (m:=m) a).integrable_comp_emb pIso.toHomeomorph.measurableEmbedding).mp ((Q.smearing (TerraSm _ _ _).continuousOn).congr (Eventually.of_forall fun i=> (he i).symm))
 change inner ℂ (∫ x,f x) y= Q.applyTo S
 rw [show Q.applyTo S=∫ x,V x from ?_, MeasureTheory.Measure.volume_eq_prod, integral_prod V hv]; swap
 · rw [←MeasurePreserving.integral_comp (volume_split _ (n:=n) (m:=m)) pIso.toHomeomorph.measurableEmbedding V]; exact integral_congr_ae (Eventually.of_forall fun i=> (he i).symm)
 have ht(x:Points n):(∫ w:Points m,V (x,w))=inner ℂ (f x) y:= integral_inner (W.DescentMars B G) (f x)
 simp_rw [ht]; rw [← inner_conj_symm _ y,← integral_inner (W.DescentMars A F),← integral_conj]; apply integral_congr_ae; exact Eventually.of_forall fun i=> inner_conj_symm .. -- tune y/f
variable (Lk: FirstPackMars p Y)
noncomputable def BorePulseMars(Q:PastTest ΡeaderMars a)(v:LabelsMars (ArrangeT Q.n Q.v)):J:= PolePulseMars W (ChainBookMars (PstMars Q) (LedgerMars v)) (τCoreMars v)
lemma PatchPulseMars (Q V:PastTest ΡeaderMars a)(z: LabelsMars (ArrangeT Q.n Q.v))(w:LabelsMars (ArrangeT V.n V.v)): inner ℂ (W.BorePulseMars Q z) (W.BorePulseMars V w)= (withOther Q V).applyTo (fun x=> (BellTableMars p Y).read x (tied (TiesMars _ z) (TiesMars _ w) a)):=by
 unfold BorePulseMars; rw[PulsePropMars,← chainCutMars]
 simp_rw [TopsPayMars]; rfl
lemma paintTouchMars (t: Test n){I:Type*}(K:Finset I)(F:I→Points n→ℂ)(h:∀ i∈ K,ContinuousOn (F i) (conf n)): t.applyTo (fun x=> ∑ i∈K,F i x)=∑ i∈K,t.applyTo (F i):=by unfold Test.applyTo; simp_rw[mul_sum]; exact integral_finsetSum _ (fun i q=>t.smearing (h i q))
lemma stampTouchMars (t:Test n)(c:ℂ)(F:Points n→ℂ): t.applyTo (fun x=>c*F x)= c*t.applyTo F:=by unfold Test.applyTo; rw[← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun i=>mul_left_comm ..)
noncomputable def FrostMantaMars (Q:PastTest ΡeaderMars a):J:=∑ a:LabelsMars _, FeedTaxMars Q.v a • W.BorePulseMars Q a
include Lk
lemma FrostπMars (Q V:PastTest ΡeaderMars a): inner ℂ (W.FrostMantaMars Q) (W.FrostMantaMars V)= ∫ x,(BellTableMars p Y).smeared a Q V x:=by
 rw [← at_integral _ Lk.SymHallMars (BellSmMars ..) Q V]
 rw [funext (fun x:Points (Q.n+V.n)=>ebanPrMars p Y a Q.v V.v x)]; unfold FrostMantaMars; rw [sum_inner]; symm
 let f(z:LabelsMars (ArrangeT Q.n Q.v))(w:LabelsMars (ArrangeT V.n V.v))(x:Points (Q.n+V.n)):= (BellTableMars p Y).read x (tied (TiesMars _ z) (TiesMars _ w) a)
 have hu(z w):ContinuousOn (fun x=> Star.star (FeedTaxMars Q.v z)* FeedTaxMars V.v w*f z w x) (conf (Q.n+V.n)):= continuousOn_const.mul (((BellTableMars p Y).smooth_read (BellSmMars ..) _).continuousOn)
 refine (paintTouchMars _ univ _ (fun z _=>continuousOn_finsetSum univ (fun w _=>hu z w))).trans (sum_congr rfl (fun i _=>?_)); rw [inner_sum]; refine (paintTouchMars _ univ _ (fun j _=>hu i j)).trans (sum_congr rfl (fun j _=>?_)); rw[stampTouchMars,inner_smul_left,inner_smul_right, PatchPulseMars,mul_assoc]; rfl -- tune PatchPulseMars include L? declared after but before include. simp path read. associativity
#print axioms FrostπMars
end PlayArchiveMars
end YM.GaugeFieldConstruction.Ember.Volumetric
