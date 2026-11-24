import YM.CF.BProof.Pods.Cup
import YM.CF.BProof.Contour.Battery

/- split according to default block (all no-bad, labels parameter 1).
Multiplies both default and excited by p_b^{-1} and restores prep κ exactly. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Pods
open Function Filter MeasureTheory Finset RG Relation Contour
open scoped Topology BigOperators Classical ENNReal
variable {B:Type}[Fintype B][DecidableEq B] (X:B→Type)
variable [∀ i,MeasurableSpace (X i)] (μ:∀ i, Measure (X i))[∀ i,IsFiniteMeasure (μ i)]
variable (I:∀ i, Set (X i))
def siteP(i:B):= (μ i) (I i)
def adj(i:B)(T:Set (X i)):= (siteP X μ I i)⁻¹ • ((μ i).restrict T)
abbrev Dayway : Prop:=∀ i:B, 0<siteP X μ I i
def accept (i:B):= adj X μ I i (I i)
def reject (i:B):= adj X μ I i (I i)ᶜ
variable (p:∀ i, MeasurableSet (I i))(h:Dayway X μ I)
lemma off_top (i:B):siteP X μ I i≠⊤:= measure_ne_top _ _
include h
lemma sunny(i:B): IsProbabilityMeasure (accept X μ I i):=⟨by
 rw [accept,adj,Measure.smul_apply,Measure.restrict_apply_univ]; exact ENNReal.inv_mul_cancel (h i).ne' (off_top X μ I _)⟩
lemma finite_adj(i:B)(T:Set (X i)): IsFiniteMeasure (adj X μ I i T):= by unfold adj; constructor; rw [Measure.smul_apply]; exact ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr (h i).ne').lt_top (measure_lt_top _ _)
lemma finiteR(i:B): IsFiniteMeasure (reject X μ I i):= finite_adj _ _ _ h i _
def soup : Pot X := {μ:=accept X μ I, ν:=reject X μ I, prob:=sunny X μ I h, fin:=finiteR X μ I h}
include p
lemma fall (i:B) : μ i= siteP X μ I i • (reject X μ I i+accept X μ I i):=by
 unfold reject accept adj; rw [← smul_add,add_comm ((μ i).restrict _),Measure.restrict_add_restrict_compl (p i),smul_smul, ENNReal.mul_inv_cancel (h i).ne' (off_top X μ I _),one_smul]
def kilo := ∏ i:B,siteP X μ I i
lemma kilo_pos : 0<kilo X μ I:= bot_lt_iff_ne_bot.mpr (prod_ne_zero_iff.mpr (fun i _=>(h i).ne'))
lemma kilo_end : kilo X μ I<⊤:= ENNReal.prod_lt_top fun _ _=> Ne.lt_top (off_top X μ I _)
abbrev visit(T:Finset B):= πμ X (accept X μ I) (reject X μ I) T
lemma visits(T:Finset B): IsFiniteMeasure (visit X μ I T):=by
 change IsFiniteMeasure (πμ X (soup X μ I h).μ (soup X μ I h).ν T); infer_instance
lemma pact : Measure.pi μ=kilo X μ I • ∑ i:Finset B,visit X μ I i:=by
 letI a:=sunny X μ I h; letI b:=finiteR X μ I h; apply Measure.pi_eq; intro T t
 simp_rw [Measure.smul_apply,Measure.finsetSum_apply ,visit,πμ,Measure.pi_pi]; -- tune simp All
 let g(i:B):= reject X μ I i (T i); let f(i:B):= accept X μ I i (T i)
 have he(i:B): μ i (T i)=siteP X μ I i * (g i + f i):=by nth_rw 1 [fall X μ I p h i]; simp only [Measure.smul_apply,Measure.add_apply]; rfl
 simp_rw [he]; rw [prod_mul_distrib,Fintype.prod_add]; change kilo X μ I * _= kilo X μ I * _; congr 1; apply sum_congr rfl; intro i u
 let P(j:B):= px X (accept X μ I) (reject X μ I) i j (T j); change (∏ j:B,P j)=_; rw [← prod_mul_prod_compl i P]; unfold P px; congr 1; apply prod_congr rfl; intro j k; rw [if_pos k]; apply prod_congr rfl; intro j k; rw [if_neg (mem_compl.mp k)] -- tune local defs
lemma checks(F: ((i:B)→ X i)→ℂ)(f:Envelope F): (∫ x,F x ∂Measure.pi μ)= (kilo X μ I).toReal • ∑ i:Finset B,∫ x,F x ∂visit X μ I i:=by
 haveI:= visits X μ I p h; rw [pact _ _ _ p h,integral_smul_measure,integral_finsetSum_measure]; intro t _; exact Law.pay f
def buzz(x:(i:B)→X i):Finset B:= univ.filter fun i=> x i∉ I i
lemma waking : ∀ T:Finset B, ∀ᵐ x∂ visit X μ I T, buzz X I x=T:=by
 intro t; let v:=px X (accept X μ I) (reject X μ I) t; letI a:= sunny X μ I h; letI b:=finiteR X μ I h
 haveI (i:B): IsFiniteMeasure (v i):=by unfold v px; split <;> infer_instance
 have he(i:B): ∀ᵐ x∂ v i,x∉ I i↔ i∈t:=by
    unfold v px reject accept; split; next g=>
       apply Measure.ae_smul_measure; filter_upwards [ae_restrict_mem ((p i).compl) (μ:=μ i)] with x hx; simp only [g,iff_true]; exact hx -- tune
    next g=>
       apply Measure.ae_smul_measure; filter_upwards [ae_restrict_mem (p i) (μ:=μ i)] with x hx; simp only [hx,g,not_true]
 have ht(i:B): ∀ᵐ x∂Measure.pi v,x i∉ I i ↔ i∈t:= (Measure.quasiMeasurePreserving_eval v i).tendsto_ae (he i)
 refine (ae_all_iff.mpr ht).mono (fun x a=>?_); ext i; simpa only [buzz,mem_filter,mem_univ,true_and] using a i
lemma remain(F: ((i:B)→ X i)→ Prop)(g:∀ᵐ x∂Measure.pi μ,F x)(T:Finset B): ∀ᵐ x∂ visit X μ I T,F x:=by
 rw [pact _ _ _ p h, Measure.ae_ennreal_smul_measure_iff (c:=(kilo X μ I)) (kilo_pos X μ I p h).ne'] at g; exact ae_finsetSum_measure_iff.mp g T (mem_univ _)
omit h
lemma buzz_m(T:Finset B) : MeasurableSet {x|buzz X I x=T}:= by
 unfold buzz; simp only [Finset.ext_iff,Set.setOf_forall,mem_filter,mem_univ,true_and]; apply MeasurableSet.iInter; intro i; by_cases v:i∈T<;>simp only [v,iff_true,iff_false,not_not]; exact ((measurable_pi_apply (X:=X) i) (p i)).compl; exact (measurable_pi_apply i) (p i)
end YM.CF.BProof.Pods
