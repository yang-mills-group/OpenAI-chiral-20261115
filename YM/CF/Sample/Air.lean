import YM.CF.Phase.Markov
set_option linter.unusedSectionVars false

/-! Probability on a finite mark DAG, an exact marginal at each ideal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase.Sample
open scoped BigOperators Topology
open MeasureTheory Set Finset Function Filter
variable {I T E : Type*} [DecidableEq I] [Fintype I] [MeasurableSpace T] [TopologicalSpace T] [CompactSpace T]
        [T2Space T] [SecondCountableTopology T] [BorelSpace T] [Nonempty T]
variable {μ : Measure T} [IsProbabilityMeasure μ]
abbrev fares (I : Type*) [Fintype I] (μ : Measure T) [IsProbabilityMeasure μ] : Measure (I→T) := Measure.pi (fun _=>μ)
def AgreeF (A : Finset I) (v w : I → T) : Prop := ∀ i∈A,v i=w i
lemma AgreeF.flip {A:Finset I} {v w:I→T} (h : AgreeF A v w) : AgreeF A w v := fun i l=> (h i l).symm
lemma AgreeF.less {A B : Finset I} {v w : I→T} (h : AgreeF A v w) (g : B ⊆ A) : AgreeF B v w := fun i l=>h i (g l)

def patchF (A : Finset I) (u v : I→T) := fun i=>if i∈A then u i else v i
lemma patch_left (A) (x y : I→T) : AgreeF A (patchF A x y) x := fun i h=> if_pos h
lemma patch_update (A : Finset I) (x y : I→T) (i : I) (h : i∉A) (p : T) :
    patchF A x (update y i p)=update (patchF A x y) i p := by
  funext j; by_cases g:j=i <;> simp [patchF,g,h]
lemma patch_hold (A : Finset I) (x y : I→T) (i : I) (h : i ∈ A) (p : T) : patchF A x (update y i p)=patchF A x y := by
  funext j; by_cases g:j=i <;> simp [patchF,g,h]
lemma patch_cont (A : Finset I) : Continuous (fun z:(I→T)×(I→T)=>patchF A z.1 z.2) := by
  refine continuous_pi fun i=>?_; unfold patchF; split <;> fun_prop
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
-- integrate over all copies with some pinned draws.
def aerate (A : Finset I) (μ : Measure T) [IsProbabilityMeasure μ] (f : (I→T)→E) (v : I→T) := ∫ w,f (patchF A v w) ∂fares I μ
lemma aerate_cont (A : Finset I) (μ : Measure T) [IsProbabilityMeasure μ] {f : (I→T)→E} (h : Continuous f) : Continuous (aerate A μ f) := net_cont _ _ (h.comp (patch_cont A))
lemma aerate_agree (f : (I→T)→E) {A : Finset I} {x y : I→T} (h : AgreeF A x y) : aerate A μ f x=aerate A μ f y := by
  unfold aerate; congr 1; ext w -- tune
  congr 1; funext i; unfold patchF; split <;> simp_all [AgreeF]
-- restores original integral (no conditions)
lemma split_air [CompleteSpace E] (A : Finset I) {f : (I→T)→E} (h : Continuous f) : (∫ v,aerate A μ f v ∂fares I μ)=∫ v,f v ∂fares I μ := by
  let m := fun _:I=>μ
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _:I=>T) (·∈A)
  have he := (measurePreserving_piEquivPiSubtypeProd m (·∈A)).symm e
  change ∫ v,aerate A μ f v ∂Measure.pi m=∫ v,f v ∂Measure.pi m
  rw [←he.integral_comp' (aerate A μ f), ←he.integral_comp' f, integral_prod, integral_prod]
  · congr 1; ext z
    let B := fun i:I=> i∈A
    let G (t : ({i:I//i∈A}→T)×({i:I//¬i∈A}→T)) := f (e.symm t)
    let M := fun (l : Fintype {i:I//¬i∈A})=> @Measure.pi _ (fun _:{i:I//¬i∈A} => T) l _ (fun _=>μ)
    let k := M (Subtype.fintype fun i:I=>¬i∈A)
    have hK : IsProbabilityMeasure k := by unfold k M; infer_instance -- tune
    have ht (y) : aerate A μ f (e.symm (z,y))=∫ t, G (z,t) ∂k := by
      unfold aerate; rw [←he.integral_comp' (fun w=> f (patchF A (e.symm (z,y)) w)), integral_prod_symm]
      · apply integral_congr_ae; apply Eventually.of_forall; intro x
        have hf (b) : patchF A (e.symm (z,y)) (e.symm (b,x))=e.symm (z,x) := by
          funext i; by_cases g:i∈A <;> simp [patchF,e,g]
        simp_rw [hf]; simp [G,m]
      change Integrable ((fun w=> f (patchF A (e.symm (z,y)) w)) ∘ ⇑e.symm) _
      apply he.integrable_comp_emb e.symm.measurableEmbedding |>.mpr
      apply net_compact; exact h.comp ((patch_cont A).comp (continuous_const.prodMk continuous_id))
    change ∫ t,aerate A μ f (e.symm (z,t)) ∂k= ∫ t,G (z,t) ∂k
    simp_rw [ht]; simp
  · exact he.integrable_comp_emb e.symm.measurableEmbedding |>.mpr (net_compact h)
  exact he.integrable_comp_emb e.symm.measurableEmbedding |>.mpr (net_compact (aerate_cont A μ h))

/-- Local probability tariffs. -/
structure Plan (I : Type*) (μ : Measure T) [Fintype I] [DecidableEq I] [IsProbabilityMeasure μ] where
  orderF : I →ℕ
  indexF : I→Finset I
  run : I→(I→T)→ℝ
  polite i : Continuous (run i)
  rightF i v : 0 ≤ run i v
  normalize i v : ∫ t:T, run i (Function.update v i t) ∂μ=1
  readF i x y : AgreeF (indexF i) x y → run i x=run i y
  before i j : j∈indexF i → i≠j → orderF j<orderF i
variable (p : Plan I μ)
abbrev sails (s : Finset I) (v : I→T) := density s p.run v
abbrev fall (v : I→T) := sails p Finset.univ v
lemma sails_nonneg (s) (v : I→T) : 0 ≤ sails p s v := prod_nonneg (fun _ _=>p.rightF ..)
def Bank (s : Finset I) := ∀ i∈s,p.indexF i⊆s
lemma Bank.union {p : Plan I μ} {s t} (h : Bank p s) (g : Bank p t) : Bank p (s∪t) := by
  intro i hi; rcases mem_union.mp hi with l|l
  · exact (h i l).trans subset_union_left
  exact (g i l).trans subset_union_right -- tune
lemma banked {s : Finset I} (h : Bank p s) {x y : I→T} (g : AgreeF s x y) : sails p s x=sails p s y := prod_congr rfl fun i hi=>p.readF i x y (g.less (h i hi))
lemma sails_all : ∫ v, fall p v ∂fares I μ=1 := dense_norm _ p.run p.orderF p.polite p.normalize fun i j e f v t=>p.readF i _ _ (fun k l=>by
  by_cases g:k=j; subst k; exact False.elim (not_lt_of_ge f (p.before i j l e)); simp [update_of_ne g])
lemma aer_valid (s : Finset I) (v : I→T) : aerate s μ (sails p sᶜ) v=1 := by
  let f (i:I) (y:I→T) : ℝ := if i∈s then 1 else p.run i (patchF s v y)
  have h (i) : Continuous (f i) := by unfold f; split; exact continuous_const; exact (p.polite i).comp ((patch_cont s).comp (continuous_const.prodMk continuous_id))
  have g y : sails p sᶜ (patchF s v y) = density sᶜ f y := prod_congr rfl (fun i l=> (if_neg (mem_compl.mp l)).symm)
  unfold aerate; simp_rw [g]; refine dense_norm sᶜ f p.orderF h ?_ ?_
  · intro i x; unfold f; split_ifs with e; simp; simp_rw [patch_update s v x i e]; exact p.normalize _ _
  intro i j e g x t; unfold f; split_ifs with hx; rfl; by_cases k:j∈s
  · rw [patch_hold s v x j k]
  rw [patch_update s v x j k]; apply p.readF; intro l hl
  by_cases f:l=j; subst l; exact False.elim ((not_lt_of_ge g) (p.before i j hl e)); rw [update_of_ne f]
lemma fuel {s} (h : Bank p s) {x y : I→T} (g : AgreeF s x y) : fall p x=sails p s y*sails p sᶜ x := by rw [←banked p h g, sails,sails,density,density,prod_mul_prod_compl]; rfl
end YM.CF.Phase.Sample
