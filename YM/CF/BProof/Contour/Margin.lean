import YM.CF.BProof.Law.Product

/-! Factorization on spatial λ disjoint supports, default and excited measures. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Contour
open Function Filter RG MeasureTheory Finset Relation
open scoped Topology BigOperators Classical ENNReal -- remove Moment...
variable {B : Type*}(X:B→Type*) [Fintype B][DecidableEq B][∀ i,MeasurableSpace (X i)]
variable (μ ν:∀ i, Measure (X i)) [∀ i,IsProbabilityMeasure (μ i)][∀ i,IsFiniteMeasure (ν i)]
abbrev LawS := ∀ i,Measure (X i)
abbrev px (t:Finset B) (i:B) := if i∈t then ν i else μ i
def πμ(t:Finset B) : Measure (∀ i,X i) :=Measure.pi (px X μ ν t)
instance px_fin (t:Finset B)(i:B): IsFiniteMeasure (px X μ ν t i):=by unfold px; split <;> infer_instance
instance π_fin(t:Finset B): IsFiniteMeasure (πμ X μ ν t):=by unfold πμ; infer_instance
lemma π_zero : πμ X μ ν ∅=Measure.pi μ:=by unfold πμ px; simp
instance : IsProbabilityMeasure (πμ X μ ν ∅) :=by rw [π_zero]; infer_instance
variable {E:Type*}(f:(∀ i,X i)→ E)
def reads (S:Finset B) : Prop:= ∀ x y,(∀ i∈ S,x i=y i)→ f x=f y
lemma reads_up(S T:Finset B)(h:S⊆ T)(p:reads X f S): reads X f T:= fun x y q=> p x y fun i t=> q i (h t)
lemma reads_comp {E':Type*}(f':E→E')(s:Finset B)(h:reads X f s): reads X (f' ∘ f) s:=fun x y e=> congrArg f' (h x y e)
variable [RCLike E] [∀ i,Nonempty (X i)] (g:(∀ i,X i)→ E)
omit [∀ i, Nonempty (X i)] in
lemma reads_prod (h:Finset B)(p:reads X f h)(v:reads X g h): reads X (fun x=> f x*g x) h:=fun x y e=> congrArg₂ _ (p x y e) (v x y e)
section
include X
private abbrev A(S:Finset B):=∀ i:{i // i∈S},X i
private abbrev A'(S:Finset B):=∀ i:{i // i∉S},X i
private abbrev leftM (v:∀ i,Measure (X i)) (S:Finset B) : Measure (A X S):=Measure.pi fun i=>v i
private abbrev rightM (v:∀ i,Measure (X i)) (S:Finset B) : Measure (A' X S):=Measure.pi fun i=>v i
private abbrev Q (S:Finset B): (∀ i,X i) ≃ᵐ A X S × A' X S:=MeasurableEquiv.piEquivPiSubtypeProd X (· ∈S)
private lemma px_q (S:Finset B)(v:∀ i,Measure (X i))[∀ i,IsFiniteMeasure (v i)] : MeasurePreserving (Q X S) (Measure.pi v) ((leftM X v S).prod (rightM X v S)):=by convert! measurePreserving_piEquivPiSubtypeProd v (· ∈S) using 2 <;>congr!
private def toy (i:B): X i:=Classical.arbitrary _
private def fL (S:Finset B)(x:A X S):= f ((Q X S).symm (x,fun i=>toy X i))
private def fR (S:Finset B)(x:A' X S):= f ((Q X S).symm (fun i=> toy X i,x))
private lemma mix (S:Finset B)(h:reads X f S)(k:reads X g Sᶜ)(v:∀ i, Measure (X i))[∀ i,IsFiniteMeasure (v i)]:
 (∫ x,f x*g x ∂(Measure.pi v))=(∫ x,fL X f S x ∂leftM X v S)*(∫ x,fR X g S x ∂rightM X v S):=by
 rw [← integral_prod_mul (μ:=leftM X v S) (ν:=rightM X v S), ← (px_q X S v).integral_comp']; apply integral_congr_ae; refine Eventually.of_forall (fun x=> congrArg₂ _ (h _ _ (fun i l=>?_)) (k _ _ (fun i l=>?_)))
 · unfold Q; simp [l]; -- tune fun L
 unfold Q; simp [mem_compl.mp l]
private lemma mix_left (S T:Finset B)(h:T⊆ S)(v:reads X f S) : (∫ x,f x ∂πμ X μ ν T)=(∫ x,fL X f S x ∂leftM X (px X μ ν T) S):=by
 let w:=px X μ ν T; have hR: rightM X w S = rightM X μ S:=by unfold rightM; congr; ext i; -- wrongly ext
                                                                         rw [show w i.val= μ i.val from if_neg (fun v=>i.property (h v))]
 have ht:= mix X f (fun _=>1) S v (fun _ _ _=>rfl) (px X μ ν T); unfold fR at ht; simp only [mul_one] at ht; rw [hR,integral_const,probReal_univ,one_smul,mul_one] at ht; exact ht
private lemma mix_right (S T:Finset B)(h:T⊆ Sᶜ)(v:reads X f Sᶜ) : (∫ x,f x ∂πμ X μ ν T)=(∫ x,fR X f S x ∂rightM X (px X μ ν T) S):=by
 let w:=px X μ ν T; have hR: leftM X w S = leftM X μ S:=by unfold leftM; congr; ext i;
                                                                     rw [show w i.val= μ i.val from if_neg (fun v=> (mem_compl.mp (h v)) i.property)]
 have ht:= mix X (fun _=>1) f S (fun _ _ _=>rfl) v (px X μ ν T); unfold fL at ht; simp only [one_mul] at ht; rw [hR,integral_const,probReal_univ,one_smul,one_mul] at ht; exact ht
-- exact on disjoint. doesn't impose equality given on default when within other's core.
theorem portion(S T J K:Finset B)(l:J⊆ S)(u:K⊆ T)(h:reads X f S)(k:reads X g T)(p:Disjoint S T): (∫ x,f x*g x ∂πμ X μ ν (J∪ K))=(∫ x,f x ∂πμ X μ ν J)*(∫ y,g y ∂πμ X μ ν K):=by
 have hp:T⊆ Sᶜ:= fun i v=> mem_compl.mpr (fun t=> disjoint_left.mp p t v); have hh:= reads_up X g _ _ hp k; rw [mix_left X μ ν f S J l h,mix_right X μ ν g S K (u.trans hp) hh]; unfold πμ; rw [mix X _ _ S h hh]; -- πμ unfolded too early
 have ht: leftM X (px X μ ν (J∪ K)) S=leftM X (px X μ ν J) S:=by unfold leftM; congr; ext i; unfold px; have hi:i.val∉K:= fun v=> mem_compl.mp (hp (u v)) i.property; simp [hi]
 have hv: rightM X (px X μ ν (J∪ K)) S=rightM X (px X μ ν K) S:=by unfold rightM; congr; ext i; unfold px; have hi:i.val∉J:= fun v=> i.property (l v); simp [hi]
 rw [ht,hv]
end
end YM.CF.BProof.Contour
