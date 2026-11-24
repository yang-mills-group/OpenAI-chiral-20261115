import YM.CF.BPress.Palmer.Price
/-! lem:B-rootK parts 1 and 2 variants with quantitative thresholds (pure constants * γ/spare; reduce rate if needed and epower). Uses manuscript graph coefficients and trees. All applications here on **finite labels**; log an actual sum over all ordered tuple multiplicities. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Palmer
open Function Relation Filter NormedSpace MeasureTheory Finset Lattice RG Grid Branch Ledger Push.AbsoluteSums Ursell Trees Animals Graph
open scoped Topology BigOperators InnerProductSpace Classical
variable {s:Side}{Y I Ω:Type}[Fintype I][Fintype Y][DecidableEq Y] {F:Branch.Field Y}{X:I→Seal Y}{c a γ δ:ℝ}{w:I→ℝ}{m: Side}
open Push.AbsoluteSums.Gas Palot
variable (X)
abbrev BranchC (X:I→Seal Y) := {S: Finset I// Spark X S}
-- hide instance synthesis across X types with classical decidability
abbrev Cover (Y':BranchC X) := Y'.val.biUnion X
structure Grows [DecidableEq I] (F:Finset I→ℂ):Prop where
 fromEmpty : F ∅=1
 mul(S T:Finset I): Disjoint (S.biUnion X) (T.biUnion X) → Disjoint S T → F (S∪T)=F S*F T
variable {X}
namespace Grows
-- use caster sort. prices can carry many core fields beyond X under contour after integration (values scalar). grouping requires no missing constraints.Agregation via Ac.Keys
variable [DecidableEq I]
abbrev stretch(B:Finset (BranchC X)):= B.biUnion Subtype.val -- W₀ unknown
private lemma downstairs(P:Finset I) : ∃ B: Finset (BranchC X),B.image Subtype.val=Parts X P:=by
 let F:= (Parts X P); refine ⟨F.attach.image (fun x=> (⟨x.val,lives X P x.property|>.2⟩:BranchC X)),?_⟩; ext1 x; conv_lhs=> simp only [mem_image,mem_attach,true_and]
 constructor; · rintro ⟨a,⟨i,rfl⟩,h⟩; exact h ▸ i.property
 intro p; let b: ↥F:=⟨x,p⟩; exact ⟨⟨x,(lives X P p).2⟩,⟨b,rfl⟩,rfl⟩
-- avoid implicit classical mismatch when `BranchC` definitions. explicit `[DecidableEq I]` req? section variable declared after defs causes `DecEq` on Subtype.Hakind`. ensure pack same.Small.
private lemma plenary (P:Finset I) : ∃ B:Finset (BranchC X), stretch (X:=X) B=P ∧ separated (relate (Cover X)) B:=by
 obtain ⟨l,g⟩:= downstairs (X:=X) P; refine ⟨l,?_ ,?_⟩; have ht: stretch (X:=X) l=(Parts X P).biUnion id:=by
    ext1 i; simp only [←g,Grows.stretch,mem_biUnion,mem_image]; constructor; rintro ⟨a,b,v⟩; exact ⟨a.val,⟨a,b,rfl⟩,v⟩; rintro ⟨i,⟨z,v,rfl⟩,h⟩; exact ⟨z,v,h⟩ -- tune
 · exact ht.trans (reconstruct X P)
 intro i h j l' e v; refine v (separate X P (show i.val∈Parts X P from g ▸ mem_image_of_mem _ h) (show j.val∈Parts X P from g ▸ mem_image_of_mem _ l') (Subtype.val_injective.ne e)) -- tune
private lemma estate {P:Finset (BranchC X)}(h:separated (relate (Cover X)) P): Parts X (stretch (X:=X) P)=P.image Subtype.val:=by
 have he : stretch (X:=X) P=(P.image Subtype.val).biUnion id:=by
    ext i; simp only [stretch,mem_biUnion,mem_image]; constructor; rintro ⟨a,b,v⟩; exact ⟨a.val,⟨a,b,rfl⟩,v⟩; rintro ⟨i,⟨z,v,rfl⟩,h⟩; exact ⟨z,v,h⟩
 rw [he]; refine separates X _ (fun i h=>?_) (fun i b k v t=>?_ ); · obtain ⟨p,v,rfl⟩:= mem_image.mp h; exact p.property
 obtain ⟨p,c,rfl⟩:= mem_image.mp (show i∈_ from b); obtain ⟨z,h',rfl⟩:=mem_image.mp (show k∈_ from v); exact not_not.mp (h p c z h' (fun p=>t (congrArg Subtype.val p))) -- tune
variable {u:Finset I→ℂ}(H:Grows X u)(t: evenT F X)
include H t
lemma worths (B:Finset (BranchC X))(h: separated (relate (Cover X)) B): u (stretch (X:=X) B)=∏ i∈ B,u i.val:=by
 induction B using Finset.induction_on with|empty=> rw [stretch,biUnion_empty,prod_empty]; exact H.fromEmpty|@insert i B t' ih=> -- tune
    let S:= stretch (X:=X) B; have hm(j:BranchC X)(p:j∈ B): Disjoint (Cover X i) (Cover X j):=not_not.mp (h _ (mem_insert_self ..) _ (mem_insert_of_mem p) (ne_of_mem_of_not_mem p t').symm); have he : Disjoint (i.val.biUnion X) (S.biUnion X):=by
       refine disjoint_left.mpr fun a p q=> ?_; obtain ⟨z,v,b⟩:= mem_biUnion.mp q; obtain ⟨j,w,g⟩:= mem_biUnion.mp v; exact disjoint_left.mp (hm j w) p (mem_biUnion.mpr ⟨z,g,b⟩)
    have hx:Disjoint i.val S:=by refine disjoint_left.mpr fun j p q=>?_ ; obtain ⟨a,g⟩:= Grid.inhabited_grove (t j); exact disjoint_left.mp he (mem_biUnion.mpr ⟨j,p,g⟩) (mem_biUnion.mpr ⟨j,q,g⟩)
    rw [show stretch (X:=X) (insert i B)=i.val∪ S from biUnion_insert, H.mul _ _ he hx, show u S=_ from ih (fun i p j h' e=> h i (mem_insert_of_mem p) j (mem_insert_of_mem h') e),prod_insert t'] -- tune
lemma totalG : ∑ i:Finset I,u i= ∑ y:Finset (BranchC X), Palot.pace (relate (Cover X)) (fun x=>u x.val) y:=by
 unfold Palot.pace; rw [←sum_filter]; symm; apply sum_bij (fun i v=> stretch (X:=X) i); · intro i _; simp
 · intro i b j c h; apply image_injective (f:=Subtype.val (p:=Spark X)) Subtype.val_injective; rw [← estate (mem_filter.mp b|>.2),h, estate ((mem_filter.mp c).2)] -- tune instances
 · intro i _; obtain ⟨B,F,V⟩:= plenary (X:=X) i; exact ⟨B,mem_filter.mpr ⟨mem_univ _,V⟩,F⟩
 intro i h; exact (worths H t i ((mem_filter.mp h).2)).symm
end Grows
-- package letter: rule_contour and pf both pointwise.HC
variable [DecidableEq I]{u:Finset I→ℂ}
lemma evenT.up (h:evenT F X): evenT F (Cover X):= fun x=> union_g x.property (fun i _=> h i)
lemma Cash0 (p:evenT F X)(S:Sole F m)(t:Stakes m a γ)(h:Cash X w (a+a) γ): Cash (Cover X) (fun i=>∏ x∈ i.val,w x) a (till_cost m γ):=by
 have he:=spark_pay p S t h; refine ⟨fun i=>prod_nonneg (fun j _=>h.pos j),fun i=> ?_⟩; let g(i:Finset I):ℝ:= if Spark X i then ∏ x∈i,w x else 0; have ht := budget_pull Subtype.val (Subtype.val_injective (p:=Spark X)) (he.hits i); refine budget_mono ht (fun x=>?_) (fun x=>?_); unfold score; split; exact mul_nonneg (Real.exp_pos _).le (prod_nonneg (fun i _=> h.pos i)); exact le_rfl; change _ ≤ score (Finset.biUnion · X) _ _ _ _; unfold score; simp [x.property,Cover] -- tune
-- `u` pointwise already coherence requires inequality only on branch families.
theorem algorithm (p:Grows X u)(T:Sole F m)(q:Stakes m a γ)(e:Stakes m (a+a) c)(hq:till_cost m c ≤ γ) (D:evenT F X)(h:Cash X w ((a+a)+(a+a)) c)(u0:∀ i: BranchC X,‖u i.val‖≤∏ j∈ i.val,w j): let w₀(i:BranchC X):=∏ j∈i.val,w j; let r:=logL (Cover X) (fun i=>u i.val); let b:=cash (Cover X) w₀; ∑ i:Finset I,u i= Complex.exp (∑ s:Seal Y,r s)∧ (∀ s:Seal Y, ‖r s‖≤ b s)∧ Cash id b a (till_cost m γ)∧∀ x:Seal Y,b x≠0→ Grove F x:=by
 intro v z b; let f:= D.up; have ht:Cash (Cover X) v (a+a) γ:= (Cash0 D T e h).weaken hq; refine ⟨p.totalG D|>.trans (bindingL f T q ht (fun i=>u i.val) u0).symm,log_cost f T q ht _ u0, book f T q ht,fun i v=> log_grove f T q ht v⟩ -- tune
end YM.CF.BPress.Palmer
#print axioms YM.CF.BPress.Palmer.algorithm
