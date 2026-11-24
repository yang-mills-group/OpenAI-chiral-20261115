import YM.CF.BProof.Prox.Atmos

/- Both column & row budgets at full exponential weight. Rectangular. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Prox
open Function Filter Finset MeasureTheory Matrix
open scoped Topology BigOperators Classical
variable {A X E I J L: Type*} [Fintype A][Fintype I][Fintype J][Fintype L][MeasurableSpace X]
abbrev Page (A I J K: Type*) := Finset A → Matrix I J K
abbrev Board (X I J K: Type*) := X→ Matrix I J K
section
variable {B:Base A}[NormedAddCommGroup E][MeasurableSpace E]
structure Show (O:Atmos A X)(F:B.Index I)(H:B.Index J)(Y:X→ Matrix I J E)(a C:ℝ): Prop where
 /-- one entry per full support size. Terms identically zero can have nonzero payroll. -/
 presents : ∃ (W: Page A I J ℝ)(K:Page A I J (X→E)),
   (∀ i: Finset A,∀ x y,Rent O i (K i x y) (W i x y)) ∧
   (∀ i x y,W i x y ≠ 0 → B.C i ∧ F.port x∈i∧H.port y∈i)∧
   (∀ x y,(fun u=> Y u x y)= ∑ i,(K i x y)) ∧ -- syntax fix expected
   (∀ i,∑ j,∑ R:Finset A,Real.exp (a*R.card)*W R i j≤ C)∧
   (∀ j,∑ i,∑ R:Finset A,Real.exp (a*R.card)*W R i j≤ C)
end
namespace Show
variable {B:Base A}{O:Atmos A X}{a C c D:ℝ}{F:B.Index I}{H:B.Index J}
section
variable [NormedAddCommGroup E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E]{Y Z : Board X I J E}
lemma zero (h:0≤C) : Show O F H (0:Board X I J E) a C:= by
 constructor; refine ⟨0,0,?_,?_,?_,?_,?_⟩
 · intro i x y; exact Rent.zero
 · intro i x y t; simp at t
 · intro x y; simp; rfl
 · intro i; simpa
 intro j; simpa
lemma presents_cost (g:Show O F H Y a C)(h:c≤a)(p:C≤D): Show O F H Y c D := by
 obtain ⟨W,K,t,v,u,l,r⟩:=g.presents; constructor
 have he(x y i):Real.exp (c*(i:Finset A).card)*W i x y≤Real.exp (a*i.card)* W i x y:=by apply mul_le_mul_of_nonneg_right _ (t i x y).price; exact Real.exp_le_exp.mpr (by gcongr)
 exact ⟨W,K,t,v,u,fun i=> (sum_le_sum (fun j _=>sum_le_sum (fun k _=>he i j k))).trans ((l i).trans p),fun i=> (sum_le_sum (fun j _=> sum_le_sum (fun k _=>he j i k))).trans ((r i).trans p)⟩
lemma add (h:Show O F H Y a C)(g:Show O F H Z a D): Show O F H (Y+Z) a (C+D) := by
 obtain ⟨W,K,t,v,u,l,r⟩:=h.presents; obtain ⟨W',K',t',v',u',l',r'⟩:=g.presents; constructor; refine ⟨W+W',K+K',fun i x y=>Rent.add (t ..) (t' ..),?_,?_,?_,?_⟩
 · intro i x y k; change W i x y+W' i x y≠0 at k; by_cases h:W i x y=0; exact v' i x y (by simpa only [h,zero_add] using k); exact v i x y h
 · intro x y; simp only [Pi.add_apply, Matrix.add_apply,sum_add_distrib]; rw [←u,←u']; rfl -- tune
 · intro i; simp only [Pi.add_apply, Matrix.add_apply, mul_add,sum_add_distrib]; exact add_le_add (l i) (l' i)
 intro i; simp only [Pi.add_apply, Matrix.add_apply, mul_add,sum_add_distrib]; exact add_le_add (r i) (r' i)
lemma neg (h:Show O F H Y a C): Show O F H (-Y) a C:= by
 obtain ⟨W,K,t,v,u,l,r⟩:=h.presents; constructor; refine ⟨W,-K,fun i x y=> (t i x y).neg,v,fun x y=>?_,l,r⟩; simp only [Pi.neg_apply,Matrix.neg_apply,sum_neg_distrib]; rw [←u]; rfl
lemma sub (h:Show O F H Y a C)(g:Show O F H Z a D): Show O F H (Y-Z) a (C+D):=by rw [sub_eq_add_neg]; exact h.add g.neg
lemma sum {K:Type*}(t: Finset K)(Y:K→Board X I J E)(C:K→ℝ)(u:∀ i∈t,Show O F H (Y i) a (C i)): Show O F H (∑ i∈t,Y i) a (∑ i∈t,C i):=by
 induction t using Finset.induction_on with |empty=> simp only [sum_empty]; exact zero le_rfl| @insert i t g ih=> rw [sum_insert g,sum_insert g]; exact (u _ (mem_insert_self ..)).add (ih (fun i v=>u i (mem_insert_of_mem v)))
lemma reorient (h:Show O F H Y a C): Show O H F (fun x=> (Y x).transpose) a C:=by
 obtain ⟨W,K,t,v,u,l,r⟩:=h.presents; constructor; exact ⟨fun i=>(W i).transpose,fun i=>(K i).transpose,fun i x y=>t i y x,fun i x y h=> ⟨(v i y x h).1,(v i y x h).2.2,(v i y x h).2.1⟩,fun x y=>u y x,r,l⟩
lemma smul [NormedSpace ℝ E] (h:Show O F H Y a C)(c:ℝ): Show O F H (c • Y) a (‖c‖*C):=by
 obtain ⟨W,K,t,v,u,l,r⟩:=h.presents; constructor; refine ⟨‖c‖ • W,c • K,fun i x y=>(t i x y).smul c,?_,?_,?_,?_⟩
 · intro i x y h; apply v; change ‖c‖*W i x y ≠ 0 at h; exact right_ne_zero_of_mul h -- name
 · intro x y; simp only [Pi.smul_apply,Matrix.smul_apply,← Finset.smul_sum]; rw [←u]; rfl
 · intro i; simp_rw [Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,mul_left_comm _ ‖c‖,← mul_sum]; exact mul_le_mul_of_nonneg_left (l i) (norm_nonneg _)
 intro j; simp_rw [Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,mul_left_comm _ ‖c‖,← mul_sum]; exact mul_le_mul_of_nonneg_left (r j) (norm_nonneg _)
lemma dotPay (h:Show O F H Y a C) (p:0≤a) (x:X)(i:I): ∑ j,‖Y x i j‖≤C:=by
 obtain ⟨W,K,t,v,u,l,r⟩:= h.presents
 apply le_trans _ (l i); apply sum_le_sum; intro j _; apply le_trans (b:=∑ a,‖K a i j x‖)
 · have he:=congrFun (u i j) x;  simp only [Finset.sum_apply] at he; rw [he]; apply norm_sum_le
 exact sum_le_sum fun R _=> ((t R i j).exact_bound x).trans (le_mul_of_one_le_left (t R i j).price (Real.one_le_exp (by positivity)))
end
end Show
end YM.CF.BProof.Prox
