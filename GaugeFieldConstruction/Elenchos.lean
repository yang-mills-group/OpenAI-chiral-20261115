import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed
/-! Finite vocabulary with uniform real coefficient bank. No norm on operands. -/
set_option autoImplicit false
set_option maxHeartbeats 45000
noncomputable section
namespace YM.Spectrix
open Function Finset
open scoped Classical
variable {E F G:Type}[AddCommGroup E][Module ℝ E][AddCommGroup F][Module ℝ F][AddCommGroup G][Module ℝ G]
abbrev voices(T:Finset E)(z:E→ℝ): E:=∑ i∈T,z i • i
structure Drama (T:Finset E)(V:ℝ)(x:E): Prop where
 pulse :∃ z:E→ℝ,(∀ i∈T,|z i|≤ V)∧voices T z=x
variable {P Q:Finset E}{S T U:Set E}{a b c:ℝ}{x y:E}
lemma Dmon (V:Drama P a x)(p:a≤b): Drama P b x:=by obtain ⟨z,v,t⟩:=V.pulse; exact ⟨z,fun i h=> (v i h).trans p,t⟩
lemma Df(u:Drama P a x)(A:P⊆Q)(p:0≤a):Drama Q a x:=by
 obtain ⟨z,v,t⟩:=u.pulse; let l(i:E):= if i∈ P then z i else 0
 refine ⟨l,fun i H=>?_,?_⟩
 · unfold l; split; next q=> exact v i q
   simpa
 rw [←t]; unfold voices; rw [←sum_subset A (f:=fun i:E=>l i • i) (fun i _ w=>by simp [l,w])]; exact sum_congr rfl fun i p=>by simp [l,p]
lemma Da(u:Drama P a x)(v:Drama P b y): Drama P (a+b) (x+y):=by
 obtain ⟨z,v',t⟩:=u.pulse; obtain ⟨w,h,s⟩:=v.pulse; refine ⟨z+w,fun i p=>(abs_add_le (z i) (w i)).trans (add_le_add (v' i p) (h i p)),?_⟩; simp only [voices,Pi.add_apply,add_smul,sum_add_distrib]; exact congrArg₂ _ t s
lemma D0(a:ℝ)(v:0≤a): Drama P a 0:=by refine ⟨0,fun i _=> show |(0:ℝ)|≤ a by simp [v],?_⟩; simp [voices]
lemma Ds(u:Drama P a x)(b:ℝ) (v:a≥0): Drama P (|b| * a) (b • x):=by
 obtain ⟨z,V,t⟩:=u.pulse; refine ⟨fun i=>b*z i,fun i p=>?_, ?_⟩
 · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (V i p) (abs_nonneg _)
 rw [← t,voices,voices, Finset.smul_sum]; exact sum_congr rfl fun i _=> mul_smul ..
lemma Di {i:E}(v:i∈P): Drama P 1 i:=by
 let w:E→ ℝ:= Pi.single i 1; refine ⟨w,fun h p=>?_,?_⟩
 · by_cases h:h=i <;> simp [w,Pi.single_apply,h]
 simp [w,voices,Pi.single_apply,ite_smul,v]
lemma D_η {I:Type*}(V:Finset I)(F:I→E)(C:I→ℝ)(K:∀ i∈V,Drama P (C i) (F i)):Drama P (∑ i∈V,C i) (∑ i∈V,F i):=by
 induction V using Finset.induction_on with|empty=> rw [sum_empty,sum_empty]; exact D0 _ le_rfl|@insert i V p ih=> rw [sum_insert p,sum_insert p]; exact Da (K i (mem_insert_self ..)) (ih fun i u=>K i (mem_insert_of_mem u))
abbrev Odious(S:Set E) : Prop:= ∃ P:Finset E, ∃ V:ℝ,0≤ V ∧ ∀ i∈S,Drama P V i
lemma Od_sub (e:S⊆T)(v:Odious T):Odious S:=by obtain ⟨P,V,K,U⟩:=v; exact ⟨P,V,K,fun i p=> U i (e p)⟩
lemma OdZ (x:E): Odious ({x}:Set E):=by refine ⟨{x},1,zero_le_one,?_⟩; rintro j (rfl: j=x); exact Di (mem_singleton_self _)
lemma OdVoid: Odious (∅:Set E):=⟨∅,1,zero_le_one,nofun⟩
lemma Od2 (u:Odious S) (v:Odious T): Odious (S∪T):=by
 obtain ⟨P,x,k,z⟩:=u; obtain ⟨Q,y,h,p⟩:=v; refine ⟨P∪Q,x+y,add_nonneg k h,?_⟩; rintro i (w|w); exact Dmon (Df (z i w) subset_union_left k) (le_add_of_nonneg_right h); exact Dmon (Df (p i w) subset_union_right h) (le_add_of_nonneg_left k)
lemma Od_a (e:∀ i∈ S,∃ j∈ T,∃ h∈ U,i=j+h)(p:Odious T)(v: Odious U):Odious S:=by
 obtain ⟨P,a,h,z⟩:=Od2 p v; refine ⟨P,a+a,add_nonneg h h,?_⟩; intro i p; obtain ⟨j,k,y,l,rfl⟩:=e i p; exact Da (z j (Or.inl k)) (z _ (Or.inr l))
lemma Od_s (e:∀ i∈ S,∃ j∈T,∃ c:ℝ,|c|≤ b∧ i=c • j)(h:Odious T)(p:0≤ b) : Odious S:=by
 obtain ⟨P,v,H,g⟩:=h; refine ⟨P,b*v,mul_nonneg p H,?_⟩; intro i p; obtain ⟨j,v,w,f,rfl⟩:=e i p; exact Dmon (Ds (g _ v) _ H) (mul_le_mul_of_nonneg_right f H)
lemma Dℓ (L:E→ₗ[ℝ] F)(p:Drama P a x)(s:0≤a): Drama (P.image L) (P.card * a) (L x):=by
 obtain ⟨z,p,r⟩:=p.pulse; let Q:=P.image L; have hp(i)(v:i∈P): Drama Q a (z i • L i):=Dmon (Ds (Di (mem_image_of_mem L v)) (z i) zero_le_one) ((mul_one _).le.trans (p i v))
 rw [←r]; unfold voices; rw [map_sum]; simp_rw [map_smul]; exact Dmon (D_η P _ _ hp) (by simp) -- tune s
lemma Od_L {S:Set F}(v:E→ₗ[ℝ] F)(H:∀ i∈ S,∃ j∈T,v j=i)(K:Odious T): Odious S:=by
 obtain ⟨P,a,p,u⟩:=K; refine ⟨P.image v, (P.card:ℝ) *a,by positivity,?_⟩; rintro i g; obtain ⟨j,w,rfl⟩:=H i g; exact Dℓ _ (u j w) p
lemma odor {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V](x:ℝ): Odious {i:V| ‖i‖≤ x}:=by
 let I:= Fin (Module.finrank ℝ V); let b:=Module.finBasis ℝ V; let L(i:I): V→L[ℝ]ℝ:=(b.coord i).toContinuousLinearMap; let Y:=|x| *∑ i:I,‖L i‖; let P:Finset V:= univ.image b
 have he:0≤Y:=mul_nonneg (abs_nonneg _) (sum_nonneg fun _ _=>norm_nonneg _)
 refine ⟨P,Fintype.card I *Y,by positivity,fun i p=>?_⟩
 have hl(j:I):|L j i|≤Y:= ((L j).le_opNorm i).trans ((mul_le_mul (single_le_sum (f:=fun j=>‖L j‖) (fun i _=>norm_nonneg _) (mem_univ j)) ((show ‖i‖ ≤ x from p).trans (le_abs_self _)) (norm_nonneg _) (sum_nonneg fun _ _=>norm_nonneg _)).trans_eq (mul_comm ..)) -- placeholder
 have hp(j:I):Drama P Y (L j i • b j):= Dmon (Ds (Di (mem_image_of_mem b ((mem_univ j)))) (L j i) zero_le_one) ((mul_one _).le.trans (hl j)); nth_rw 1 [← b.sum_repr i]; exact Dmon (D_η univ _ _ fun j _=>hp j) (by simp [I])
lemma Od_full {ι:Type*}(s:Finset ι)(F:ι→Set E)(h:∀ i∈s,Odious (F i)): Odious {j|∃ i∈s,j∈ F i}:=by
 induction s using Finset.induction_on with
 | empty=> apply Od_sub _ OdVoid; intro i ⟨j,h,k⟩; exact (notMem_empty _ h).elim -- tune
 | @insert i s t ih=>
    apply Od_sub _ (Od2 (h i (mem_insert_self ..)) (ih (fun i p=>h i (mem_insert_of_mem p))))
    rintro j ⟨u,k,v⟩; cases mem_insert.mp k with|inl p=> exact Or.inl (p ▸ v)|inr p=> exact Or.inr ⟨u,p,v⟩
lemma Od_total {ι:Type*}(s:Finset ι)(F:ι→Set E)(h:∀ i∈s,Odious (F i))(K: ∀ i∈ S, ∃ g:ι→ E,(∀ i∈s,g i∈F i) ∧ i=∑ j∈s,g j):Odious S:=by
 obtain ⟨P,v,w,x⟩:= Od_full s F h; refine ⟨P, s.card*v,mul_nonneg (Nat.cast_nonneg _) w,?_⟩; intro i p; obtain ⟨g,V,rfl⟩:=K i p; exact Dmon (D_η s g (fun _=>v) (fun i p=> x _ ⟨i,p,V i p⟩)) (by simp)
-- Inside procurement: using generators in S themselves. Project P along any non-normed algebraic Complement. each projected i admits some drama by membership in span. normalize. This will choose exact probes incl all-budget Jet currencies.
lemma drama_in {x:E}(h:x∈ Submodule.span ℝ S): ∃ P:Finset E, ∃ v:ℝ,(P:Set E)⊆S∧0≤v∧Drama P v x:=by
 apply Submodule.span_induction (p:=fun x _=>∃ P: Finset E,∃ v:ℝ,(P:Set E)⊆S∧0≤v∧ Drama P v x) ?_ ?_ ?_ ?_ h
 · intro i q; exact ⟨{i},1,by simpa,zero_le_one,Di (mem_singleton_self _)⟩
 · exact ⟨∅,0,by simp,le_rfl,D0 0 le_rfl⟩
 · rintro x y _ _ ⟨P,v,u,a,b⟩ ⟨T,k,h,l,w⟩; exact ⟨P∪ T,v+k,(by simpa using Set.union_subset u h),add_nonneg a l,Da (Df b subset_union_left a) (Df w subset_union_right l)⟩
 rintro t x _ ⟨P,v,a,h,l⟩; exact ⟨P,|t| *v,a,mul_nonneg (abs_nonneg _) h,Ds l _ h⟩
lemma chief (p:Odious S):∃ P:Finset E,∃ v:ℝ,0≤ v ∧ (P:Set E) ⊆ S ∧ ∀ i∈ S,Drama P v i:=by
 let H:=Submodule.span ℝ S; obtain ⟨M,m⟩:= H.exists_isCompl; let L:=Submodule.projection H M m; -- tune
 choose f c u v z using fun i:E=> drama_in (S:=S) (Submodule.projection_apply_mem m i)
 obtain ⟨P,V,K,U⟩:=p; let Q:= P.biUnion f; let W:= ∑ i∈P,V*c i; refine ⟨Q,W,sum_nonneg (fun i _=>mul_nonneg K (v i)),fun i t=>?_,fun i t=>?_⟩
 · obtain ⟨j,p,v⟩:=mem_biUnion.mp t; exact u j v
 obtain ⟨h,y,Y⟩:= (U i t).pulse
 have hp:L i=i:= Submodule.projection_apply_of_mem_left m (Submodule.subset_span t); rw [← hp,←Y]; unfold voices; rw [map_sum]; simp only [map_smul]; apply D_η; intro j p; exact Dmon (Ds (Df (z j) (fun i v=>mem_biUnion.mpr ⟨j,p,v⟩) (v j)) _ (v j)) (mul_le_mul_of_nonneg_right (y j p) (v j))
end YM.Spectrix
end
