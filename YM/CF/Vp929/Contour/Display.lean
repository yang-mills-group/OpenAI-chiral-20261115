import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic

/-! Usable least costs computed against finite systems of jets. No assumption tests separate, and
no artificial topological completions. In context of arrays known to have *some* structure and
cost (possibly much larger; including the existence of permissible jets to test). Display calculus. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Py.Rate
open Function Set BigOperators Filter Topology
variable {X Y A i j:Type*}(H:Submodule ℝ (X→ℝ))
structure Display (cost: X→ℝ→Prop) :Prop where
 exists_T : ∃ L:Set (X→ℝ), L ⊆ H ∧ L.Nonempty ∧ ∀ x:X,(∃ u,cost x u)→∀ u, cost x u ↔ ∀ l∈ L,|l x|≤ u
variable {H}
namespace Display
variable {c:X→ℝ→Prop}{d:i→X→ℝ→Prop}
lemma hull (h:Display H c)(k:X→ℝ→Prop)(p:∀ x,(∃v,k x v)→ ∀u,k x u↔c x u): Display H k:=by
 obtain ⟨L,h,b,e⟩:= h.exists_T; exact ⟨L,h,b,fun x E u=> (p x E u).trans (e x (by obtain ⟨t,t'⟩:= E; exact ⟨_, (p _ ⟨_,t'⟩ _).1 t'⟩) u)⟩
lemma pull (F:Y→X){T:Submodule ℝ (Y→ℝ)}(u:∀ h:X→ℝ,h∈H→h ∘ F∈ T)(p:Display H c): Display T (fun x=> c (F x)):=by
 obtain ⟨L,h,b,e⟩:= p.exists_T; refine ⟨(fun f=> f ∘ F) '' L, ?_, b.image _,fun x p u=> ?_⟩; · rintro k ⟨k,h',rfl⟩; exact u _ (h h')
 rw [forall_mem_image]; exact e (F x) p u
lemma coin (h:Display H c)(x:X)(v:ℝ)(hv:c x v) : 0≤ v:=by
 obtain ⟨L,g,⟨p,b⟩,e⟩:= h.exists_T; exact (abs_nonneg _).trans ((e x ⟨_,hv⟩ _|>.1 hv) p b)
lemma captures (F:X→Y)[NormedAddCommGroup Y][NormedSpace ℝ Y](he:∀ v:Y→L[ℝ]ℝ,v ∘ F ∈ H): Display H (fun x b=> ‖F x‖≤ b):=by
 refine ⟨(fun p:Y→L[ℝ]ℝ=> p ∘ F) '' {p | ‖p‖ ≤ 1},?_, ⟨0, (0:Y→L[ℝ]ℝ), by simp,rfl⟩,?_⟩; · rintro k ⟨p,x,rfl⟩; exact he _
 intro x _ u; rw [forall_mem_image]; constructor; · intro h f a; rw [comp_apply,←Real.norm_eq_abs]; exact (f.le_opNorm _).trans ((mul_le_mul_of_nonneg_right (show ‖f‖≤1 from a) (norm_nonneg _)).trans ((one_mul _).trans_le h))
 intro h; obtain ⟨g,x',t⟩:= exists_dual_vector'' ℝ (F x); specialize @h g x'; rw [comp_apply,t] at h; exact (le_abs_self _).trans h
lemma sup (v:∀ a, Display H (d a)) : Display H (fun x u=> 0≤u ∧ ∀ j,d j x u):=by
 classical
 choose L g h p using fun a=> (v a).exists_T
 refine ⟨{0} ∪ ⋃ a, L a,union_subset (Set.singleton_subset_iff.mpr H.zero_mem) (iUnion_subset g), ⟨0,Or.inl rfl⟩,?_ ⟩
 rintro x ⟨v,V⟩ u; constructor
 · rintro ⟨Y,B⟩ f (r|e)
   · rw [show f=0 from r]; simpa using Y
   obtain ⟨i,h⟩:=mem_iUnion.mp e; exact (p i x ⟨_,V.2 i⟩ u).1 (B i) _ h
 intro B; exact ⟨by simpa using B 0 (Or.inl rfl),fun i=> (p i x ⟨_,V.2 i⟩ _).2 fun k h=>B k (Or.inr (mem_iUnion.mpr ⟨i,h⟩))⟩
lemma drug [Fintype i] [Nonempty j] (v:∀ a,Display H (d a))(W:j→i→ℝ)(p:∀ j i,0≤ W j i):
 Display H (fun x u=>∃ t:i→ℝ, (∀ i,d i x (t i)) ∧ ∀ j, ∑ i,W j i*t i≤u) :=by
 classical
 choose L g h q using fun a=> (v a).exists_T
 let G(A:j)(F:i→X→ℝ) (s:i→ℝ):X→ℝ:= ∑ i, (W A i*s i) • F i
 let T:Set (X→ℝ):= {f|∃ A F s,(∀ i,F i∈ L i ∧ |s i|=1) ∧ f= G A F s}
 refine ⟨T,?_ ,?_ ,?_ ⟩
 · rintro v ⟨A,F,s,p,rfl⟩; exact Submodule.sum_mem H (fun i _=> H.smul_mem _ (g i (p i).1))
 · choose F p using h; exact ⟨_,Classical.arbitrary j,F,fun _=>1,fun i=>⟨p i,abs_one⟩,rfl⟩
 rintro x ⟨v,S,Sp,Sv⟩ u; constructor
 · rintro ⟨v,ht,hv⟩ _ ⟨A,F,s,b,rfl⟩; simp only [G,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; refine le_trans (Finset.abs_sum_le_sum_abs (fun i=> W A i*s i*F i x) _) (le_trans ?_ (hv A)); refine Finset.sum_le_sum (fun i _=>?_ ); rw [abs_mul,abs_mul,abs_of_nonneg (p ..),(b i).2, mul_one]; exact mul_le_mul_of_nonneg_left ((q i x ⟨_, ht i⟩ (v i)).1 (ht i) _ (b i).1) (p ..)
 let A(i):= (fun f:X→ℝ => |f x|) '' (L i); let B(a:i):= sSup (A a); have ha(i):Set.Nonempty (A i):=(h i).image _
 intro z; refine ⟨B, fun a => (q a x ⟨_,Sp a⟩ _).2 fun f t=> le_csSup (s:=A a) ⟨S a, Set.forall_mem_image.mpr ((q a x ⟨_,Sp a⟩ _).1 (Sp a))⟩ (mem_image_of_mem _ t),fun j=>?_⟩
 let v:= W j; let X':=∑ i, v i; change ∑ i,v i * B i ≤ u; have hp:0≤ X':= Finset.sum_nonneg fun i _=> p j i
 refine le_of_forall_pos_le_add fun e pE=>?_ ; let σ:=e/(X'+1); have hs:0<σ:=by unfold σ; positivity
 have hs'(i):∃ f∈L i,B i ≤ |f x|+σ:=by obtain ⟨_,⟨f,u,rfl⟩,b⟩:= exists_lt_of_lt_csSup (ha i) (sub_lt_self (B i) hs); exact ⟨_,u,(sub_le_iff_le_add.mp b.le)⟩
 choose f a b using hs'; let s (i):ℝ:= if 0≤f i x then 1 else -1; have sK(i):|s i|=1:=by unfold s; split<;>simp
 have hh(i): (v i*s i) * f i x=v i*|f i x|:=by
    rw [mul_assoc]; unfold s; split
    next h=> rw [abs_of_nonneg h,one_mul]

    next h=> rw [abs_of_nonpos (le_of_not_ge h), neg_one_mul]
 specialize z _ ⟨j,f,s,fun i=>⟨a i,sK _⟩,rfl⟩; have hi:∑ i,v i *|f i x| ≤ u:=by
    apply le_trans _ ((le_abs_self _).trans z); dsimp only [G]; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; exact (Finset.sum_le_sum fun i _ => (hh i).symm.le)
 refine (Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (b i) (p ..)).trans ?_ ; simp_rw [mul_add,Finset.sum_add_distrib,←Finset.sum_mul]; refine add_le_add hi ?_ ; have pE:X' * σ + σ=e:=by unfold σ; field_simp
 exact pE ▸ le_add_of_nonneg_right hs.le
end Display
end YM.CF.Py.Rate
