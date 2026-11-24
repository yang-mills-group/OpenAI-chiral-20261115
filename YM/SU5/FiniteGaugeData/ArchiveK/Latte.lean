import YM.SU5.FiniteGaugeData.ArchiveK.Tuba
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
namespace Violas
-- numerical rank. concentrated projection via trace. build ARK of J movers. Avoid Matrix rank explicit. Preserve estimates. actual ‖W‖ via Engine.Small ℂ.
open LinearMap Submodule Module -- may conflict `re` etc
variable {X Y Z J:Type*}[Fintype X][Fintype Y][Fintype Z][DecidableEq X][DecidableEq Y][DecidableEq Z]
attribute [local instance] opCStarAlgebra
abbrev gas(A: Op X)(x: Ket X):ℝ:=(inner ℂ x (ract A x)).re
abbrev dim(P:Submodule ℂ (Ket X)):= finrank ℂ P
abbrev page(X:Type*)[Fintype X]:= Fintype.card X
abbrev PlansM(X:Type*)[Fintype X]:= Submodule ℂ (Ket X)
lemma book(X Y:PlansM Z) : dim X + dim Y ≤ page Z + dim (X⊓Y):=by let h:=finrank_sup_add_finrank_inf_eq X Y; rw [←h]; exact Nat.add_le_add_right ((Submodule.finrank_le (X⊔Y)).trans_eq finrank_euclideanSpace) _
lemma fees(U:PlansM X)(t:dim U>0): ∃ x:Ket X,x∈U ∧ x≠0:=by obtain ⟨x,h⟩:= (show ∃ x:U,x≠0 from (letI:Nontrivial U:= Module.nontrivial_of_finrank_pos t; exists_ne _)); exact ⟨x.val,x.property, fun z=> h (Subtype.ext z)⟩
lemma gramFee (F:Ruler X Y)(x:Ket Y) : gas (Fᴴ*F) x=‖ract F x‖^2 := by unfold gas; rw [Largo.R_mul,← R_adj, Matrix.conjTranspose_conjTranspose]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _ -- tune
section
variable (F:Ruler X Y)(x:Ket Y)(z:Ket X)
lemma adjacent : inner ℂ (ract F x) z=inner ℂ x (ract Fᴴ z) := by have he:= R_adj Fᴴ x z; rwa [Matrix.conjTranspose_conjTranspose] at he
lemma hurdler (F:Ruler X Y) : (Fᴴ*F).IsHermitian := (show (Fᴴ*F)ᴴ=Fᴴ*F from (by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]))
end
variable {A:Op X}(h:A.IsHermitian)
local notation "B"=> h.eigenvectorBasis
local notation "F"=> h.eigenvalues
def wood (a:ℝ) : Finset X:= Finset.univ.filter fun i:X=> a≤ h.eigenvalues i
include h
lemma beauty(i:X) : ract A (B i)=((F i:ℝ):ℂ) • B i:= by
 let Y:OrthonormalBasis X ℂ (Ket X):=B; let v:= h.mulVec_eigenvectorBasis i; apply PiLp.ext; intro x; rw [R_at]; have he:∀ p:Ket X,((F i:ℝ):ℂ) • p=(F i) • p:=by intros; exact Complex.coe_smul ..
 rw [he,v]; rfl
lemma beau(i:X) : gas A (B i)= F i:=by unfold gas; rw [beauty,inner_smul_right,inner_self_eq_norm_sq_to_K, h.eigenvectorBasis.orthonormal.1 i]; simp
-- express on span of S. pick representation.Inject.
def PitchB(P:Finset X): PlansM X:= Submodule.span ℂ (Set.range (fun i:P=> h.eigenvectorBasis i.val))
lemma forest (P:Finset X) : dim (PitchB h P)=P.card:= by let X:=fun i:P=>B i.val; unfold dim; rw [show finrank ℂ (PitchB h P)= _ from finrank_span_eq_card (h.eigenvectorBasis.orthonormal.linearIndependent.comp (fun i:P=>i.val) Subtype.val_injective)]; simp
lemma larch(P:Finset X) (x:Ket X)(Hx:x∈ PitchB h P) : ∑ i∈P,inner ℂ (B i) x • B i=x:=by
 let L(i:X):= inner ℂ (B i) x; have hzero(i:X)(t:i∉P):L i=0:=by
    refine span_induction (p:=fun x _=>inner ℂ (B i) x=0) ?_ (inner_zero_right ..) ?_ ?_ Hx; · rintro z ⟨j,rfl⟩; exact (h.eigenvectorBasis.orthonormal).2 (fun k=> t (k.symm ▸ j.property)) -- tune
    · intro p q _ _ u v; rw [inner_add_right,u,v,add_zero]
    intro p x _ v; rw [inner_smul_right,v,mul_zero]
 rw [Finset.sum_subset (Finset.subset_univ P) (fun i t p=> by rw [show inner ℂ (B i) x=0 from hzero i p, zero_smul])]; convert h.eigenvectorBasis.sum_repr x using 1; simp [OrthonormalBasis.repr_apply_apply] -- tune
-- decom rect test.
lemma controls(P:Finset X)(x:Ket X)(Hx:x∈ PitchB h P): let a(i:X):=‖inner ℂ (B i) x‖^2; ∑ i∈P,a i=‖x‖^2∧ gas A x=∑ i∈P,F i*a i:=by
 intro a; let k(i:X):= inner ℂ (B i) x; have he(i:X): (k i * inner ℂ x (B i)).re= a i:=by rw [← inner_conj_symm (𝕜:=ℂ) x (B i), show starRingEnd ℂ (inner ℂ (B i) x)=_ from rfl]; exact Eq.trans (congrArg Complex.re (Complex.mul_conj (k i))) (Complex.normSq_eq_norm_sq _)
 constructor
 · rw [← show (inner ℂ x x).re=‖x‖^2 from inner_self_eq_norm_sq (𝕜:=ℂ) x]; nth_rw 2 [←larch h P x Hx]; rw [inner_sum, Complex.re_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [inner_smul_right]; exact (he i).symm
 unfold gas; nth_rw 2 [←larch h P x Hx]; rw [map_sum,inner_sum, Complex.re_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul,beauty,inner_smul_right,inner_smul_right]; change (k i*(((F i:ℝ):ℂ)*_)).re=_; rw [mul_left_comm (k i),re_ofReal_mul]; rw [he]
lemma high_P (x:ℝ)(y:Ket X)(t:y∈ PitchB h (wood h x)) : x*‖y‖^2 ≤ gas A y:=by
 let a(i:X):=‖inner ℂ (B i) y‖^2; obtain ⟨u,v⟩:= controls h (wood h x) y t; rw [v,←u,mul_sum]; exact sum_le_sum fun i t=> mul_le_mul_of_nonneg_right ((mem_filter.mp t).2) (sq_nonneg _)
lemma lo_P (x:ℝ)(y:Ket X)(t:y∈ PitchB h (wood h x)ᶜ) : gas A y≤x*‖y‖^2:= by
 let a:= (wood h x)ᶜ; obtain ⟨u,v⟩:= controls h a y t; rw [v,←u,mul_sum]; refine sum_le_sum fun i t=> mul_le_mul_of_nonneg_right (le_of_not_ge ?_) (sq_nonneg _); -- tune le_of_not_ge concludes ???
 exact fun v=> (mem_compl.mp t) (mem_filter.mpr ⟨mem_univ i,v⟩)
#print axioms high_P
lemma frostD (a:ℝ) : dim (PitchB h (wood h a)) + dim (PitchB h (wood h a)ᶜ) = page X:= by rw [forest,forest]; simp [page]
lemma cold (a:ℝ):∃ U V: PlansM X,dim U+dim V=page X∧(∀ x∈ U,a*‖x‖^2 ≤ gas A x)∧∀ x∈V,gas A x ≤ a*‖x‖^2:=by exact ⟨_,_,frostD h a,high_P h a,lo_P h a⟩
-- if trace ≥3/4 b * N, each ≤b, ⇒ ≥ half N high at b/2. use for tang.
lemma polarCharge (a:ℝ)(ha:0<a)(v:A.trace.re≥3/4*a*((page X:ℕ):ℝ))(g:∀ x:Ket X,gas A x≤a*‖x‖^2): ∃ U:PlansM X,page X≤2*dim U∧(∀ x∈ U,a/2*‖x‖^2 ≤ gas A x):=by
 let S:= wood h (a/2); let T:=Sᶜ; have he:A.trace.re=∑ i,F i:=by rw [h.trace_eq_sum_eigenvalues,Complex.re_sum]; rfl
 have hk(i:X) : F i ≤ a:= (beau h i).symm ▸ (g (B i)).trans_eq (by rw [h.eigenvectorBasis.orthonormal.1 i,one_pow,mul_one]); -- tune
 have hl:A.trace.re≤ (S.card:ℝ)*a + (T.card:ℝ)*(a/2):=by rw [he,← Finset.sum_add_sum_compl S]; apply add_le_add (le_trans (sum_le_sum (g:=fun i=>a) (fun i _=>hk i)) (le_of_eq ?_)) (le_trans (sum_le_sum (g:=fun i=>a/2) (fun i t=>?_ )) (le_of_eq ?_)); simp; simp [T]; exact le_of_not_ge fun v=>(mem_compl.mp t) (mem_filter.mpr ⟨mem_univ _,v⟩) -- tune
 refine ⟨PitchB h S,?_,high_P h _⟩; have ht:(S.card:ℝ)+ (T.card:ℝ)= page X:= by exact_mod_cast (by simp [T,page]: S.card+T.card=page X);
 rw [forest]; have hy: (page X:ℝ)≤ 2*S.card:= le_of_not_gt fun z=>by nlinarith only [hl,v,mul_lt_mul_of_pos_left z ha, show a*((S.card:ℝ)+T.card)=a*page X from (congrArg (fun p=>a*p) ht)];
 exact_mod_cast hy
omit h
variable (P:Ruler X Y)
lemma frigo(a:ℝ)(t:0≤a):∃ U V: PlansM Y, dim U+dim V=page Y ∧ (∀ x∈ U,a*‖x‖≤ ‖ract P x‖) ∧ (∀ x∈ V, ‖ract P x‖ ≤ a*‖x‖):=by
 obtain ⟨U,V,h,H,K⟩:=cold (hurdler P) (a^2); refine ⟨U,V,h,fun i h=> ?_,fun i h=> ?_⟩ <;> rw [←sq_le_sq₀ (by positivity) (by positivity),mul_pow,←gramFee]; exact H i h; exact K i h
lemma combine (A:Finset J)(U:PlansM X)(W:J→ PlansM X)(c:J→ℕ)(p:∀ i∈ A, page X ≤ dim (W i)+c i): ∃ S:PlansM X,dim U ≤ dim S+∑ i∈A,c i ∧ S≤U ∧ ∀ i∈A,S≤ W i := by
 classical
 induction A using Finset.induction with
 | empty=> refine ⟨U,?_,le_rfl,?_⟩ <;> simp
 | insert i T b ih=>
    obtain ⟨S,a,u,Q⟩:= ih (fun i h=> p i (mem_insert_of_mem h)); have hv:=book S (W i); have hz:= p i (mem_insert_self ..); refine ⟨S⊓W i,?_,inf_le_left.trans u,fun j v=> ?_⟩; · rw [sum_insert b]; omega
    rcases mem_insert.mp v with v|v; · subst j; exact inf_le_right
    exact inf_le_left.trans (Q j v)
-- kernel dims rank.Users. mixing
lemma rootsF (W: X→ X) : True:=trivial -- ignore
lemma skim_ker (U V:PlansM X)(h:U ⊓ V=⊥): dim U+dim V ≤ page X:=by have he:=book U V; rw [h] at he; simpa [dim] using he
end Violas
end YM.CF.Window.ArchiveK
