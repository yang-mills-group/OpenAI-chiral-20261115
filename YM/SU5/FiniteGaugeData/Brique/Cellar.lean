import YM.SU5.FiniteGaugeData.Brique.Wood
import YM.CF.Buffered.Mark
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Fock.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Tenant Tulip Peaks Buffered Spire
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
section
variable {S T:Finset I} {P Q:Op I}
/- block structure without copying growing budgets -/
structure Cellar (S:Finset I)(P:Op I): Prop where
  leftP : cutM S * P=P
  rightP : P*cutM S=P
lemma cut_meet (S T:Finset I): cutM S*cutM T=cutM (S∩T):=by
 apply op_columns; intro i; rw [act_mul,cut_basis,cut_basis]; by_cases h:i∈ T; rw [if_pos h,cut_basis]; simp [h]; rw [if_neg h,map_zero]; simp [h]
lemma cut_air (S T:Finset I)(h:Disjoint S T): cutM S*cutM T=0:=by
 rw [cut_meet, disjoint_iff_inter_eq_empty.mp h]; apply op_columns; intro i; simp [cut_basis]
lemma cut_disj (t:Disjoint S T): cutM (S∪T)=cutM S + cutM T:= by
 apply op_columns; intro i; rw [act_add,cut_basis,cut_basis,cut_basis]; by_cases h:i∈ S <;> by_cases g:i∈ T <;> simp [h,g]; exact False.elim (Finset.disjoint_left.mp t h g)
lemma Cellar.left_data (v: cutM S*P=P)(u:IsSelfAdjoint P) : Cellar S P:= ⟨v,by rw [← u.star_eq,← (cutM_idp S).2.star_eq,← star_mul,v]⟩
lemma Cellar.stock (t:Cellar S P)(h:S⊆T): Cellar T P:=by
 constructor
 · nth_rw 1 [← t.leftP]; rw [← mul_assoc,cut_meet,inter_eq_right.mpr h,t.leftP]
 nth_rw 1 [←t.rightP]; rw [mul_assoc,cut_meet,inter_eq_left.mpr h,t.rightP]
lemma Cellar.add (t:Cellar S P)(v:Cellar S Q): Cellar S (P+Q):=by
 constructor; rw [mul_add,t.leftP,v.leftP]; rw [add_mul,t.rightP,v.rightP]
lemma Cellar.starP (t:Cellar S P): Cellar S (star P):=by
 constructor; rw [← (cutM_idp S).2.star_eq,←star_mul,t.rightP]; rw [← (cutM_idp S).2.star_eq,←star_mul,t.leftP]
lemma Cellar.orthProd (t:Cellar S P)(v:Cellar T Q)(h:Disjoint S T): P*Q=0:=by
 rw [←t.rightP, ←v.leftP, mul_assoc,←mul_assoc (cutM S),cut_air _ _ h,zero_mul,mul_zero]; -- tune occurrence
lemma duo_orth (p:IsStarProjection P)(q:IsStarProjection Q)(e:P*Q=0): IsStarProjection (P+Q):=by
 have he:Q*P=0:=by rw [← p.2.star_eq,←q.2.star_eq,←star_mul,e,star_zero]
 exact ⟨by unfold IsIdempotentElem; rw [mul_add,add_mul,add_mul,(show P*P=P from p.1),(show Q*Q=Q from q.1),e,he,add_zero,zero_add],by unfold IsSelfAdjoint; rw [star_add,p.2.star_eq,q.2.star_eq]⟩
lemma Cellar.pythe (u: Cellar S P)(v:Cellar T Q)(h:Disjoint S T)(x:Ket I): ‖acts (P+Q) x‖^2=‖acts P x‖^2+‖acts Q x‖^2:=by
 rw [act_add]; simp only [sq]; apply norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜:=ℂ) -- check
 nth_rw 1 [←star_star P]; rw [act_inner,←act_mul,u.starP.orthProd v h,act_zero,inner_zero_right]
lemma Cellar.stockC (S:Finset I): Cellar S (cutM S):= ⟨(cutM_idp S).1,(cutM_idp S).1⟩
lemma duo_max [Nonempty I] (u:Cellar S P) (v:Cellar T Q)(h:Disjoint S T){r:ℝ}(p:‖P‖≤r)(q:‖Q‖≤r): ‖P+Q‖ ≤ r:=by
 have ht:0≤r:=(norm_nonneg _).trans p
 rw [←Matrix.l2_opNorm_toEuclideanCLM]; apply ContinuousLinearMap.opNorm_le_bound _ ht; intro x; change ‖acts (P+Q) x‖ ≤ _
 have he {A:Op I}{S:Finset I}(u:Cellar S A)(p:‖A‖≤r) : ‖acts A x‖^2 ≤ r^2 * ‖acts (cutM S) x‖^2 := by
    nth_rw 1 [←u.rightP]; rw [←mul_pow,act_mul]; exact pow_le_pow_left₀ (norm_nonneg _) ((Flare.opy ..).trans (mul_le_mul_of_nonneg_right p (norm_nonneg _))) 2
 have hp: ‖acts (cutM (S∪T)) x‖ ≤ ‖x‖:= (Flare.opy ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).norm_le _));
 refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht (norm_nonneg _))).1 ?_; rw [u.pythe v h,mul_pow]; exact (add_le_add (he u p) (he v q)).trans (by rw [←mul_add,← Cellar.pythe (Cellar.stockC S) (Cellar.stockC T) h,←cut_disj h]; gcongr)
lemma Cellar.no_room (S:Finset I):Cellar S 0:=by constructor; rw [mul_zero]; rw [zero_mul]
lemma Cellar.stanch (S:Finset I)(x:Ket I) : withinM S (acts (cutM S) x) := by unfold withinM; rw [←act_mul, show cutM S * cutM S=_ from (cutM_idp S).1]
-- Subset, even rotated.
lemma Cellar.acts_t (v: Cellar S P)(x:Ket I): withinM S (acts P x) := by unfold withinM; rw [←act_mul,v.leftP]
lemma Cellar.twist_t (u:UNI I)(v:Cellar S P)(h:twist u (cutM S)=cutM T): Cellar T (twist u P) := by
 constructor; rw [←h,←map_mul,v.leftP]; rw [←h,←map_mul,v.rightP]
end
section
variable {N:Side}{s t:Support (More N)}
local notation "ϕ"=> Single N
local notation "μ" T:max=> modesIn N T
local notation "Μ" T:max=> cutM (μ T)
variable (a:Axis) (z:ℤ)
set_option quotPrecheck false
local notation "U" => Buffered.carR a z N
local notation "X" => fun i: Support (More N) => i.image ((plane a z).anon N)
abbrev Neighbor (w:ℕ) (A:Op (Single N)) := ∀ (S T:Support (More N)), Lattice.halo w S⊆T → Μ S * A * Μ T= Μ S * A
variable {w:ℕ}{A B:Op (Single N)}
lemma neighbor_entry (h:∀ i j:Single N, w < separation (node i.1.1) (node j.1.1) → A i j=0) : Neighbor w A:=by
 intro S T t; ext i j; unfold cutM; rw [Matrix.mul_diagonal]; by_cases e:j∈μ T; rw [if_pos e,mul_one]; rw [if_neg e,mul_zero,Matrix.diagonal_mul]; by_cases f:i∈μ S; swap; · rw [if_neg f,zero_mul]
 rw [if_pos f,h,one_mul]; refine lt_of_not_ge (fun u=> e ((modes_at ..).mpr (t (halo_spec.mpr ⟨node i.1.1,(modes_at ..).mp f, u⟩)))) -- orientation
lemma neighbor_iff (h:Neighbor w A)(i j:Single N)(u:w< separation (node i.1.1) (node j.1.1)): A i j=0:=by
 let S: Support (More N):={node i.1.1}; let T:=Lattice.halo w S; let v:= h S T le_rfl; have he : ¬ node j.1.1∈T:=by intro t; have hh:= halo_spec.mp t; exact u.not_ge (by simpa [S] using hh)
 have hx:= congr_fun (congr_fun v i) j; simpa [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul,(show i∈μ S from by simp [S]),(show node i.1.1 ∈ S from mem_singleton_self _),he] using hx.symm
lemma reflect_halo (i:Support (More N))(w:ℕ):X (Lattice.halo w i)=Lattice.halo w (X i):=by
 let F:Site (More N)→Site (More N):= (Buffered.plane a z).anon N; have hp(x y):separation (F x) (F y)=separation x y:=by unfold F Shape.anon affine; rw [separation_translate,separation_signed]
 ext j; constructor
 · intro t; obtain ⟨s,u,rfl⟩:= mem_image.mp t; obtain ⟨b,v,t⟩:=halo_spec.mp u; exact halo_spec.mpr ⟨F b,mem_image_of_mem _ v,(hp _ _).trans_le t⟩
 intro g; obtain ⟨s,u,t⟩:= halo_spec.mp g; obtain ⟨b,v,rfl⟩:= mem_image.mp u; have h(i):F (F i)=i:= fling_there a z i; refine mem_image.mpr ⟨F j,halo_spec.mpr ⟨b,v,?_⟩,h _⟩; exact (hp _ _).symm.trans_le (by rw [h]; exact t)
lemma Neighbor.reoriented (h:Neighbor w A): Neighbor w (twist U A):=by
 intro S T t; have he: Lattice.halo w (X S)⊆ X T:=by rw [← reflect_halo]; exact image_mono _ t
 have hh:=congrArg (twist U) (h _ _ he); rw [map_mul,map_mul, refl_modes,refl_modes] at hh; dsimp only at hh; rw [fling_image,fling_image] at hh; exact hh -- beta?
lemma Neighbor.r_back (h:Neighbor w A): Neighbor w (twist (star U) A):=by
 -- no sign proof: push to tw; note twiststar U; direct
 intro S T t; have he: Lattice.halo w (X S)⊆ X T:=by rw [← reflect_halo]; exact image_mono _ t
 have hz (S : Support (More N)): twist (star U) (Μ (X S))=Μ S:= by rw [← refl_modes a z S, twist_inv]
 have hh:= congrArg (twist (star U)) (h _ _ he); rw [map_mul,map_mul,hz S,hz T] at hh; exact hh
lemma Neighbor.expanded (h:Neighbor w A)(p:Cellar (μ s) B)(e:Lattice.halo w s⊆t): Cellar (μ t) (B*A) := by
 have ht: s⊆t:=Subset.trans (halo_subset ..) e; constructor; rw [←mul_assoc,(p.stock (modes_monotone ht)).leftP]; nth_rw 1 2 [←p.rightP]; rw [mul_assoc,mul_assoc,mul_assoc]; -- tune
 rw [← mul_assoc (Μ s), h _ _ e]
lemma Halo_unionB (S T: Support (More N))(w:ℕ):Lattice.halo w (S∪T)= Lattice.halo w S ∪ Lattice.halo w T:= by ext; simp only [halo_spec,mem_union]; grind
lemma modes_orth (g:Disjoint s t): Disjoint (μ s) (μ t):=disjoint_left.mpr fun _ h p=> Finset.disjoint_left.mp g ((modes_at ..).mp h) ((modes_at ..).mp p) -- implicits lamb order
end
end YM.CF.Fock.Brique
