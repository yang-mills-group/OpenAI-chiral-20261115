import YM.CF.BPress.Bias.Brim
import YM.CF.BPress.Pf.Log
import YM.CF.BPress.Spin.Reeds
/- color point blocks on the ACTUAL three generations together (all the Boots tests).
 Mismatch obstruction. Only distinctness of dictionaries bought here. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Finset Filter NormedSpace Metric Lattice Fock Laurent Bloch Next.Free Cube Fir Lat Spin Paint Rush Blank Nacre SU Tulip Spin.Cellar Spin.Cellar.Pass Spin.Hole Spin.Trans Spin.Pledge Spin.Stride Dial Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {N: Side} {j:ℕ} {M:Jill.Male} {P C:Op (Single N)} {u:Paint (More N)}
-- block read. row = first projection. lost heat.
abbrev Page := SpinIdx×Slot
def book (x y:Site N)(A:Op (Single N)): Op Page:=Matrix.of fun i j=> A ((x,i.1),i.2) ((y,j.1),j.2)
local notation "C[" u "]"=> Paint.coupling u -- warning inside vars
lemma leftC (x y:Site N)(A:Op (Single N)): book x y (C[u]*A)= nodeC (u (node x)) * book x y A:=by
 ext ⟨i,r⟩ ⟨j,t⟩; unfold book; simp only [Matrix.of_apply,Matrix.mul_apply, atX, Single,Fintype.sum_prod_type, ite_mul,zero_mul]; rw [sum_eq_single x]; · simp
 · intro i _ v; simp [Ne.symm v]
 simp -- tune
lemma rightC (x y:Site N)(A:Op (Single N)): book x y (A*C[u])= book x y A * nodeC (u (node y)):=by
 ext ⟨i,r⟩ ⟨j,t⟩; unfold book; simp only [Matrix.of_apply,Matrix.mul_apply,atX,Single,Fintype.sum_prod_type, mul_ite,mul_zero]; rw [sum_eq_single y]; · simp
 · intro i _ v; simp [v]
 simp -- atX home row choose conv
lemma book_sub (x y: Site N)(A B:Op (Single N)): book x y (A-B)= book x y A-book x y B:=rfl -- eta (? proof funext)
lemma book_cc (x y:Site N)(A:Op (Single N)): book x y (cc A)=cc (book x y A):=rfl
abbrev oxide (P:Op Page)(A B: Op Slot):= P*nodeC B-nodeC A*cc P
lemma twistC (x y: Site N): book x y (wash P C[u])=oxide (book x y P) (u (node x)) (u (node y)):=by rw [wash,book_sub,leftC,rightC,book_cc]
section Hue
variable {B U:Op Slot} {X Y: Op Page}
lemma nodeS(C:Op Slot): nodeC C=((1:Op SpinIdx) ⊗ₖ C)*nodeC (1:Op Slot):=by unfold nodeC; rw [op_kron_mul, one_mul,mul_one]
def prismC := {X : Op Page| ∀ A:Op Slot,oxide X A A=0}
lemma contextM(h:X∈prismC) (C:Op Slot) : Commute X ((1:Op SpinIdx) ⊗ₖ C):=by
 have hy:=sub_eq_zero.mp (h 1); let U:= (1:Op SpinIdx) ⊗ₖ C; let V:=nodeC (1:Op Slot); have hx: X*nodeC C=nodeC C*cc X:=sub_eq_zero.mp (h C)
 suffices p:X*U*V=U*X*V by
    have ht: (X*U)*(V*star V)=(U*X)*(V*star V):=by rw [←mul_assoc,p,mul_assoc]; -- helper
    have hv:V*star V=1:=(node_unit _ (unitary _).one_mem).2; rw [hv,mul_one,mul_one] at ht; exact ht
 rw [nodeS C, ←mul_assoc, mul_assoc U, ←show X*V=V*cc X from hy,←mul_assoc U] at hx; exact hx
lemma scalarAt(h:X∈prismC): ∃ f: Op SpinIdx, X=f⊗ₖ (1:Op Slot):=by
 let b:Slot:=Classical.arbitrary _; refine ⟨Matrix.of fun i j=> X (i,b) (j,b), ?_⟩; ext ⟨i,x⟩ ⟨j,y⟩; have ht:= Matrix.ext_iff.mpr (contextM h (Matrix.single y b (1:ℂ))).eq (i,x) (j,b); rw [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.mul_apply,Fintype.sum_prod_type] at ht; by_cases f:x=y; · subst x; simpa [Matrix.one_apply, Matrix.single,mul_ite,ite_mul] using ht
 simpa [Matrix.single,Matrix.one_apply,mul_ite,ite_mul,f,Ne.symm f] using ht
lemma definite(h:X∈prismC)(t:U≠ B)(g:oxide X U B=0): X=0:=by
 have he:X*(nodeC B-nodeC U)=0:=by rw [mul_sub,sub_eq_zero.mp g,sub_eq_zero.mp (h U),sub_self]
 obtain ⟨f,p⟩:= scalarAt h; rw [p,nodeC,nodeC,←op_kron_sub,op_kron_mul, one_mul] at he; have ht:f*spinJ=0:=by
    obtain ⟨i,h⟩:=Function.ne_iff.mp (show B-U ≠ 0 from sub_ne_zero.mpr (Ne.symm t)); obtain ⟨j,h⟩:=Function.ne_iff.mp h; ext a b; have hg:=Matrix.ext_iff.mpr he (a,i) (b,j); change (f*spinJ) a b*(B-U) i j=0 at hg; exact (mul_eq_zero.mp hg).resolve_right h
 have hv : f=0:=by nth_rw 1 [←mul_one f, ←spinJ_unitary.2]; rw [←mul_assoc,ht,zero_mul]
 rw [p,hv, Matrix.zero_kronecker]
private lemma contColour (A B:Op Slot) : Continuous (fun X:Op Page=> oxide X A B):= by
 unfold oxide; have ht: Continuous (cc : Op Page → Op Page):= continuous_matrix fun i j=> (Continuous.star (Continuous.matrix_elem continuous_id i j)); exact (continuous_id.mul continuous_const).sub (continuous_const.mul ht)
lemma ox_price (p:U≠B): ∃ c:ℝ,0<c ∧ ∀ X∈prismC,c*‖X‖ ≤ ‖oxide X U B‖:=by
 let f: Op Page→ℝ:=fun X=> ‖oxide X U B‖; let S:= prismC ∩ Metric.sphere 0 1; have ht:IsClosed prismC:= by rw [show prismC=⋂ K:Op Slot,{X:Op Page|oxide X K K=0} by ext; simp; rfl]; exact isClosed_iInter fun i=> isClosed_eq (contColour i i) continuous_const
 have hp: ∃ c:ℝ,0<c ∧ ∀ X∈S,c≤f X:=by
    cases S.eq_empty_or_nonempty with
    | inl h=> exact ⟨1,one_pos,by rw [h]; simp⟩
    | inr h=>
      have H:IsCompact S:= (isCompact_sphere ..).inter_left ht; obtain ⟨i,h,e⟩:= IsCompact.exists_isMinOn H h (contColour U B).norm.continuousOn; refine ⟨f i,?_ ,e⟩; have hx : ‖i‖=(1:ℝ):=by simpa using h.2
      refine norm_pos_iff.mpr ?_; intro g; simp [definite h.1 p g] at hx
 have hv(A B:Op Slot)(x:ℝ)(u:Op Page): oxide (x • u) A B=x • oxide u A B:=by unfold oxide; rw [cc_rsmul,Algebra.mul_smul_comm, Algebra.smul_mul_assoc,smul_sub]
 obtain ⟨c,v,V⟩:= hp; refine ⟨c,v,fun X h=>?_⟩; by_cases s:X=0; · simp [s,oxide]
 have hy:0<‖X‖:=norm_pos_iff.mpr s; have ht : ‖X‖⁻¹ • X∈ S:= ⟨fun V=>by rw [hv,h V,smul_zero], mem_sphere_zero_iff_norm.mpr (by rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hy.ne'])⟩
 have he:= V _ ht; unfold f at he; rw [hv,norm_smul,Real.norm_of_nonneg (by positivity),mul_comm, ← div_eq_mul_inv] at he; exact (le_div_iff₀ hy).mp he
end Hue
variable {r c:ℝ} (h:Bore P (coupling u) r)
lemma toll_r : ∀ t:Finset (Per N),∀ M (v:ℝ),let S:=Lower t; let A:=nativeX j M N; (1≤j)→Pass (pos S) (Hole.neg S) (loose S) A v → Boots (ramp (loose S) (pos S) A):=by
 intro t M v S A p H; rw [show ramp (loose S) (pos S) A=smoothP (pos S) (Hole.neg S) (loose S) A 0-pos S by rw [H.mark_exit]; abel]; have he : Boots A:= by unfold A; rw [nativeEq p]; exact fun W=> free_anti j p M W
 refine Boots.sub (Boots.roots H he 0 (by simp)) ?_; intro X T; rw [show cc (pos S)=pos S from cut_real _]; exact (coupling_lock _ _).symm -- tune
abbrev ash (x:Site N) (P:Op (Single N)):= (book x x P).trace.re
lemma ash_ord {A B:Op (Single N)}(p:A ≤ B)(x:Site N): ash x A≤ash x B:=by
 unfold ash Matrix.trace; simp only [Complex.re_sum,Matrix.diag_apply,book, Matrix.of_apply]; refine sum_le_sum fun i _=>?_ ; let X:Single N:=((x,i.1),i.2); have hp:= Quad.e_mono p (basisKet X); unfold Quad.energy at hp; simpa using hp
private lemma geh (b:Op (Single N))(i j :Single N) : ‖b i j‖^2 ≤ ((b*star b) i i).re:=by
 rw [Matrix.mul_apply,Complex.re_sum]; have he(j): (b i j*star b j i).re=‖b i j‖^2:=inner_self_eq_norm_sq (𝕜:=ℂ) (b i j); simp_rw [he]; exact single_le_sum (f:=fun j=>‖b i j‖^2) (fun i _=>sq_nonneg _) (mem_univ j)
local notation "Y0"=>C[u]
include h
lemma warmth (x:Site N)(i:Single N)(j:Single N)(t:penX i=x) : ‖(P*Y0*(1-cc P)) i j‖^2 ≤ ash x (lost P (coupling u)):=by
 have hx:= ash_ord h.PSD x; rw [h.portion]; let B:=P*Y0*(1-cc P); apply (geh _ i j).trans; unfold ash Matrix.trace; rw [Complex.re_sum]; let F(r:Page):ℝ:=((book x x (B*star B)).diag r).re; change ((B*star B) i i).re ≤ ∑ k,F k; suffices z:F (i.1.2,i.2)=((B*star B) i i).re by rw [←z]; exact single_le_sum (f:=F) (fun p _=> show 0≤((B*star B) ((x,p.1),p.2) ((x,p.1),p.2)).re from (sq_nonneg _).trans (geh B ((x,p.1),p.2) j)) (mem_univ ((i.1.2,i.2):Page))
 subst x; rfl
private lemma transpose_tax : P* Y0*(1-cc P)= -( (1-P)*Y0*cc P)ᵀ:=by
 rw [Matrix.transpose_mul,Matrix.transpose_mul,ccT,h.p.isSelfAdjoint,h.sk,Matrix.transpose_sub,Matrix.transpose_one,show Pᵀ=cc P by rw [cc,h.p.isSelfAdjoint], neg_mul, mul_neg,neg_neg,mul_assoc]
lemma warmth_wash (x y: Site N)(i j:Single N)(s:penX i=x)(u':penX j=y): ‖wash P (coupling u) i j‖ ≤ Real.sqrt (ash x (lost P (coupling u)))+ Real.sqrt (ash y (lost P (coupling u))):=by
 let D:=P*Y0*(1-cc P); let F:=(1-P)*Y0 *cc P; have ht:= transpose_tax h; change D= -Fᵀ at ht; have hp: wash P Y0=D-F:=by unfold D F wash; rw [mul_sub,mul_one,sub_mul,sub_mul,one_mul]; abel
 have hx:= Real.le_sqrt_of_sq_le (warmth h y j i u'); rw [hp,Matrix.sub_apply]; apply (norm_sub_le ..).trans; apply add_le_add (Real.le_sqrt_of_sq_le (warmth h x i j s)); change ‖D j i‖ ≤ _ at hx; rwa [ht,Matrix.neg_apply,Matrix.transpose_apply,norm_neg] at hx
omit h in
theorem C_entry {U B: Op Slot}(v:U≠B):∃ K:ℝ, 0<K ∧ ∀ (N:Side) (r:ℝ)(P: Op (Single N))(u: Paint (More N)), Bore P (coupling u) r → Boots P→∀ (i j: Single N), let x:= penX i; let y:= penX j; u (node x)=U →u (node y)=B → ‖P i j‖ ≤ K*(Real.sqrt (ash x (lost P (coupling u)))+ Real.sqrt (ash y (lost P (coupling u)))):=by
 obtain ⟨c,p,H⟩:=ox_price v; let C:ℝ:= Fintype.card Page; have hx:0<C:=Nat.cast_pos.mpr Fintype.card_pos
 refine ⟨C/c,div_pos hx p, ?_⟩; intro N r P u h b i j x y hw hz; let A:=book x y P; let Y:=oxide A U B; let K(x:Site N):= Real.sqrt (ash x (lost P (coupling u)))
 have he:‖Y‖≤C*(K x+K y):=by
    have ht:book x y (wash P C[u])=Y:=by unfold Y; rw [twistC,hw,hz]
    rw [← ht]; exact Sods.cost_D _ (fun a r=> warmth_wash h x y ((x,a.1),a.2) ((y,r.1),r.2) rfl rfl) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
 have ht(c:Op Slot):oxide A c c=0:=by
    change oxide _ ((fun _:Site (More N)=>c) (node x)) ((fun _:Site (More N)=>c) (node y))=0; rw [← twistC (P:=P) (u:=fun _=>c) x y,wash,b c,sub_self]; rfl -- tune
 apply le_trans (norm_entry A (i.1.2,i.2) (j.1.2,j.2)); rw [div_mul_eq_mul_div,le_div_iff₀ p,mul_comm _ c]; exact (H A ht).trans he
end YM.CF.BPress.Bias
