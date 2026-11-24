import YM.CF.BPress.Spin.Lock
/-! Model configurations for anti-intertwiners on the conditioned projection: arbitrary constant-color fields, no continuity assertion on models. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin.Hole
open Function Filter NormedSpace Finset Lattice SU Lat Fock Cube Tenant Branch Tulip Scroll Dial Thera Nacre Laic Paint Eye Pledge Stride Quad Blank Cellar Cellar.Pass
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{A B L P:Op (Single N)}{c:ℝ}{S:Support N}
def Boots (A:Op (Single N)):Prop := ∀ v: Op Slot, let B := coupling (N:=N) (fun _=>v); A*B=B*cc A
namespace Boots
lemma one (N:Side): Boots (N:=N) 1:=by intro v B; simp
lemma add(h:Boots A)(g:Boots B): Boots (A+B):=by intro v X; rw [add_mul,cc_add,mul_add,h v,g v]
lemma sub(h:Boots A)(g:Boots B): Boots (A-B):=by intro v X; rw [sub_mul,cc_sub,mul_sub,h v,g v]
lemma scale(h:Boots A)(u:ℝ): Boots (u • A):=by intro v X; rw [cc_rsmul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,h v]
lemma mul(h:Boots A)(g:Boots B): Boots (A*B):=by intro v X; rw [cc_mul,mul_assoc, g v, ←mul_assoc A,h v,mul_assoc]
lemma reflect(h: Boots A): Boots (star A):=by
 intro v X; let B:=coupling (N:=N) (fun _=>vᵀ); have he:Bᵀ= -X:=by
   have hJ : spinJᵀ= -spinJ:= by have ht:= spinJ_real; unfold cc at ht; rw [←ht, Matrix.transpose_transpose,ht,spinJ_star]
   unfold B X; rw [coupling_const, ←Matrix.kroneckerMap_transpose,Matrix.transpose_transpose, coupling_const]; ext ⟨⟨x,i⟩,a⟩ ⟨⟨y,j⟩,b⟩; by_cases hx:x=y; simp only [hx,Matrix.kroneckerMap_apply,Matrix.transpose_apply, jump_apply,Equiv.refl_apply,ite_true, show spinJ j i= -spinJ i j from Matrix.ext_iff.mpr hJ i j,Matrix.neg_apply,neg_mul]; simp [hx,Ne.symm hx,jump_apply]
 have hp:= congrArg Matrix.transpose (h vᵀ); change (A*B)ᵀ=(B*cc A)ᵀ at hp; rw [Matrix.transpose_mul,Matrix.transpose_mul,he,Fock.ccT, neg_mul,mul_neg, show Aᵀ=cc (star A) by simp [cc],neg_inj] at hp; exact hp.symm
lemma invert (h:Boots A)(p:IsUnit A) : Boots A⁻¹:=by
 intro v B; let t:= live p; have he:cc A*cc A⁻¹=1:=by rw [←cc_mul, t.1,cc_one]
 have hv: A⁻¹*B=A⁻¹*B*(cc A*cc A⁻¹):=by rw [he,mul_one]
 rw [hv,←mul_assoc,mul_assoc A⁻¹ B, ←h v, ←mul_assoc,t.2,one_mul]
lemma ready1 (p:Trans.Ready c A B)(h:Boots A)(g:Boots B): Boots (Trans.beam A B):= hF -- tune
where hF : Boots (Trans.beam A B):=g.mul (((((g.reflect.mul g).add ((one N).sub h)).invert p.live_G).mul g.reflect))
lemma roots (X: Pass (Hole.pos S) (Hole.neg S) (loose S) A c)(h:Boots A)(v:ℝ)(p:‖v‖≤1): Boots (smoothP (Hole.pos S) (Hole.neg S) (loose S) A v):=by
 have hB(u:Bool): Boots (Lock S u):=by intro v T; rw [show cc (Lock S u)=Lock S u from cut_real _]; exact (coupling_lock _ u).symm
 let f:= hB true; let g:=hB false; have ht: Boots (rent1 (Hole.pos S) A):= ready1 X.gate1 f (h.mul f); have hh:= ((one N).sub (f.add g)); let L:=loose S; have hh: Boots L:= by unfold L; rw [X.l0]; exact hh
 exact ready1 (X.enjoy _ p) h ((((f.add (hh.scale v)).add (g.scale (v^2))).mul ht).add ((hh.add (g.scale v)).mul (h.sub ht)))
end Boots

def leak(A:Op (Single N))(C: Paint (More N)):= (1-A)*coupling C*cc A
lemma none_leak {C:Paint (More N)}(p:IsStarProjection A)(h:A*coupling C=coupling C*cc A) : leak A C=0:= by unfold leak; rw [mul_assoc,←h, ←mul_assoc,p.one_sub_mul_self,zero_mul]
lemma hole_free (h:Boots A)(X: Pass (pos S) (neg S) (loose S) A c)(x: Op Slot)(u:ℝ)(p:‖u‖≤1): leak (smoothP (pos S) (neg S) (loose S) A u) (fun _=>x)=0:= none_leak (X.stamped u p) (Boots.roots X h u p x)
lemma leak_bound (p:IsStarProjection A)(U:Paint (More N))(c:ℝ)(g:‖wash A (coupling U)‖≤c):‖leak A U‖≤c:=by
 let W:= coupling U; rw [show leak A U=(1-A)*-(wash A W) by unfold leak wash; rw [mul_neg,mul_sub,←mul_assoc (1-A) A,p.one_sub_mul_self,zero_mul,zero_sub,neg_neg,mul_assoc]]; apply (norm_mul_le ..).trans; rw [norm_neg]; exact (mul_le_of_le_one_left (norm_nonneg _) (p.one_sub.norm_le _)).trans g
lemma leak_sub(U V:Paint (More N)): leak A U-leak A V=leak A (U-V):=by unfold leak; simp only [coupe_sub,mul_sub, sub_mul,one_mul]
lemma norm_from_node (U:Paint (More N))(c:ℝ)(p:0≤c)(h:∀ x:Site N, ‖U (node x)‖≤c): ‖coupling U‖≤c:=by rw [coupling,love_money]; exact jump_bound _ _ p fun i=> (node_low ..).trans (h _)
lemma leak_from_node (h:IsStarProjection A)(U:Paint (More N))(c:ℝ)(p:0≤c)(g:∀ x:Site N, ‖U (node x)‖≤c): ‖leak A U‖ ≤ c:= by
 apply (norm_mul_le ..).trans; rw [norm_cc]; apply (mul_le_of_le_one_right (norm_nonneg _) (h.norm_le _)).trans; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (h.one_sub.norm_le _)).trans (norm_from_node U c p g))

-- split W-space; leakage with ℙ vacant can adjust H on those sites without changes.
lemma shadowed (U:Paint (More N))(h:∀ x: Site N,x∉S→U (node x)=0): coupling U*loose S=0:=by
 unfold loose; rw [mul_sub, mul_one, sub_eq_zero]; ext i j; rw [look_right]; split_ifs with e; rfl; rw [atX]; split_ifs with he; swap; · rfl
 rw [show U (home N i)=0 from h i.1.1 fun t=>e (mem_image.mpr ⟨_,t,congrArg node he⟩)]; simp [nodeC]
lemma leak_shadow (U:Paint (More N))(h:∀ x: Site N,x∉S→U (node x)=0) (X: Pass (pos S) (neg S) (loose S) A c): leak (pos S+ramp (loose S) (pos S) A) U=0:=by
 let V:= ramp (loose S) (pos S) A; let K:= coupling U; let L:=loose S; let D:=pos S; have he:cc D=D:=cut_real _; have hg:cc L=L:= cut_real' -- tune
 have hp: V*K=0:=by nth_rw 1 [← (across X.toEmpties.r X.ramp_star X.ramp_L : V*L=V)]; rw [mul_assoc,← loose_lock, shadowed U h,mul_zero] -- tune ns
 have ht: K*cc V=0:=by nth_rw 1 [← (show L*V=V from X.ramp_L)]; rw [cc_mul,hg,←mul_assoc,shadowed U h,zero_mul]
 refine none_leak ?_ ?_; exact climax X.p X.ramp_P X.ramp_star; change (D+V)*K=K*cc (D+V); rw [add_mul,cc_add,mul_add, hp, he, coupling_lock,ht] -- order wrong
where cut_real': cc (loose S)= loose S:=by rw [loose,cc_sub,cc_one]; congr 1; exact cut_real _
lemma back_cost (X: Pass (pos S) (neg S) (loose S) A c)(h:Boots A)(C:Paint (More N))(m:Op Slot)(a:ℝ)(p:0≤a)(t:∀ x:Site N,x∉S→‖C (node x)-m‖≤a): ‖leak (smoothP (pos S) (neg S) (loose S) A 0) C‖≤a:=by
 let P:=pos S+ ramp (loose S) (pos S) A; let K(x:Site (More N)):= if x∈ wings S then m else C x
 have hp: leak P C=leak P K:=sub_eq_zero.mp (by rw [leak_sub]; apply leak_shadow (X:=X); intro i p; simp [K,wings,needle.eq_iff,p])
 let W:Paint (More N):=fun _=>m; have ht:leak P W=0:= by unfold P; rw [←X.mark_exit]; exact hole_free h X m 0 (by simp)
 rw [X.mark_exit,hp]; nth_rw 1 [← sub_zero (leak _ K)]; rw [←ht,leak_sub];
 apply leak_from_node (by unfold P; rw [←X.mark_exit]; exact X.stamped 0 (by simp)) _ a p; intro i; by_cases l:i∈S
 · simp [K,wings,needle.eq_iff,l,W,p]
 simpa [K,wings,needle.eq_iff,l,W] using t i l
end YM.CF.BPress.Spin.Hole
