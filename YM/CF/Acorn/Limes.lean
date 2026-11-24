import YM.CF.Acorn.Maze
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Matrix NormedSpace Finset Fock Jet Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {n Y D:Type} [LinearOrder n][Fintype n][Fintype Y][DecidableEq Y][TopologicalSpace D]
abbrev Tiny (Y D n:Type):= Capot n Y D
def Drop (X:Master D Y)(H:n→Y)(a:ℝ)(i:I n)(L:D→FC n)(V:ℝ):Prop:= ∃ (J:Type) (_:Fintype J)(v:J→Seal Y × I n × (D→ℂ) × ℝ),
 (∀ j,let (S,k,f,r):=v j; Pro X S f r ∧ (r≠0→ H i.2∈S∧H k.2∈S))∧(∑ i,rent a (v i).1*(v i).2.2.2) ≤ V∧∀ x,L x=∑ j,(v j).2.2.1 x • pen (v j).2.1
variable {X:Master D Y} {O:n→Y}{a v c w H L h:ℝ}{M N:D→ FC n}{i j:I n}{R S:Seal Y}
namespace Drop
lemma more (p:Drop X O a i M c)(g:c≤L):Drop X O a i M L:=by obtain ⟨j,g',V,v,k,u⟩:=p; exact ⟨j,g',V,v,k.trans g,u⟩
lemma add(p:Drop X O a i M c)(g:Drop X O a i N L):Drop X O a i (M+N) (c+L):=by
 obtain ⟨i,h,v,t,l,m⟩:=p; obtain ⟨j,h',W,s,k,V⟩:=g; refine ⟨i⊕j,inferInstance, Sum.elim v W,?_,?_,?_⟩
 · rintro (i|j); exact t i; exact s j
 · simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]; exact add_le_add l k
 intro x; simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.add_apply,m,V]
lemma fixed (X:Master D Y)(i:I n)(O:n→Y)(a:ℝ):Drop X O a i (fun _=> pen i) (Real.exp a):=by
 let v : Seal Y:={O i.2}
 refine ⟨Unit,inferInstance,fun _=>(v,i,(fun x:D=>(1:ℂ)),‖(1:ℂ)‖),fun x=> ⟨Pro.nonzero (X:=X) v (fun _=> Grove.single _),fun t=>⟨mem_singleton_self _,mem_singleton_self _⟩⟩,by simp [v,rent],by simp⟩
lemma copp (p:Drop X O a i M c)(g:Drop X O a j N v)(hp:0≤a)(hk:c≤w){f:D→ℂ}{r:ℝ}(u:Pro X S f r)(hu:r≠0→R⊆ S ∧ O i.2∈S ∧ O j.2∈ S) : Carries X O R a h (fun x=> f x • (M x*N x)) ((worth X.k)^2*cost a R S*h^2*r*w*v) :=by
 obtain ⟨b,hB,U,t,l,m⟩:=p; obtain ⟨d,E,V,s,k,W⟩:=g
 let A:=worth X.k; have ha:0≤A:=by have he:=one_w X.k; exact zero_le_one.trans he
 let rite (z:b×d):Capot n Y D := let x:=U z.1; let y:=V z.2; ((S∪x.1)∪y.1,[x.2.1,y.2.1],(f*x.2.2.1)*y.2.2.1,A*(A*r*x.2.2.2)*y.2.2.2)
 have hx(q): Pro X (U q).1 (U q).2.2.1 (U q).2.2.2:= (show _ ∧ _ from t q).1
 have hy(q): Pro X (V q).1 (V q).2.2.1 (V q).2.2.2:= (show _ ∧ _ from s q).1
 refine ⟨_,inferInstance,rite,fun z=>?_,?_,?_⟩
 · rcases z with ⟨x,y⟩
   have he(p:(U x).2.2.2≠0) := (show _ ∧ _ from t x).2 p -- tune
   have hg(p:(V y).2.2.2≠0) := (show _∧ _ from s y).2 p
   refine ⟨(u.twice (hx x) (fun p k=>⟨O i.2, mem_inter.mpr ⟨(hu p).2.1,(he k).1⟩⟩)).twice (hy y) (fun p k=>?_),fun l=> ?_⟩
   · have ht:=right_ne_zero_of_mul (left_ne_zero_of_mul p); exact ⟨O j.2,mem_inter.mpr ⟨mem_union_left _ ((hu ht).2.2),(hg k).1⟩⟩
   change A*(A*r*_)*_≠0 at l; have hr:=right_ne_zero_of_mul (left_ne_zero_of_mul l); have hb:=left_ne_zero_of_mul hr
   refine ⟨((hu (right_ne_zero_of_mul hb)).1.trans subset_union_left).trans subset_union_left, ⟨1,rfl⟩,fun i h=>?_⟩; rcases List.mem_cons.mp h with ht|ht
   · subst i; exact mem_union_left _ (mem_union_right _ (he (right_ne_zero_of_mul hr)).2)
   rw [List.mem_singleton.mp ht]; exact mem_union_right _ (hg (right_ne_zero_of_mul l)).2
 · let T:= A^2*cost a R S*h^2*r; have hv:0≤T:=by unfold T; have hr:=u.pos; have hc:0<cost a R S:=rent_pos ..; positivity
   let f(q):= rent a (U q).1*(U q).2.2.2; let g(q):=rent a (V q).1*(V q).2.2.2
   have hs:0≤ ∑ i:d,g i:=sum_nonneg fun i _=> mul_nonneg (rent_pos ..).le (hy i).pos; have he:0≤w:=le_trans (le_trans (sum_nonneg (f:=f) fun i _=>mul_nonneg (rent_pos ..).le (hx i).pos) l) hk
   change _≤T*w*v
   calc
     _ ≤ ∑ z:b×d,T*(f z.1*g z.2):= by
       refine sum_le_sum fun z _=> ?_; let X:=U z.1; let Y:=V z.2; let t:=X.2.2.2; let k:=Y.2.2.2; change cost a R _* h^2*(A*(A*r*t)*k)≤ T*_
       have hA:0≤t:=(hx z.1).pos; have hY:0≤k:=(hy z.2).pos; have hu:=u.pos
       have ht:cost a R (S ∪ X.1 ∪ Y.1) ≤ cost a R S*rent a X.1*rent a Y.1:=by
         refine (cost_join hp _ _ _).trans (mul_le_mul ((cost_join hp ..).trans (mul_le_mul_of_nonneg_left (cost_trim hp ..) (rent_pos ..).le)) (cost_trim hp ..) (rent_pos ..).le (mul_nonneg (rent_pos ..).le (rent_pos ..).le))
       apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht (by positivity)) (by positivity)); unfold T f g; change _ ≤ (A^2*_*_*r)*(rent a X.1*t*(rent a Y.1*k)); exact le_of_eq (by ring)
     _ ≤ _:= by rw [←mul_sum, Fintype.sum_prod_type]; simp_rw [← mul_sum,← sum_mul]; rw [mul_assoc T]; exact mul_le_mul_of_nonneg_left (mul_le_mul (l.trans hk) k hs he) hv
 intro z; change f z • (M z*N z)=_; rw [m,W,Finset.sum_mul_sum,Fintype.sum_prod_type,Finset.smul_sum]; refine sum_congr rfl fun x _=>?_ ; rw [Finset.smul_sum]; refine sum_congr rfl fun y _=>?_; simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm, smul_smul]; unfold valK rite; simp [mul_assoc]; rw [mul_comm ((U x).2.2.1 z)]
end Drop
end YM.CF.Acorn
