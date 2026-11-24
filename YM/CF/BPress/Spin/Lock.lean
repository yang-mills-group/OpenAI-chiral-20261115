import YM.CF.BPress.Spin.Basement
import YM.CF.BPress.Spin.Breach
/-! Concrete locks. Leave purchase connected to Pbits in the gauge lattice. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin.Hole
open Function Filter NormedSpace Finset Lattice Fock SU Lat Cube Tenant Branch Tulip Scroll Dial Thera Nacre Laic Paint Eye Pledge Stride Quad Blank Cellar Cellar.Pass Fir
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{c d:ℝ}{S T:Support N}
abbrev pos (S:Support N):= Lock S true
abbrev neg (S:Support N):= Lock S false
def loose (S:Support N): Op (Single N):=1-look (home N) (wings S)
lemma locks (u:Bool)(i:Single N) : (i∈ Locks S u) ↔ i.1.2∈cup u ∧ home N i∈ wings S:= by simp [Locks,tenureX,home,wings, needle.eq_iff]
lemma brake(u:Bool)(i j:Single N): Lock S u i j= if i=j∧ i∈Locks S u then 1 else 0:=by unfold Lock cutM; by_cases h:i=j; simp [h]; simp [h]
lemma coverP (S:Support N): pos S+neg S=look (home N) (wings S):=by ext i j; unfold pos neg; by_cases h:i=j <;> by_cases p: i.1.1∈ S <;> by_cases t:i.1.2∈plusHalf <;> simp only [Matrix.add_apply,brake,locks, cup,Bool.false_eq_true, ↓reduceIte,mem_compl]; all_goals simp_all [look,cutM,wings, home, needle.eq_iff]
lemma plusMinus (S:Support N): Cellar.Empties (pos S) (neg S) (loose S):=by
 refine ⟨cutM_idp _,cutM_idp _, show loose S=1-(pos S+neg S)  from (by rw [loose,coverP]),?_⟩ -- tune
 ext i j; rw [Matrix.mul_apply]; apply sum_eq_zero; intro k _; by_cases h:k=j <;> by_cases t:i=k <;> by_cases w:i.1.2∈plusHalf <;> simp_all [pos,neg,brake,locks,cup]
lemma passed {A:Op (Single N)} (m:IsStarProjection A)(e:0<c)(p:c≤1) (h:Meets c S A): Pass (pos S) (neg S) (loose S) A c:= ⟨plusMinus S,m,e,p,h true,h false⟩
lemma none : (pos (∅:Support N))=0 ∧ neg (∅:Support N)=0 ∧ loose (∅:Support N)=1:=by
 have he(u):Lock (∅:Support N) u=0:=by ext; simp [brake,locks,wings]
 refine ⟨he true,he false,?_⟩; rw [(plusMinus _).l0]; unfold pos neg; simp [he]
lemma meets0(A:Op (Single N))(a:ℝ): Meets a ∅ A:=by
 intro u x; have hx:x=0:=by cases u; exact none.2.1; exact none.1
 rw [hx]; simp
lemma lock_f(u:Bool) (S:Support N): Lock S u=tenureP N u*look (home N) (wings S):=by ext i j; simp only [look_right,brake,locks]; by_cases h:i=j; subst j; all_goals simp only [tenureP, cutM]; all_goals grind [tenureX, Matrix.diagonal_apply]
lemma terra (g:Tenant.Geometry N)(S: Support N): twist (tradew N g) (look (home N) (wings S))=look (home N) (wings S):=by
 have he := strip_tag (bail N 1) g (wings S); rw [twist_formula]
 let V:=tradew N g; change V.val*_*star V.val=_; rw [← show look (home N) (wings S)*V.val= V.val * look (home N) (wings S) from he, mul_assoc,V.property.2,mul_one]
lemma terra_l (u:Bool)(g:Tenant.Geometry N): twist (tradew N g) (Lock S u)=Lock S u:=by
 let W:=tradew N g; let C:=tenureP N u; have he: twist W C=C:=by
    have hx: W.val*C=C*W.val:=by
       ext ⟨⟨x,i⟩,a⟩ ⟨⟨y,j⟩,b⟩; unfold C tenureP cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; unfold W tradew; by_cases h:x=y∧ i=j
       · rcases h with ⟨rfl,rfl⟩; simp only [tenureX,mem_filter,mem_univ,true_and]; split <;> simp
       simp [jump_apply,h]
    rw [twist_formula,hx,mul_assoc,W.property.2,mul_one]
 rw [lock_f,map_mul,terra,he]

-- Every pair commutes with lock per P values regardless of all H.
lemma coupling_lock (H:Paint (More N))(u:Bool): coupling H*Lock S u= Lock S u*coupling H:=by
 rw [show Lock S u=love N (jump (Equiv.refl _) (fun x:Site N=> if x∈ S then angle u ⊗ₖ (1:Op Slot) else 0)) from ?_]; swap
 · ext ⟨⟨x,i⟩,a⟩ ⟨⟨y,j⟩,b⟩; rw [Blank.lid,brake]; change (if _ then _ else _) = jump (Equiv.refl _) (fun x:Site N=> if x∈S then cutM (cup u)⊗ₖ (1:Op Slot) else 0) (x,i,a) (y,j,b); by_cases h:x=y <;> by_cases t:x ∈ S <;> by_cases f:i=j <;> by_cases v:a=b <;> simp_all [jump_apply,Lock,Locks,tenureX,cutM]
 unfold coupling; rw [←map_mul,←map_mul,jump_mul,jump_mul]; apply congrArg; apply congrArg; funext i; unfold nodeC; simp only [Equiv.refl_apply]; split; swap; · simp
 rw [op_kron_mul,op_kron_mul,mul_one,one_mul]; congr 1; cases u; exact neg_anti; exact (by rw [lid]; exact overJ.symm) -- tune u false
where neg_anti : spinJ*angle false=angle false*spinJ:=by rw [lid,show cup false=plusHalfᶜ from rfl,dim_cut,sub_mul,mul_sub,mul_one,one_mul,overJ]
lemma loose_lock (H:Paint (More N)): coupling H * loose S=loose S * coupling H:=by simp only [(plusMinus _).l0,pos,neg,sub_mul,mul_sub,mul_one,one_mul,add_mul, mul_add,coupling_lock]
lemma looks_act (v:Ket (Single N))(i:Single N): (acts (look (home N) (wings S)) v).ofLp i= if i.1.1∈S then v.ofLp i else 0:=by rw [look,cut_apply]; simp [wings,home,needle.eq_iff]

-- priced reads at bits (cast Finset TopologicalSpace instance issue). uses common b for all.
variable {D:Type}[TopologicalSpace D]{G:Form N D}{U:D→ Support N}
def Bits (G:Form N D)(U:D→ Support N): Prop:=∀ S:Seal (Site (More N)),∀ x y:D,∀ i:Site N, node i∈S→ ((i∈ U x ∧ i∉ U y) ∨ (i∈ U y∧ i∉ U x))→1≤G.eval S x y
lemma trackprice (G:Form N D)(h:Bits G U)(p:∀ x:Site N, IsClopen {i:D|x∈U i})(u:Bool): Form.Comes G (stream 1) (fun x=> Lock (U x) u):=by
 let W:= fun x=>Lock (U x) u; have hT(i j:Single N): Continuous (fun x=> W x i j):= by
    have he x: W x i j=if i.1.1∈ U x then (if i=j∧ i.1.2∈cup u then 1 else 0) else 0:=by unfold W; simp only [brake,Locks,tenureX]; grind -- tune
    simp_rw [he]; have h₁:Continuous ({x:D| i.1.1∈ U x}.indicator (fun _=>((if i=j∧i.1.2∈cup u then 1 else 0):ℂ))) := (p _).continuous_indicator continuous_const; convert! h₁ using 1; ext1 x; by_cases t:i.1.1∈U x <;> simp [Set.indicator,t]
 have hm : 1 ≤ max (1:ℝ) 1:= le_max_left ..; refine (row_earn (g:=zero_le_one.trans hm) G.full Form.paid (show 0≤(1:ℝ) by norm_num) (fun i _=> Empty.elim i) (continuous_matrix hT) 0 (fun x i j t=>by unfold W; rw [brake]; exact if_neg (fun g=> ne_of_gt t (by rw [g.1,G.stage.F.reflex]))) (fun i j x=> (norm_entry ..).trans ((IsStarProjection.norm_le (W x) (cutM_idp _)).trans hm)) (fun i j x y=>?_)).books (le_max_right ..)
 let S:=bay G.stage.F (G.stage.home i) 0
 have hk :node i.1.1∈S:=bay_mem _|>.2 (G.stage.F.reflex _|>.le)
 let e:=G.eval S x y; let V:=(max (1:ℝ) 1)*e; have ht:e≤ V:= le_mul_of_one_le_left (G.pos ..) hm
 change ‖W x _ _- W y _ _‖≤V; have hh:S.Nonempty:=⟨_,hk⟩
 unfold W; rw [brake,brake]; split_ifs with f₁ f₂ f₃
 · rw [sub_self,norm_zero]; exact (G.pos ..).trans ht
 · rw [sub_zero,norm_one]; simp only [Locks, tenureX, mem_filter,mem_univ,true_and] at f₁ f₂; apply (h S x y _ hk _).trans ht; tauto
 · rw [zero_sub,norm_neg,norm_one]; simp only [Locks, tenureX, mem_filter,mem_univ,true_and] at f₁ f₃; apply (h S x y _ hk _).trans ht; tauto
 rw [sub_self,norm_zero]; exact (G.pos ..).trans ht
end YM.CF.BPress.Spin.Hole
