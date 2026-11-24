import YM.CF.BPress.Spin.Invest
import YM.CF.Pic.Sig
/- Pair field on all gauge sites, used just at nodes by pairing. Keep whole 45 colors. D=ℂ with skew parity. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter Finset NormedSpace Lattice Fock Cube Tenant SU SU.Pair Branch Lat Tulip Scroll Dial SpinSign Pledge
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker BigOperators
attribute [local instance] opCStarAlgebra
abbrev Paint (s:Side):= Site s→ Op Slot
structure Sym (A: Op Slot) : Prop where
 triangle : Aᵀ=A
 gate : A∈unitary (Op Slot)
 traceX : A.det=1
variable {s N:Side} (U: Paint (More N))
lemma Sym.full (x:Vect)(h:‖x‖=1) : Sym (fullM x) := ⟨(full_laws x h).1,(full_laws x h).2.2,(full_laws x h).2.1⟩
namespace Paint
def nodeC(A:Op Slot): Op (SpinIdx×Slot):= spinJ ⊗ₖ A
def coupling (U:Paint (More N)):= love N (jump (Equiv.refl _) (fun x=> nodeC (U (node x))))
lemma fromX (X:Stun N): coupling (fun x=>fullM (hook X x))=postC X:=rfl
lemma atX (U:Paint (More N)) (i j:Single N): coupling U i j=if i.1.1=j.1.1 then nodeC (U (home N i)) (i.1.2,i.2) (j.1.2,j.2) else 0:=rfl
lemma node_skew (A:Op Slot)(p:Aᵀ=A): (nodeC A)ᵀ= -nodeC A:=by
 unfold nodeC; rw [← Matrix.kroneckerMap_transpose, p, show spinJᵀ= -spinJ from (by have h:= spinJ_real; unfold cc at h; rw [←h, Matrix.transpose_transpose,h,spinJ_star]),op_kron_neg]
lemma node_unit (A:Op Slot)(h:A∈unitary (Op Slot)): nodeC A ∈unitary (Op (SpinIdx×Slot)):= Matrix.kronecker_mem_unitary spinJ_unitary h
lemma node_low (A:Op Slot) : ‖nodeC A‖≤ ‖A‖:=by
 rw [show nodeC A= nodeC 1 * ((1:Op SpinIdx) ⊗ₖ A) by unfold nodeC; rw [op_kron_mul,mul_one,one_mul]]
 apply (norm_mul_le ..).trans; rw [CStarRing.norm_of_mem_unitary (node_unit 1 (unitary _).one_mem),one_mul]; exact replicas_bound ..
lemma node_move(x y:Op Slot): ‖nodeC x-nodeC y‖≤ ‖x-y‖:=by rw [show nodeC x-nodeC y=nodeC (x-y) from (op_kron_sub ..).symm]; exact node_low _
def MatPlan (U : Paint s): Prop:= ∀ x, Sym (U x)
def MatLite (U :Paint s)(a:ℝ): Prop:=∀ x, ‖U x‖ ≤ a
variable {U} {a:ℝ}
lemma MatPlan.one (S:MatPlan U) : MatLite U 1:= fun x=> (CStarRing.norm_of_mem_unitary (S x).gate).le -- repeat More s later
lemma unit (U:Paint (More N))(S:MatPlan U): coupling U ∈ unitary (Op (Single N)):=attached _ fun x=> ⟨_, node_unit _ (S (node x)).gate⟩
lemma skew (U:Paint (More N))(S:MatPlan U): (coupling U)ᵀ= -coupling U:=by
 ext ⟨⟨x,i⟩,u⟩ ⟨⟨y,j⟩,v⟩; by_cases h:x=y
 · subst y; simp only [Matrix.transpose_apply, atX, ↓reduceIte,Matrix.neg_apply]; exact Matrix.ext_iff.mpr (node_skew _ (S (node x)).triangle) (i,u) (j,v) -- nondec equality tune
 simp [Matrix.transpose_apply, atX,h,Ne.symm h]
lemma coupe_norm (h:MatLite U a)(p:0≤a): ‖coupling U‖≤a:=by rw [coupling,love_money]; exact jump_bound _ _ p fun x=> (node_low ..).trans (h _)
lemma coupe_sub (U V: Paint (More N)): coupling (U-V)=coupling U-coupling V:=by
 unfold coupling; rw [←map_sub, ←jump_sub]; congr 2; ext1 x; exact op_kron_sub ..
-- free constant anti-intertwiner for ANY pair color
lemma coupling_const (A:Op Slot) : coupling (N:=N) (fun _=>A)=jump (Equiv.refl (Site N)) (fun _=>spinJ) ⊗ₖ A:=by
 ext ⟨⟨x,i⟩,u⟩ ⟨⟨y,j⟩,v⟩; by_cases h:x=y <;> simp [atX,h,nodeC,jump_apply]
theorem free_anti (j:ℕ)(h:1≤j)(M:Jill.Male)(K: Op Slot) : let P:=spar j M (1:Bkg (More N)); let B:= coupling (N:=N) (fun _=>K); P*B=B*cc P:=by
 intro P B; let H:=fullM apex.val; let E:=Pic.poleC N; have hx:E=coupling (N:=N) (fun _=>H):=rfl; have hp:P*E=E*cc P:=Pic.spoke j h M N; let A:Op (Single N):=(1:Op (Site N × SpinIdx))⊗ₖ (star H*K)
 have ht:B=E*A:=by rw [hx,coupling_const]; unfold B A; rw [coupling_const,op_kron_mul,← mul_assoc H,H_mem',one_mul,mul_one] -- tune
 have hy : cc P*A=A*cc P:=by unfold P spar; rw [profile_trivial, funde_flat _ h,op_cc_kron, cc_one]; unfold A; rw [op_kron_mul,op_kron_mul,one_mul,mul_one,mul_one,one_mul]
 rw [ht, ←mul_assoc,hp,mul_assoc E, hy,mul_assoc]
where H_mem' : (fullM apex.val)*star (fullM apex.val)=1:= (full_laws _ (hookN (vacuumW (2:Side)) 0)).2.2.2 -- tune name

variable {x y: E} {P:Op Slot}
abbrev swivelC (x:E) (A:Op Slot):= congrC (matter x) A
def rotateC (g: Site s→ E)(U:Paint s) :Paint s:= fun x=> swivelC (g x) (U x)
lemma turn_add (k l:E)(A:Op Slot) : swivelC (k*l) A=swivelC k (swivelC l A):=by simp only [swivelC,map_mul,show ∀ x y:UNI Slot, (x*y).val=x.val*y.val from fun _ _=> rfl,congrC, Matrix.transpose_mul,mul_assoc] -- tune
lemma turn_one (A:Op Slot): swivelC 1 A=A:=by simp only [swivelC, map_one, congrC]; simp
lemma turn_plan (H:Sym P)(x:E): Sym (swivelC x P):=by
 let V:=matter x; constructor
 · change (congrC V P)ᵀ= _; rw [congrC,Matrix.transpose_mul, Matrix.transpose_mul,Matrix.transpose_transpose,H.triangle]; rw [←mul_assoc]; rfl
 · exact (unitary _).mul_mem ((unitary _).mul_mem V.property H.gate) (Matrix.transpose_mem_unitaryGroup_iff.mpr V.property)
 change (V.val*P * V.valᵀ).det=1; rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose, H.traceX,triple_det',mul_one,mul_one]
where triple_det' : (matter x).val.det=1:=triple_det x
lemma iso (x:E) (A B:Op Slot): ‖swivelC x A-swivelC x B‖=‖A-B‖:=by rw [show _-swivelC x B=congrC (matter x) (A-B) by simp [swivelC,congrC,mul_sub,sub_mul]]; exact congr_norm ..
lemma spoke (g: Tenant.Geometry N): (tradew N g).val=love N (jump (Equiv.refl _) (fun x:Site N=> (1:Op SpinIdx)⊗ₖ (matter (g (node x))).val)):=by
 ext ⟨⟨x,i⟩,k⟩ ⟨⟨y,j⟩,l⟩; change jump (Equiv.refl (Site N × SpinIdx)) (fun i=> (matter (g (node i.1))).val) ((x,i),k) ((y,j),l)= jump (Equiv.refl _) (fun x:Site N=> (1:Op SpinIdx)⊗ₖ (matter (g (node x))).val) (x,i,k) (y,j,l); by_cases h:x=y <;> by_cases g': i=j <;> simp [h,g',jump_apply]
lemma coupe_gauge (U:Paint (More N))(g:Tenant.Geometry N): coupling (rotateC g U)=congrC (tradew N g) (coupling U):=by
 let V(x:Site N):Op (SpinIdx×Slot):=(1:Op SpinIdx) ⊗ₖ (matter (g (node x))).val; let W:=jump (Equiv.refl _) V; rw [congrC,spoke, coupling,coupling,show (love N W)ᵀ=love N (jump (Equiv.refl _) (fun x: Site N=>(V x)ᵀ)) from ?_, ←map_mul, ←map_mul,jump_mul,jump_mul]; swap
 · ext ⟨⟨x,i⟩,k⟩ ⟨⟨y,j⟩,l⟩; change W (y,j,l) (x,i,k)=jump (Equiv.refl _) (fun x: Site N=>(V x)ᵀ) (x,i,k) (y,j,l); by_cases h:x=y <;> simp [W,h,eq_comm (a:=y) (b:=x),jump_apply]
 congr 2; ext1 x; change nodeC _= V x * nodeC _*(V x)ᵀ; unfold V nodeC; rw [←Matrix.kroneckerMap_transpose,Matrix.transpose_one,op_kron_mul,op_kron_mul,one_mul,mul_one]; rfl
lemma coupling_cont: Continuous (coupling (N:=N)):= continuous_matrix fun i j=> by
 simp_rw [atX]; split; swap; · exact continuous_const
 simp only [nodeC, Matrix.kroneckerMap_apply]; apply continuous_const.mul; exact (continuous_apply (home N i)).matrix_elem ..

def stream (C:ℝ): Pledge:= ⟨1,(max 1 (quota*(((0:ℕ):ℝ)+1)^4*Real.exp (1*(quota*(((0:ℕ):ℝ)+1)^4))* max C 1)), one_pos,lt_max_of_lt_left one_pos⟩
lemma stream_cost {D: Type}[TopologicalSpace D] (g:Form N D){C:ℝ}(U:D→ Paint (More N))(u:∀ x, MatLite (U x) C)(h:Continuous U)(v:∀ (X:Support (More N)) (x y:D) i, i∈X→ ‖U x i-U y i‖≤g.eval X x y) : Form.Comes g (stream C) (fun x=> coupling (U x)):=by
 let K:=max C 1; have ht:1≤K:=le_max_right ..; have hk:0≤K:=zero_le_one.trans ht
 refine (row_earn g.full Form.paid (show 0≤(1:ℝ) by norm_num) (fun i _=>Empty.elim i) (coupling_cont.comp h) hk 0 ?_ ?_ ?_).books (le_max_right ..)
 · exact fun x i j p=> by rw [comp_apply,atX]; exact if_neg fun s=>ne_of_gt p ((congrArg (g.stage.F.span (g.stage.home i)) ((congrArg node s).symm : g.stage.home j=g.stage.home i)).trans (separation_self _)) -- tune
 · exact fun i j x=> (norm_entry ..).trans (coupe_norm (fun b=> (u x b).trans (le_max_left ..)) hk)
 intro i j x y; let S:=bay (terr (More N)) (home N i) 0; rw [comp_apply,comp_apply,atX,atX]; split; swap; · rw [sub_self,norm_zero]; exact mul_nonneg hk (g.pos ..)
 refine (norm_entry (nodeC (U x (home N i))-nodeC (U y (home N i))) (i.1.2,i.2) _).trans ((node_move ..).trans ((v S x y _ ((bay_mem _).2 ((terr (More N)).reflex _ |>.le))).trans (le_mul_of_one_le_left (g.pos ..) ht)))
end Paint
end YM.CF.BPress.Spin
