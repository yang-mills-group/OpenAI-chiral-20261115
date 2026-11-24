import YM.CF.Font.Bow
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Font
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {c f:Side}(G:Ratio c f)
lemma visitsH(P:Op (Iota G)):arch G (P*hood G)= arch G P:=by
 ext i j; unfold arch; rw [lighthouse]; simp only [Matrix.of_apply,Fock.cutM, Matrix.mul_diagonal]; rw [if_pos, mul_one]; simp [lows]
omit G
set_option maxHeartbeats 650000 in
lemma bluff(j:ℕ)(h:Even j)(p:2≤j)(u: Bool):∃ σ D:ℝ,0<σ∧0<D ∧∀ {c f:Side}(G:Ratio c f)(w:Odd G.count.val)(T:Script Male)(e:Use j G.count @T)(M: Male), BudH G (arch G (pine j G.count w @T u M G 1)) σ D:=by
 let I:=Σ x:Male×Male,Site x.1.val
 obtain ⟨b,C,x,y,H⟩:= pricelet u j (fun i:I=>i.1.1.val) (fun i=>i.1.2.val) (fun i=>i.1.1.property) (fun i=>i.1.2.property) (fun i=> i.2) [] p
 let t:=Real.exp (2*b); let K:=↑(Fintype.card SpinIdx)*(↑(Fintype.card Slot)*t*C)
 refine ⟨b/2,K,by positivity,by unfold K t; positivity,fun {c f} G w T e M=>?_⟩
 let W:= coverlet u j G.count M.val []; let V:=tub W
 let P:= pine j G.count w @T u M G 1; let Q:= cart c V; let Y:= arch G P
 have hz:P*hood G= Q⊗ₖ 1:=by have hh:= pine_stencil j G.count w h (by omega) T e G rfl M u [] p; simp only [sentry,List.map_nil,List.prod_nil,Matrix.one_kronecker_one,one_mul] at hh; exact hh
 have hg(m n:Site c)(i k:SpinIdx)(r:Site G.count)(a b:Slot): Y (switchG G ((m,(r,i)),a)) ((n,k),b)= Q (m,r,i) (n,0,k)*(1:Op Slot) a b:=by unfold Y; rw [←visitsH,hz]; unfold arch; simp only [Matrix.of_apply,Equiv.symm_apply_apply]; rfl
 have he(m n:Site c)(i k:SpinIdx)(r:Site G.count)(a d:Slot): bolt (b/2) G (switchG G ((m,(r,i)),a)) ((n,k),d)*‖Y (switchG G ((m,(r,i)),a)) ((n,k),d)‖ ≤ t* (Faro b m n* ‖Q (m,r,i) (n,0,k)‖):=by
   rw [← mul_assoc t,hg]; refine mul_le_mul ?_ ?_ (norm_nonneg _) (by unfold t Faro; positivity); rotate_left
   · rw [norm_mul,Matrix.one_apply]; split <;> simp
   unfold t Faro bolt; rw [← Real.exp_add]; apply Real.exp_monotone; have hp:(dish G (switchG G ((m,(r,i)),a)) ((n,k),d):ℝ)≤ 2*(separation m n)+4:=by exact_mod_cast dish_le G w m n i k a d r -- tune
   linarith [mul_le_mul_of_nonneg_left hp x.le]
 let L:= followV [] G.count
 have hh(a i k):Width b (C*L) fun x=> V x (a,i) (0,k):= H (⟨(⟨_,w⟩,M),a⟩:I) i k
 constructor
 · intro z; change ∑ i:Single c, bolt _ _ z i*‖Y z i‖ ≤ _
   obtain ⟨⟨⟨m,r,i⟩,a⟩,rfl⟩:= (switchG G).surjective z; let z:=switchG G ((m,(r,i)),a); let W(k d):=∑ n:Site c,bolt (b/2) G z ((n,k),d)* ‖Y z ((n,k),d)‖
   have hv(k d):W k d ≤ t*(C*L):=by apply (sum_le_sum fun n _=> he m n i k r a d).trans; rw [← mul_sum]; apply mul_le_mul_of_nonneg_left (plate_e x (hh r i k) m); positivity -- tune
   have hx: ∑ j:Single c,bolt (b/2) G z j *‖Y z j‖= ∑ k,∑ d,W k d:=by unfold Single W; rw [Fintype.sum_prod_type, Fintype.sum_prod_type]; rw [sum_comm]; refine sum_congr rfl ?_; intro k _; rw [sum_comm]
   change ∑ j:Single c,bolt (b/2) G z j *‖Y z j‖ ≤ _; rw [hx]; apply le_trans (sum_le_sum fun k _=> sum_le_sum fun d _=> hv k d); unfold K; simp only [sum_const,card_univ,nsmul_eq_mul]; unfold L; apply le_of_eq; ring -- tune
 intro z; obtain ⟨⟨n,k⟩,d⟩:=z; let z:Single c:= ((n,k),d); let A(i: Iota G):= bolt (b/2) G (switchG G i) z * ‖Y (switchG G i) z‖; rw [←Equiv.sum_comp (switchG G)]; let f(r i a):= ∑ m:Site c,A ((m,(r,i)),a)
 have hv(r i a): f r i a ≤ t*(C*L):=by
    apply (sum_le_sum fun m _=> he m n i k r a d).trans; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (plate_f (furl j u [] p G w M) x (hh r i k) _) (Real.exp_pos _|>.le)
 change (∑ i,A i)≤ _; have hs:(∑ i,A i)=∑ a,∑ r,∑ i,f r i a:=by
    unfold f Iota; rw [Fintype.sum_prod_type, sum_comm]; refine sum_congr rfl ?_; intro a _; rw [Fintype.sum_prod_type, sum_comm]; unfold St; rw [Fintype.sum_prod_type]
 rw [hs]; apply le_trans (sum_le_sum fun a _=> sum_le_sum fun r _=>sum_le_sum fun i _=> hv r i a); unfold K L; simp only [sum_const,card_univ,nsmul_eq_mul,site_card,Nat.cast_pow]; apply le_of_eq; ring -- tune
end YM.CF.Font
