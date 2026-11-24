import YM.CF.Rel.View
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
def Prox (F:FileM n G) (l:ℕ)(A:ℝ):Prop:=∀ j:Fin l→ Body 1 n,∀ s:SpotG G l, ‖∑ i,cake l (satX (F i)) (fun y=>flaw G (j y) (s y))‖ ≤ A
lemma scatter {F: SpaceX G n}{i:Site n}(j:Fin m→Body 1 n)(s:SpotG G m)(h:Atom F i r)(he:ContDiffAt ℝ m (satX F) 0)(k:Fin m)(hl:r < separation i (j k).1): cake m (satX F) (fun y=> flaw G (j y) (s y))=0:=by
 let v:= (Trot n).symm ∘ j; have hi: timeA (cake m (satX F)) v=0:=by
    apply spelt h he k; exact hl
 have hm : cake m (satX F) (fun y=> flaw G (j y) (s y))=timeA (cake m (satX F)) v (fun y=>jewelG G (s y)):=by
    congr 0; apply congr_arg (fun a=> cake m (satX F) a); funext u; change _= Pi.single (M:=fun _=> G.Color) (Trot n ((Trot n).symm (j u))) _; rw [Equiv.apply_symm_apply]; rfl
 rw [hm,hi]; rfl
-- cost absolute sum for V pulses
lemma scan_F {F: FileM n G} (h:∀ i:Site n, Atom (F i) i r)(he:∀ i,ContDiffAt ℝ (↑(m+1:ℕ):WithTop ℕ∞) (satX (F i)) 0)(e:Prox F (m+1) A) (hp:0 ≤ A)(k:Site n)(hS:shapeV k F)(v:Axis→ℝ)(pv:Push.Loops.Matches (axes v) k) (W:KitM G n (m+1))(hc:∀ V,cake (m+1) (satX (F 0)) V=∑ p,engages W p V)(a:Run (m+1))(b:SpotG G (m+1))(u:DialT n m):
 ‖clipP (breathL W k b) v a (tollX u)‖ ≤ ↑((plot (2*r))^m)*A:=by
 let V:=clipP (breathL W k b) v a (tollX u); let Z(x:DialT n (m+1)):=∑ X,cake (m+1) (satX (F X)) (fun i=> flaw G (x i,a i) (b i)); let Y:= plot (2*r)^m; let T (x:DialT n (m+1)):=cMul (listH u k) x * Z x
 have hh(i:Site n):(∑ j:DialT n m,‖T (Fin.cons i j)‖) ≤ (Y:ℝ)*A:=by
    let P:= scope n (pavilion (2*r) i) m; have ht: P.card ≤ Y:=by unfold Y P; rw [careC]; exact pow_le_pow_left₀ (Nat.zero_le _) (pay_v i) _
    rw [← sum_subset (subset_univ P) (show ∀ j∈univ,j∉P→ ‖T (Fin.cons i j)‖=0 from ?_)]
    · apply (sum_le_sum (g:=fun _=> A) (fun j _=>?_)).trans (by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) hp); unfold T; rw [norm_mul,cUnit,one_mul]; exact e _ _
    intro j _ hj; unfold T; suffices hZ: Z (Fin.cons i j)=0 by rw [hZ,mul_zero,norm_zero]
    simp only [P,scope,Fintype.mem_piFinset,theatre,not_forall,not_le] at hj; obtain ⟨k,hk⟩:=hj; apply sum_eq_zero; intro X _
    let P(u:Fin (m+1)):Body 1 n:= ((Fin.cons i j:DialT n (m+1)) u,a u); by_cases hh:r < separation X i; · exact scatter P _ (h X) (he X) 0 hh
    apply scatter P _ (h X) (he X) k.succ; change r< separation X ((Fin.cons i j: DialT n (m+1)) k.succ); rw [Fin.cons_succ]; have H:= separation_triangle i X (j k); rw [separation_comm i X] at H; omega
 let N:ℂ:= Fintype.card (Site n); have hz : N*V=∑ x,T x:=by
    unfold T Z; simp_rw [mul_sum]; rw [sum_comm]; simp_rw [asks k hS (he 0) W hc v u pv _ a b]; simp [N,V]
 let D:= Fin.consEquiv (fun _ : Fin (m+1)=>Site n); have ht:0<‖N‖:=norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero))
 apply le_of_mul_le_mul_left _ ht; change ‖N‖*‖V‖ ≤ _; rw [← norm_mul,hz]; apply (norm_sum_le ..).trans; change ∑ i, ‖T i‖≤ _; rw [←D.sum_comp (fun i=>‖T i‖),Fintype.sum_prod_type]; apply (sum_le_sum (g:=fun _=> (Y:ℝ)*A) (fun i _=> hh i)).trans; simp [N,Y]
end YM.CF.Rel
