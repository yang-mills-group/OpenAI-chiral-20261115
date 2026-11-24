import YM.CF.Pec.Minny
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n N:Side}{a b c:ℝ}
-- per y anchored on links in same torus (More N). use phi cross
def ripe (K:Ok N→ Ok n→ℝ)(x:Orig N)(V:Dues N):Dues n := ∑ i:Ok N,∑ j:Ok N,fun p q=> roseK K x i j p q • V i j
private lemma inner_w (x:Orig N)(y:Orig n)(X:Ok N→ Ok n→ℝ)(F:Dues N)(U:Cloud n)(V:Cloud N)(h:∀ i,heat x (collect group V) i=∑ z,X i z • heat y (collect group U) z) (p:∀ i j,mom F i j=0): datam x F V=datam y (ripe X x F) U:=by
 unfold datam; simp_rw [h]; let W(t):=heat y (collect group U) t; let T i j u v:= X i u*X j v; let R(i j u v) :ℂ:= (inner ℝ (W u) (W v)) • T i j u v • F i j
 have he : ∀ u v: Ok n, ∑ i:Ok N,∑ j:Ok N,T i j u v • F i j = ∑ i:Ok N, ∑ j:Ok N,roseK X x i j u v • F i j:=by
    intro u v; unfold Ok PrizeX Wind; simp_rw [Fintype.sum_sum_type, sum_add_distrib]; refine congrArg₂ _ ?_ rfl; refine congrArg₂ _ ?_ rfl; unfold Face; simp_rw [Fintype.sum_prod_type]; unfold roseK T; simp_rw [sub_smul, Finset.sum_sub_distrib]; -- all orders
    simp only [eq_sub_iff_add_eq,add_eq_left]; let L(t k:PlaqAxes):= X (Sum.inl (x,t)) u* X (Sum.inl (x,k)) v; change (∑ i:Orig N,∑ t:PlaqAxes, ∑ j:Orig N, ∑ k:PlaqAxes, (L t k) • F (Sum.inl (i,t)) (Sum.inl (j,k)))=0
    rw [sum_comm]; apply sum_eq_zero; intro i _; -- reorder
    rw [show ∀(f:Orig N→Orig N→PlaqAxes→ℂ), (∑ i:Orig N, ∑ j:Orig N, ∑ k:PlaqAxes,f i j k)=∑ k:PlaqAxes, ∑ i:Orig N,∑ j:Orig N,f i j k from fun f=>by rw [sum_comm (s:=(univ:Finset PlaqAxes))]; apply sum_congr rfl; intro; intro; rw [sum_comm]]; apply sum_eq_zero; intro k _; simp_rw [← Finset.smul_sum]; rw [show ∑ i':Orig N, ∑ j:Orig N,_=_ from p i k, smul_zero]
 have hv(i j :Ok N): inner ℝ (∑ z:Ok n,X i z • heat y (collect group U) z) (∑ z:Ok n,X j z • heat y (collect group U) z) • F i j=∑ u:Ok n,∑ v:Ok n,R i j u v:=by
    rw [sum_inner]; simp_rw [Finset.sum_smul,inner_sum,Finset.sum_smul]; refine sum_congr rfl fun k _=>sum_congr rfl fun l _=> ?_; unfold R T W; rw [real_inner_smul_left,real_inner_smul_right,smul_smul]; congr 1; ring
 simp_rw [hv]; unfold ripe; simp only [Finset.sum_apply]; simp_rw [←he,Finset.smul_sum]; change (∑ i:Ok N,∑ j:Ok N, ∑ u:Ok n, ∑ v:Ok n,R i j u v)=∑ i:Ok n,∑ j:Ok n,∑ u:Ok N,∑ v:Ok N,R u v i j
 -- Fintype.sum_prod
 have hp {A B C D:Type}[Fintype A][Fintype B][Fintype C][Fintype D](g:A→ B→C→D→ℂ): (∑ i:A,∑ j:B,∑ k:C,∑ l:D,g i j k l)=∑ k:C, ∑ l:D,∑ i:A,∑ j:B,g i j k l:=by
    simp_rw [← Fintype.sum_prod_type' (α₁:=A) (α₂:=B),← Fintype.sum_prod_type' (α₁:=C) (α₂:=D)]
    rw [Finset.sum_comm]
 exact hp R
lemma riseK (K:Ok N→ Ok n→ℝ)(x:Orig N)(y:Orig n)(V:Dues N)(g:∀ i j,tither a y (roseK K x i j) ≤ nick a (contour x i j)*b) :cents y (ripe K x V) a ≤ cents x V a * b:=by
 have hp{ι:Type}[Fintype ι](T:ι→Dues n): cents y (∑ i,T i) a≤ ∑ i,cents y (T i) a:=by
    classical
    suffices hh:∀ s:Finset ι,cents y (∑ i∈s,T i) a≤∑ i∈s,cents y (T i) a from hh univ
    intro s; induction s using Finset.induction_on with | empty=>simp [cents]| @insert i s h ih=>simp only [sum_insert h];apply (coverG ..).trans; gcongr
 let A(i j: Ok N)(p q: Ok n):= roseK K x i j p q • V i j; apply le_trans (hp (fun i : Ok N=> ∑ j:Ok N,A i j)); unfold cents; simp_rw [Finset.sum_mul]; refine sum_le_sum fun i _=> ?_; refine (hp (A i)).trans (sum_le_sum fun j _=>?_ ); unfold cents; simp_rw [A,norm_smul, ←mul_assoc,← sum_mul]; exact (mul_le_mul_of_nonneg_right (g i j) (norm_nonneg _)).trans_eq (mul_right_comm ..)
lemma lin_pole{ι:Type}[Fintype ι](K:ι→ Dues n)(x:Orig n)(y:Cloud n): datam x (∑ i,K i) y=∑ i,datam x (K i) y:=by unfold datam; simp_rw [Finset.sum_apply,Finset.smul_sum]; rw [sum_comm (s:=(univ:Finset ι))]; refine sum_congr rfl fun i _=>?_ ; rw [sum_comm]
lemma edge_t (G:Ratio n N)(t:Site G.count)(x:Site n)(p:Odd G.count.val): separation (node x) ((ratio G).parent (node (isle G (x,t))))≤ 4:=by
 let g:=ratio G; rw [embed_node G p]; let V:= (2:ℕ) • Lattice.lift t; let A:=node x; let X:= g.embed A
 have he: separation X (X+wrap _ V)≤ 2*G.count.val:=by
   rw [separation_comm,separation,add_sub_cancel_left]; apply Work.E01.pdist_wrap_le; rw [box_test]; have h(j): - (↑(2*G.count.val):ℤ) ≤ V j∧ V j≤ (↑(2*G.count.val):ℤ):=by have hh:= lift_centers t j; unfold V; simp; omega -- parentheses
   exact ⟨fun j=>(h j).1,fun j=>(h j).2⟩
 have ht:= Corona.foreshorten g X (X+wrap _ V); rw [show g.parent X=A from Ratio.embed_parent ..] at ht; have hx:g.count=G.count:=rfl; change separation A (g.parent (X+wrap _ V))≤ 4; have hz:=G.count.property; apply Nat.le_of_mul_le_mul_left _ g.count.property; apply ht.trans; rw [hx]; refine le_trans (Nat.add_le_add_right he G.count.val) ?_; change 2*G.count.val+G.count.val ≤ G.count.val*4; omega
lemma stigma (p:0<a)(h:0<b) (C:ℝ)(hv:0≤C):∃ K:ℝ,0<K ∧∀ (L:Side)(w:Odd L.val),4≤L.val→∀ d:ℝ, 0<d→d≤a/2→∃ N:ℕ,∀ {f n:Side}{G:Ratio n f}{T:RG.StepData (More n) (More f)}{F: Forest T.ratio}{z:Cloud n→AxisChart group F}, G.count=L→ T.ratio=ratio G→ Nativity F z→ Gazes T F z a C b→N≤(More n).val→∀ (H:Pride f),WordK H→merit H→∀ v, (∀ x,cents (node x) (H x) d≤v)→∃ h:Pride n,WordK h ∧ Nacre.crystal 2 (pigment H ∘baby F z) (diem h) ∧∀ x,cents (node x) (h x) d≤ v*K/Real.sqrt L.val :=by
 obtain ⟨V,hV,D⟩:= children b a C 4 h p (by norm_num) hv; refine ⟨_,hV,fun L w e c s y=>?_⟩
 obtain ⟨N,Y⟩:=D L e c s y; refine ⟨N,?_⟩; intro f n G T F z t v hp hu hx H he hq d hh
 obtain ⟨Λ,A,X⟩:=hu.was; have ht:Rails (ratio G) b a Λ:=by rw [←v]; exact A
 let h:=ratio G; have hy:Odd G.count.val:=t.symm ▸ w
 let a(i: Site n)(j:Site G.count):= isle G (i,j)
 choose P K E using (fun i:Site n=>fun j:Site G.count=>X (node (a i j)) (node i)); let W(i:Site n)(j:Site G.count):= ripe (P i j) (node (a i j)) (H (a i j)); let J:Pride n:=fun i=>∑ j,W i j; let T':=fderiv ℝ (Iteration.chartOf F z) 0; have hg(x:Cloud n): letter J x=letter H (T' x):=by
   unfold letter; conv_rhs=> rw [← Equiv.sum_comp (isle G), Fintype.sum_prod_type]
   refine sum_congr rfl fun i _=> ?_; unfold J; rw [lin_pole]; apply sum_congr rfl; intro j _; exact (inner_w _ _ _ _ _ _ (E i j x) (hq (a i j))).symm
 have hz:= cook (tourists hp H) (tip_p v hp he) (funext hg)
 refine ⟨stageM J,repose _,tour_s v hp _ hz,fun x=> W_h_cost ?_ x⟩
 intro x
 let k:= V/(Real.sqrt (L.val:ℝ)*(L.val:ℝ)^4); have hl:0<(L.val:ℝ):=Nat.cast_pos.mpr L.property; have hK:0<k:=by unfold k; positivity
 have hw(j:Site G.count): cents (node x) (W x j) c ≤ d*k:=by
    have he:= edge_t G j x (show Odd G.count.val from hy)
    refine (riseK _ _ _ _ (Y _ (show (ratio G).count=L from t) hx Λ _ ht (K x j) (node (a x j)) (node x) (by exact_mod_cast he))).trans (mul_le_mul_of_nonneg_right (hh _) hK.le)
 apply (bookZ _ _ hw).trans_eq; rw [site_card,t,Nat.cast_pow]; unfold k; field_simp
end YM.CF.Pec
