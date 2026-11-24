import YM.CF.Moire.Corn
/-! Extensive *nonperturbative* analytically tilted Weyl sea. Projection complexification with gauge for sector extensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Moire
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire Branch Nacre
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m:ℕ}{n:Side}
variable {U W e b a:ℝ}
def Wheel(P:Toy m n)(s: Signed)(X:Chin n):=∑ i:Rota m n,mulC s P i.1 i.2.1 i.2.2 X
def Badge(a:ℝ)(x y:HopK n)(k:Trip m n):=nick a (notx m (x,Classical.ofNonempty) (y,Classical.ofNonempty) k)
def ornament(m:ℕ):ℝ:=8*(1+2*m)+16*((m:ℝ)+1)
lemma ornP(m:ℕ):0<ornament m:=by unfold ornament; positivity
def pen(e:ℝ)(m:ℕ)(U W:ℝ):ℝ:=Real.exp (e*(1+2*m+ornament m))*ruby m U W 1
lemma digH (m:ℕ)(h:0<e)(p:e*ornament m≤ b)(a:Shape)(x y:HopK n)(k:Trip m n)(g:0≤U)(l:0≤W): rent e (Ferry a x y k)*ruby m U W (titanic e (pays x y k))≤ pen e m U W* Badge b x y k:=by
 let A:=notx m (x,Classical.ofNonempty) (y,Classical.ofNonempty) k; have ha: 0≤A:=notx_zero ..; let N:=pays x y k; have hN:N=8*(1+A):=rfl
 have hx:= pays_F a x y k; let B:=ornament m; let H:=Ferry a x y k; have hv: e*↑H.card+(m:ℝ)* (2*e*N)+2*e*N ≤ e*(1+2*m+B)+b*A:=by
   apply le_trans (b:=e*((1+2*m)*(1+N))+(m:ℝ)*(2*e*N)+2*e*N) (by gcongr)
   rw [hN]; unfold B ornament; have he:= mul_le_mul_of_nonneg_right p ha; unfold ornament at he; linarith only [he] -- nonlinear normalize linarith
 have he: Real.exp (e*H.card)* (titanic e N)^m*titanic e N≤ Real.exp (e*(1+2*m+B))* Badge b x y k:=by
   unfold titanic; rw [←Real.exp_nat_mul, ←Real.exp_add,←Real.exp_add]; apply (Real.exp_monotone hv).trans; rw [Real.exp_add]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le (le_add_of_nonneg_right ha)) (Real.exp_pos _).le
 apply le_trans (b:=(Real.exp (e*(1+2*m+B))* Badge b x y k)* ruby m U W 1) _ (le_of_eq (by unfold pen; change _= Real.exp (e*(1+2*m+B))*_ *_; ring)); apply le_trans _ (mul_le_mul_of_nonneg_right he (by unfold ruby; positivity)); apply le_of_eq; change Real.exp (e*H.card)*ruby _ _ _ (titanic e N)=_; unfold ruby; ring

def tinP(a:ℝ)(P:Toy m n)(x y:HopK n):ℝ:=∑ j:Trip m n, Badge a x y j*(∑ b:Slot,netP P x y j b)
def brass(P:Toy m n)(x y:Site n)(e:ℝ):=∑ i:SpinIdx,∑ j:SpinIdx,tinP e P (x,i) (y,j)
lemma tin_P (x:HopK n)(a:ℝ)(P:Toy m n): ∑ y: HopK n,tinP a P x y=∑ i:Slot,balance a P (x,i):=by
 unfold tinP balance netP Single; simp_rw [Fintype.sum_prod_type (α₁:=HopK n),mul_sum]; conv_rhs=> rw [sum_comm]
 refine sum_congr rfl fun y _=>?_ ; rw [sum_comm]; apply sum_congr rfl; intro i h; rw [sum_comm]; rfl
lemma tin_h(a:ℝ)(x y:HopK n)(t:Cover)(P:Toy m n)(H:Prints P): tinP a P (rollH t x) (rollH t y)=tinP a P x y:=by
 unfold tinP; rw [← Equiv.sum_comp (pinch (m:=m) t)]; apply sum_congr rfl; intro i _; rw [show Badge a _ _ _= Badge a x y i by unfold Badge; exact congr_arg (nick a) (notx_t t (x,Classical.ofNonempty) (y,Classical.ofNonempty) i)]; congr 1; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro k _; change ‖P (ramH t (x,j)) (ramH t (y,k)) _‖= _; rw [H,norm_smul,norm_mul]; change ‖Rush.wind _ _‖*‖Rush.wind _ _‖*_= _; unfold Rush.wind; rw [fee_norm,fee_norm,one_mul,one_mul]
def flair :ℝ:= Fintype.card SpinIdx * (↑(Fintype.card Slot):ℝ)
def logos(P:Toy m n)(s:Signed)(e U W:ℝ)(i j:Single n):ℝ:= ∑ p:Rota m n,rent e (Ferry (incX s⁻¹) p.1 p.2.1 p.2.2)*Owes s P p.1 p.2.1 p.2.2 e U W i j
lemma dress_h(a:ℝ)(z:Site n)(P:Toy m n)(p:Prints P): ∑ i:Site n,brass P i z a=∑ i:Site n,brass P z i a:=by
 let V:= (Equiv.neg (Site n)).trans (Equiv.addRight (2 • z))
 conv_rhs=> rw [← Equiv.sum_comp V]
 apply sum_congr rfl; intro i _; apply sum_congr rfl; intro u _; apply sum_congr rfl; intro v _; let t:=natural (z-i); have ht:wrap _ t=z-i:=nat_true _; have hv:V i=z+(z-i):=by unfold V; simp [two_smul]; abel
 simpa only [rollH,ht,hv, add_sub_cancel] using (tin_h a (i,u) (z,v) t P p).symm -- orientation row z spin same
lemma coin(P:Toy m n)(v:∀ i,balance a P i≤ b)(x:Site n): ∑ i:Site n,brass P x i a ≤ flair * b:=by
 unfold brass; rw [sum_comm]; simp_rw [← Fintype.sum_prod_type' (α₁:=Site n) (α₂:=SpinIdx)]; apply (sum_le_sum (g:=fun _=>∑ _ : Slot,b) ?_).trans; swap
 · intro i _; change (∑ j:HopK n,tinP a P (x,i) j)≤_; rw [tin_P]; exact sum_le_sum fun j _=> v _
 simp [flair]; ring_nf; rfl -- tune
lemma Logos(P:Toy m n)(s:Signed)(i j: Single n)(h:0<e)(p:e*ornament m≤ a)(g:0≤U)(l:0≤W): logos P s e U W i j≤ (↑(Fintype.card Slot):ℝ)*pen e m U W * brass P ((Tofu (incX s) n) i.1.1) ((Tofu (incX s) n) j.1.1) a :=by
 let x:=(Tofu (incX s) n) i.1.1; let y:= (Tofu (incX s) n) j.1.1
 unfold logos Rota HopK; simp_rw [Fintype.sum_prod_type (α₁:=Site n × SpinIdx),Fintype.sum_prod_type (α₁:=Site n)]; simp only [Owes,ite_and, mul_ite,mul_zero,sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true]
 unfold brass tinP; simp_rw [mul_sum]; -- tune retaining net sum? expands everything
 apply sum_le_sum; intro u _; apply sum_le_sum; intro v _; apply sum_le_sum; intro w _; apply sum_le_sum; intro k _; let R:=Ferry (incX s⁻¹) (x,u) (y,v) w; let Q:=netP P (x,u) (y,v) w k; let N:=(↑(Fintype.card Slot):ℝ); let Y:=ruby m U W (titanic e (pays (x,u) (y,v) w)); change rent e R * (N*Y * Q)≤N * pen e m U W * (Badge a (x,u) (y,v) w * Q); calc
   _ = (N*Q)*(rent e R*Y):=by ring
   _ ≤ (N*Q)*(pen e m U W * Badge a (x,u) (y,v) w):=mul_le_mul_of_nonneg_left (digH m h p _ _ _ _ g l) (by unfold N Q netP; positivity)
   _ = _:=by ring
end YM.CF.Moire
