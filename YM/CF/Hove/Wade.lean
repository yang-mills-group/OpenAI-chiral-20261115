import YM.CF.Hove.Prune
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable (j m:ℕ)(e:Even j)(p:4≤j)(v:2 ≤ m)
variable{c f:Side}(o:Site c)(G:Ratio c f)(w:Odd G.count.val)(M:Male)(b:Bool)(T:Script Male)(u:Use j G.count T)
local notation "Sφ"=> (heel G o)
local notation "W"=> nook_T o m
include e p
lemma αp : ∃ C:ℝ,0 ≤ C∧∀{c f:Side}(o:Site c)(G:Ratio c f)(w:Odd G.count.val)(T:Script Male),Use j G.count @T →∀ M:Male,∀ (x:List Axis), x.length ≤2→∀ i:Kt, paidX (nook_T o m) (fun y:Single c=>wingF j G w T M b (heel G o) x i y)≤ C*lace x.length G.count:=by
 obtain ⟨A,h,H⟩:=Tap.lumpK j m e p b; refine ⟨A,h.le,fun {c f} o G w T u M x q i=>?_⟩
 let z:= stickW (heel G o) i; have ht:= H G w T u M z 0 x q; rw [show Laurent.size (0:Cover)=0 by simp [Laurent.size],Nat.cast_zero,_root_.zero_div, add_zero, one_pow,mul_one] at ht
 apply le_trans _ ht; rw [←spex j G w T M b (heel G o) i]; apply le_of_eq (congr_arg (fun f=>paidX f _) (show nook_T o m=_ from funext fun i=>cue_l G w o m i)) -- definal HT streak
omit e p
variable (F K:Matrix Kt (Single c) ℂ)(P:Op Kt) {a b d:ℝ}(hF:∀ i:Kt,paidX (nook_T o m) (fun k=>F i k) ≤ a)(hK:∀ i:Kt,paidX (nook_T o m) (fun k=>K i k) ≤ b)(ha:0≤a)(hb:0≤b)
local notation "OpF"=> Op (Single c)
local notation "Zτ"=> paid_M
include hF hK ha hb
lemma paid_g (p:‖P‖≤ d): paid_M o (Fᴴ * P * K) m ≤ (Fintype.card Kt:ℝ)^2*(2*a*b*d):=by
 let f(i:Kt)(x:Single c):=F i x; let k(i:Kt)(x:Single c):=K i x; let X(i:Kt×Kt):=P i.1 i.2 • dishV (f i.1) (k i.2)
 have hv:1 ≤ W:=nook_l o m; have hv':0≤W:=fun i=>zero_le_one.trans (hv i)
 let Q:=2*a*b*d
 have he(i:Kt×Kt): paidX (coyF W) (X i)≤ Q:=by
    unfold X; rw [p_smul,fork_p,dish_p,dish_p]; have hp:= (norm_nonneg _).trans p
    let g:= f i.1; let v:= k i.2; let S:Single c→ℝ:=1; have hs:0≤S:= fun _=>zero_le_one; have hx:paidX S g≤ a:=(chargeO S W hs hv _).trans (hF i.1); have ht:paidX S v≤ b:=(chargeO S W hs hv _).trans (hK i.2)
    refine (mul_le_mul ((norm_entry P i.1 i.2).trans p) (add_le_add (mul_le_mul (hF i.1) ht (windL S v hs) ha) (mul_le_mul hx (hK i.2) (windL W v hv') ha)) (add_nonneg (mul_nonneg (windL W g hv') (windL S v hs)) (mul_nonneg (windL S g hs) (windL W v hv'))) hp).trans_eq ?_; unfold Q; ring
 unfold paid_M; rw [show pinF (Fᴴ * P *K)=∑ i:Kt×Kt,X i from ?_]; swap
 · ext1 q; rw [Finset.sum_apply]; conv_rhs=>rw [Fintype.sum_prod_type,sum_comm]
   change ((Fᴴ* P)*K) _ _=_; rw [Matrix.mul_apply]; apply sum_congr rfl; intro i _; rw [Matrix.mul_apply,sum_mul]; apply sum_congr rfl; intro j _; change star (F j _)* P j i* K i _= P j i*(star (F j _)*K i _); ring
 apply (p_posts (coyF W) (fun i=> add_nonneg (hv' i.1) (hv' i.2)) _ X).trans; refine (sum_le_sum (fun i _=> he i)).trans ?_; simp [Fintype.card_prod,Q,pow_two]
omit hF hK ha hb
lemma paid_posts (Φ:Finset Axis)(V:Axis→Op (Single c)): paid_M o (∑ i∈Φ,V i) m ≤ ∑ i∈Φ, paid_M o (V i) m:=by
 induction Φ using Finset.induction with
 | empty=> simp [paid_M,paidX,show pinF (0:OpF)=0 from rfl]
 | insert _ _ h u=> rw [sum_insert h,sum_insert h]; exact (paidp_sum ..).trans (add_le_add (le_refl _) u)
include p e
-- total upper Ψ value from jets. 
lemma field_v : ∃ C:ℝ,0 ≤ C∧∀ {c f:Side}(o:Site c)(G:Ratio c f)(w:Odd G.count.val)(T:Script Male),Use j G.count @T →∀ M:Male,∀ X:Dome,∀ a b:ℝ,‖X.1‖≤ a → (∀ i, ‖X.2.1 i‖≤b)→(∀ i,‖X.2.2 i‖≤b) → paid_M o (chipF j G w T M (heel G o) X) m≤ C * ((lace 0 G.count)^2*a+8*(lace 0 G.count*lace 1 G.count)*b):=by
 obtain ⟨A,z,u⟩:= αp j m e p false; obtain ⟨B,y,v⟩:= αp j m e p true; let C:=(Fintype.card Kt:ℝ)^2*(2*A*B); refine ⟨C,by unfold C; positivity,fun {c f} o G w T H M X a b g i l=>?_ ⟩
 let FA:= wingF j G w T M false (heel G o); let FB:= wingF j G w T M true (heel G o); let W_K(d):=lace d G.count; have hp(d):0≤ W_K d:=by unfold W_K lace; positivity
 let Y(i t:List Axis)(y:Pal):= (FA i)ᴴ * y * FB t
 have h (i t:List Axis)(p':i.length ≤2)(v':t.length≤2)(Z:Pal)(k:ℝ)(r:‖Z‖≤k): paid_M o (Y i t Z) m≤ C*(W_K i.length * W_K t.length)*k:=by refine (paid_g m o _ _ Z (u o G w T H M _ p') (v o G w T H M _ v') (mul_nonneg z (hp _)) (mul_nonneg y (hp _)) r).trans_eq ?_; unfold C W_K; ring
 let Tp:=C*(W_K 0 * W_K 1)*b; have hd : paid_M o (∑ j:Axis, Y [] [j] (X.2.2 j)) m ≤ 4*Tp:=by
    apply (paid_posts m o univ _).trans; apply le_trans (b:=∑ j:Axis,Tp) (sum_le_sum (fun j _=> h [] [j] (by simp) (by simp) _ b (l j))); simp [Axis]
 have hg : paid_M o (∑ j:Axis, Y [j] [] (X.2.1 j)) m ≤ 4*Tp:=by
    apply (paid_posts m o univ _).trans; refine (sum_le_sum (g:=fun _=> Tp) ?_).trans (by simp [Axis]); intro j _; refine (h [j] [] (by simp) (by simp) _ b (i j)).trans_eq ?_; change C*(W_K 1 *W_K 0)* b=_; unfold Tp; ring
 unfold chipF; refine (paidp_sum ..).trans ((add_le_add ((paidp_sum ..).trans (add_le_add (h [] [] (by simp) (by simp) _ _ g) hd)) hg).trans_eq ?_); unfold Tp W_K; change C* (lace 0 G.count* lace 0 G.count) *a+_+_= _; ring
end YM.CF.Hove
