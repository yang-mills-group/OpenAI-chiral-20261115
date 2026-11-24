import YM.CF.Hove.Out
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

variable{c f:Side}(G:Ratio c f)(w:Odd G.count.val)(T:Script Male)(j m:ℕ)(e:Use j G.count T)(p:Even j)(u:Bool)(M:Male)(o:Site f)
variable(h:1≤j)(X:Cover)(z':Single c)(i s:Kt)
local notation "Pa"=> Paw j M u
local notation "V"=> toneT G w T j u M o
local notation "Fx"=> feeT G m o
local notation "L₀"=> lace 0 G.count
local notation "L₁"=> lace 1 G.count
local notation "L₂"=> lace 2 G.count
variable(A:ℝ)(hp:∀ (s:Kt) x D,D.length ≤ 2→paidX (feeT G m o) (toneT G w T j u M o s D x) ≤ A*lace D.length G.count * ratioY (Tap.oneF G) m x)
abbrev m_fee (u:Bool):= ‖(baseF u)‖ + ∑ j:Axis,‖ditF u j‖
lemma mpe (u:Bool):0 ≤ m_fee u:=add_nonneg (norm_nonneg _) (sum_nonneg fun _ _=>norm_nonneg _)
lemma mp_iv : ‖baseF u i s‖ ≤ m_fee u:= (by
 unfold m_fee; exact le_trans (norm_entry _ _ _) (le_add_of_nonneg_right (sum_nonneg fun _ _=> norm_nonneg _))) -- lamp?
lemma mon_v (a:Axis):‖moonB u a X i s‖≤ (1+(Laurent.size X:ℝ))*m_fee u:=by
 have h:‖ditF u a i s‖ ≤ m_fee u:= le_trans (norm_entry _ _ _) ((single_le_sum (fun b (_:b∈ univ)=>norm_nonneg (ditF u b)) (mem_univ a)).trans (le_add_of_nonneg_left (norm_nonneg _))) -- lamp
 change ‖(X a:ℂ)*baseF u i s+ _‖≤ _; refine (norm_add_le _ _).trans ?_; rw [norm_mul]; exact (add_le_add (mul_le_mul (Push.Loops.axis_le_size X a) (mp_iv u i s) (norm_nonneg _) (by positivity)) h).trans_eq (by ring) -- tune
include hp
omit hp
abbrev b_fee (P:ℝ) (Y:Bool):ℝ:= (Fintype.card Kt:ℝ)* (Fintype.card Axis * (P*m_fee Y))
variable (ha: 0 ≤ A)
include hp ha
lemma ν_le (g:ℕ)(v:g≤2): paidX Fx (indexF G w T j u M o i) ≤ b_fee A u* L₀:=by
 have hY:0≤ b_fee A u:= by unfold b_fee; have:= mpe u; positivity
 apply le_trans (p_posts Fx (fun s=> zero_le_one.trans (feeK G _ o s)) _ _)
 have h(i s:Kt): paidX Fx (vowel G w T j u M o i s)≤ m_fee u *(A*L₀):=by
    unfold vowel; rw [p_smul]; apply mul_le_mul (mp_iv u i s) _ (sum_nonneg fun i _=> mul_nonneg (zero_le_one.trans (feeK G _ o _)) (norm_nonneg _)) (mpe u)
    simpa only [List.length_nil,paidX,ratioY, Laurent.size, Pi.zero_apply, Int.natAbs_zero,sum_const_zero,Nat.cast_zero,_root_.zero_div,add_zero,one_pow,mul_one] using hp s 0 [] (by simp) -- tune
 refine (sum_le_sum (fun s _=>h i s)).trans ?_; simp only [sum_const,card_univ,nsmul_eq_mul]
 conv_lhs=> rw [show (m_fee _ * _)= _ from (show m_fee u*(A*L₀)= (A*m_fee u)*L₀ by ring),←mul_assoc]
 apply mul_le_mul_of_nonneg_right _ (by unfold lace; positivity); unfold b_fee; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (mul_nonneg ha (mpe _)) (by simp [Axis])) (Nat.cast_nonneg _)
lemma ν_p : paidX Fx (plyT G w T j u M o i X)≤ b_fee A u*((1+(Laurent.size X:ℝ))*L₁):=by
 have ht:0≤Fx:= fun s=> zero_le_one.trans (feeK G _ o s)
 apply le_trans (p_posts Fx ht _ _)
 let b:ℝ:=1+(Laurent.size X:ℝ); have hb:0≤b:=by unfold b; positivity
 have h(i s):paidX Fx (apron G w T j u M o X i s)≤ Fintype.card Axis*(b*m_fee u * (A* L₁)):=by
    apply le_trans (p_posts Fx ht _ _)
    apply (sum_le_sum (g:=fun _=>b*m_fee u*(A*L₁)) _).trans; · simp
    intro a _; rw [p_smul]; apply mul_le_mul (mon_v u X i s a) _ (sum_nonneg fun r _=>mul_nonneg (ht _) (norm_nonneg _)) (mul_nonneg hb (mpe _))
    simpa only [List.length_cons,List.length_nil,zero_add,paidX,ratioY, Laurent.size, Pi.zero_apply, Int.natAbs_zero,sum_const_zero,Nat.cast_zero,_root_.zero_div,add_zero,one_pow,mul_one] using hp s 0 [a] (by simp) -- tune
 apply (sum_le_sum (fun s _=> h i s)).trans; simp only [sum_const, card_univ,nsmul_eq_mul]; apply le_of_eq; unfold b_fee b; ring
omit hp ha
private lemma lace_o (B:Side)(n:ℕ):0 ≤ Tap.lace n B:=by unfold lace; positivity
variable(vP:4≤j)(qQ : 2 ≤ m)
include vP p qQ
lemma font_u :∃ C:ℝ,0<C∧∀{c f:Side}(G:Ratio c f)(w:Odd G.count.val)(T:Script Male), Use j G.count @T→∀(M:Male)(o:Site f)(i:Kt)(x:Cover), let H:=feeT G m o; let L:=G.count; let F:=flute G w T j u M o i x; let W:=indexF G w T j u M o i; let Qv:=plyT G w T j u M o i x; paidX H F ≤ C*(lace 0 L*ratioY (Tap.oneF G) m x) ∧ paidX H W ≤ C*lace 0 L ∧ paidX H Qv ≤ C*((1+(Laurent.size x:ℝ))*lace 1 L) ∧ paidX H (F-(W+Qv)) ≤ C*(tweight m x*lace 2 L) :=by
 obtain ⟨A,hP,U⟩:= lumpK j m p vP u; obtain ⟨Y0,v,G₀⟩:=pawn_p j m (by omega) u
 obtain ⟨A',hQ,K⟩:= Tap.resto j m p vP qQ u; let C:ℝ:=Fintype.card Kt * ((A+A')*Y0)
 have hz':0 < C:= by unfold C; positivity
 refine ⟨C+b_fee A u,add_pos_of_pos_of_nonneg hz' (by unfold b_fee; have hh:=mpe u; positivity), fun {c f} G w T ht M o i x=>?_⟩
 intro H L F W Q'
 have hp (s:Kt) x d (p:d.length ≤ 2) : paidX (feeT G m o) (toneT G w T j u M o s d x) ≤ A*lace d.length L* ratioY (Tap.oneF G) m x:=U G w T ht M (stickW o s) x d p -- d inference
 have h1:0 ≤ ratioY (Tap.oneF G) m x:=by unfold ratioY; positivity
 have hB:0≤b_fee A u:=by unfold b_fee; have h:=mpe u; positivity
 have hv : (Fintype.card Kt:ℝ)*(A*Y0) ≤ C+b_fee A u:=by refine le_trans ?_ (le_add_of_nonneg_right hB); unfold C; gcongr; apply le_add_of_nonneg_right hQ.le
 have hx : (Fintype.card Kt:ℝ)*(A'*Y0) ≤ C+b_fee A u:=by refine le_trans ?_ (le_add_of_nonneg_right hB); unfold C; gcongr; apply le_add_of_nonneg_left hP.le
 refine ⟨(post_P G w T j m u M o x i Y0 _ (G₀ M) (mul_nonneg hP.le (lace_o L 0)) (fun s X=>hp s X [] (by simp)) (by omega)).trans ?_,(ν_le G w T j m u M o i _ hp hP.le 0 (by omega)).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hz'.le) (lace_o L 0)),(ν_p G w T j m u M o x i _ hp hP.le).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hz'.le) (mul_nonneg (by positivity) (lace_o L 1))), (post_Y G w T j m u M o x i Y0 (A'*lace 2 L) (G₀ M) (mul_nonneg hQ.le (lace_o L _)) (fun s X=>K G w T ht M (stickW o s) X) (by omega)).trans ?_⟩
 · refine le_trans ?_ (mul_le_mul_of_nonneg_right hv (mul_nonneg (lace_o L 0) h1)); apply le_of_eq; ring
 refine le_trans ?_ (mul_le_mul_of_nonneg_right hx (mul_nonneg (tw_pos ..) (lace_o L 2))); apply le_of_eq; ring
omit qQ
lemma flute_p : ∃ C:ℝ,0<C ∧∀{c f:Side}(G:Ratio c f)(w:Odd G.count.val)(T:Script Male),Use j G.count @T→∀ (M:Male)(o:Site f)(i:Kt)(x:Cover), paidX 1 (flute G w T j u M o i x)≤ C* lace 0 G.count:=by
 obtain ⟨A,hP,U⟩:= lumpK j 0 p vP u; obtain ⟨Y0,v,G₀⟩:=pawn_p j 0 (by omega) u; refine ⟨Fintype.card Kt*(A*Y0),by positivity,fun {c f} G w T ht M o i x=>?_⟩
 have he(s:Kt)(z:Cover):paidX (feeT G 0 o) (toneT G w T j u M o s [] z) ≤ A*lace 0 G.count* ratioY (Tap.oneF G) 0 z:=U G w T ht M (stickW o s) z [] (by simp)
 rw [show (1: Single c→ℝ)=feeT G 0 o from funext fun x=>by simp [feeT,Tap.streak,gum]]
 apply (post_P G w T j 0 u M o x i _ _ (G₀ M) (mul_nonneg hP.le (lace_o G.count 0)) he (by omega)).trans_eq; simp only [ratioY,pow_zero,mul_one]; ring
end YM.CF.Hove
