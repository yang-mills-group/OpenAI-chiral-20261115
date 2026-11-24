import YM.CF.Tap.Sila
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
lemma disp {ι:Type*}[Fintype ι](S:Finset Axis)(F:Axis→ι→ℂ)(H:ι→ℝ)(h:∀ i,0≤ H i):paidX H (∑ i∈ S,F i) ≤ ∑ i∈ S,paidX H (F i):=by
 induction S using Finset.induction_on with
 | empty=> simp [paidX]
 | @insert i S hi ih=>rw [sum_insert hi,sum_insert hi]; exact (p_sum h _ _).trans (add_le_add_right ih _)
abbrev lace (D:ℕ)(L:Side):= Real.sqrt L.val/(L.val:ℝ)^(D+2)
lemma lumpK(j m:ℕ)(p:Even j)(e:4≤j)(u:Bool):∃ C:ℝ,0<C ∧∀{c f:Side}(G:Ratio c f)(h:Odd G.count.val)(T:Script Male), Use j G.count @T → ∀ M: Male,∀ v:Single f,∀ x:Cover,∀ D:List Axis,D.length ≤ 2 → paidX (streak G m v) (pax G h T j u M v D x)≤ C* lace D.length G.count * (1+(Laurent.size x:ℝ)/oneF G)^m:=by
 choose B H K using fun D: {x:List Axis // x.length ≤ 2}=>ferryY j p u m D.val (by have:=D.property; omega)
 have hl : {x:List Axis|x.length ≤2}.Finite:=List.finite_length_le Axis 2 -- tune
 let R: Finset (List Axis):=hl.toFinset
 let A(x:List Axis):ℝ:=if g:x.length ≤2 then B ⟨x,g⟩ else 0
 have ht(x):0≤A x:=by unfold A; split; apply (H _).le; rfl
 let C:=1+∑ i∈R,A i; have hp:1≤C:= le_add_of_nonneg_right (sum_nonneg fun i _=> ht i)
 refine ⟨C,one_pos.trans_le hp,fun {c f} G h t e M v x D z=>?_⟩ -- implicit arity tune
 let d: {x:List Axis // x.length≤2}:=⟨D,z⟩; have hv:B d≤ C:=by unfold C; rw [show B d=A D by simp [A,z,d]]; apply le_trans (single_le_sum (f:=A) (fun i _=> ht i) _ ) (le_add_of_nonneg_left (by norm_num)); exact hl.mem_toFinset.mpr z
 refine (K d G h t e M v x).trans ?_; unfold followV; change B d * lace D.length G.count * _≤ _; gcongr
private lemma taylorH (x:Cover) : ∃ w:Walk,stop (0:Cover) w=x ∧ w.length ≤ 4*Laurent.size x:=by
 refine ⟨_,route_end 0 x 1,route_size 0 x 1 _ (fun i=>?_)⟩; have hp:(x i).natAbs≤ Laurent.size x:= Finset.single_le_sum (f:=fun i:Axis=>(x i).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ i); simpa
lemma resto(j m:ℕ)(h:Even j)(v:4≤j)(p:2≤m)(u:Bool):∃ A:ℝ,0<A∧∀{c f:Side}(G: Ratio c f)(w:Odd G.count.val)(T:Script Male),Use j G.count @T→∀ (M:Male)(x:Single f)(b:Cover), paidX (streak G m x) (thorn (pax G w T j u M x) b)≤ A*lace 2 G.count*tweight m b:=by
 obtain ⟨C,he,H⟩:=lumpK j m h v u; refine ⟨16*5^m*C+ (2^m+5)*C,by positivity,fun {c f} G w T s M x b=>?_⟩
 let L:=oneF G; let P:=pax G w T j u M x; let W:= streak G m x; have hT:1≤L:= by unfold L oneF; exact_mod_cast G.count.property -- tune
 let A:=lace 2 G.count; have hA:0<A:=by unfold A lace; positivity
 let l:= Laurent.size b; let y:ℝ:=l; have hp:0≤y:= Nat.cast_nonneg _
 by_cases g:l ≤ G.count.val
 · obtain ⟨z,hz,q⟩:= taylorH b; let t:=4*l; have hx: z.length ≤ t:=q; let B:=5^m*C*A; have ha: 0≤B:=by unfold B; positivity
   have hW:∀ i j z,Laurent.size z≤t→ paidX W (P [i,j] z)≤B:=by
      intro i k z u'; apply (H G w T s M x z [i,k] (by simp)).trans
      have h: (Laurent.size z:ℝ)≤ 4*L:=by unfold L oneF; exact_mod_cast u'.trans (Nat.mul_le_mul_left 4 g)
      change C*A*(1+ _/L)^m≤_; rw [show B=C*A*5^m by unfold B; ring]; apply mul_le_mul_of_nonneg_left _ (by positivity); refine pow_le_pow_left₀ (by positivity) ?_ m; linarith only [(div_le_iff₀ (zero_lt_one.trans_le hT)).mpr h] -- tune
   have hl:0≤ W:= streak_pos G m x; have ht:= walkPaid_p hl P (fun D i z=> pax_e G w T j s h u M x D i z (by omega)) ha z hx hW; rw [hz] at ht; refine ht.trans ?_; have hk : ((z.length:ℕ):ℝ)≤ 4*y:= by unfold t at hx; unfold y; exact_mod_cast hx
   calc
     _ ≤ 4*y*((t:ℝ)*B):=by gcongr
     _ = (16*5^m*C)*A*y^2:=by unfold B t y; push_cast; ring
     _ ≤_:=by
        have hu: y^2≤ tweight m b:= (pow_le_pow_left₀ hp (show y≤ 1+y by linarith) 2).trans (pow_le_pow_right₀ (by linarith : 1≤ 1+y) p)
        change _≤ (_+_)*A*tweight _ _; gcongr; apply le_add_of_nonneg_right; positivity
 let V:=streak G m x; have hk:L≤y:=by unfold L oneF y; exact_mod_cast Nat.le_of_not_ge g
 let X:= 1+y/L; let r:=C*A*tweight m b; have hv:0≤ tweight m b:=tw_pos ..
 have hy:lace 0 G.count = A * L^2 ∧ lace 1 G.count = A*L:=by unfold A lace L oneF; have he:= side_pos G.count; constructor <;>field_simp <;> ring
 have hw:L^2≤ tweight m b:=(pow_le_pow_left₀ (by positivity) (show L≤1+y by linarith) 2).trans (pow_le_pow_right₀ (by linarith : 1 ≤ 1+y) p)
 have hb:L*y≤ tweight m b:=(show L*y≤(1+y)^2 from by nlinarith only [hp, mul_le_mul_of_nonneg_right hk hp]).trans (pow_le_pow_right₀ (by linarith : 1 ≤ 1+y) p)
 have hxA:paidX V (P [] 0)≤ r:=by refine (H G w T s M x 0 [] (by decide)).trans ?_; simp only [List.length_nil, hy.1,show Laurent.size (0:Cover)=0 by simp [Laurent.size], Nat.cast_zero,_root_.zero_div,add_zero,one_pow,mul_one]; unfold r; rw [←mul_assoc]; gcongr
 have heP (i):paidX V ((b i:ℂ) • P [i] 0)≤ r:=by
    rw [p_smul]; have hp:(b i).natAbs ≤l:= Finset.single_le_sum (f:=fun i:Axis=>(b i).natAbs) (fun _ _=> Nat.zero_le _) (mem_univ i); refine (mul_le_mul_of_nonneg_left (H G w T s M x 0 [i] (by simp)) (norm_nonneg _)).trans ?_; simp only [List.length_cons,List.length_nil,zero_add,hy.2,show Laurent.size (0:Cover)=0 by simp [Laurent.size],Nat.cast_zero,_root_.zero_div,add_zero,one_pow,mul_one]; calc
      _ ≤ y * (C*(A*L)):=by apply mul_le_mul_of_nonneg_right (Push.Loops.axis_le_size ..); positivity
      _ ≤ _:=by unfold r; rw [show y*(C* (A*L))= C*A*(L*y) by ring]; gcongr
 have hpX: paidX V (P [] b) ≤ 2^m*r:=by
    refine (H G w T s M x b [] (by decide)).trans ?_; simp only [List.length_nil,hy.1]; unfold r; change C*(A*L^2) * _ ≤ _; have ht: tweight m b=(1+y)^m:=rfl
    rw [mul_comm (2^m:ℝ),ht, mul_assoc (C*A), ←mul_pow]; rw [←mul_assoc C, mul_assoc (C*A)]; apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hw:L^2*X^m ≤ ((1+y)*2)^m:=by
       have hm:L^m*X^m=(L+y)^m:=by rw [←mul_pow]; apply congrArg (·^m); unfold X; field_simp
       apply le_trans _ (le_trans hm.le (pow_le_pow_left₀ (by linarith) (by linarith : L+y≤(1+y)*2) m)); exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT p) (by unfold X; positivity)
    exact hw
 have hZ:paidX V (trix P b) ≤ 4*r:=by apply (disp univ _ V (streak_pos G _ x)).trans; refine (sum_le_sum (fun i _=> heP i)).trans ?_; simp [Axis] -- tune
 have hu:0≤V:= streak_pos G _ x
 change paidX V _≤ _; unfold thorn; rw [sub_eq_add_neg]; refine (p_sum hu _ _).trans ((add_le_add hpX (show paidX V (-(P [] 0+ trix P b))≤r+4*r from ?_)).trans ?_)
 · rw [p_negative]; exact (p_sum hu _ _).trans (add_le_add hxA hZ)
 unfold r; change _ ≤ (_+_)*A*tweight _ _; nlinarith only [mul_nonneg (show 0≤16*5^(m:ℕ)*C*A by positivity) hv]
end YM.CF.Tap
