import YM.CF.Tap.Camper
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (m:ℕ)
abbrev gum (i:ℝ):= (1+i)^m
variable {ι:Type*}[Fintype ι]
def paidX(H:ι→ℝ)(F:ι→ℂ):=∑ i,H i* ‖F i‖
lemma p_negative (H:ι→ℝ)(F:ι→ℂ): paidX H (-F)= paidX H F:=by simp [paidX]
variable {H:ι→ℝ}(p:∀ i, 0≤H i){f g: ι→ℂ}
include p in
lemma p_sum (f g:ι→ℂ): paidX H (f+g) ≤ paidX H f+ paidX H g:=by unfold paidX; rw [←sum_add_distrib]; apply sum_le_sum; intro i _; rw [←mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le ..) (p i)
lemma p_smul(k:ℂ)(F:ι→ℂ) (V:ι→ℝ): paidX V (k • F)=‖k‖*paidX V F:=by unfold paidX; rw [mul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [Pi.smul_apply, norm_smul]; ring
-- Newton row coefficient
variable (F: List Axis→Cover→ (ι→ℂ)) (h:∀ D i z,F (i::D) z= F D (z+step i)- F D z)
def trix (x:Cover):ι→ℂ:= ∑ i, (x i:ℂ) • F [i] 0
def thorn (x:Cover): ι→ℂ:= F [] x-(F [] 0+ trix F x)
private lemma thorn_o: thorn F 0=0:=by simp [thorn,trix]
private lemma p_abs (W:Cover→ (ι→ℂ))(x y:Cover): paidX H (W y-W x)= paidX H (W x-W y):=by rw [←p_negative H,neg_sub]
private lemma size_stepK (i:Axis):Laurent.size (step i)=1:=by unfold Laurent.size; rw [sum_eq_single i]; simp; intro _ _ h; simp [h]; simp
lemma worth (W:Walk): Laurent.size (stop (0:Cover) W) ≤ W.length:=by
 induction W using List.reverseRecOn with
 | nil => simp [stop,Laurent.size];
 | append_singleton P s ih =>
    rw [stop_append,stop,stop,List.length_append,List.length_singleton]; refine (Laurent.size_add ..).trans (Nat.add_le_add ih ?_); obtain ⟨i,_|_⟩:=s; exact (size_stepK i).le
    change Laurent.size (-step i)≤1; simp [Laurent.size_neg,size_stepK]
private lemma trix_i(z:Cover)(i:Axis): trix F (z+step i)=trix F z+F [i] 0:=by unfold trix; simp only [Pi.add_apply,Int.cast_add,add_smul,sum_add_distrib]; congr 1; simp -- tune
include h
lemma thorn_w (i:Axis)(z:Cover): thorn F (z+step i)-thorn F z=F [i] z - F [i] 0:=by unfold thorn; rw [trix_i]; rw [show F [] (z+step i)= F [i] z + F [] z from eq_add_of_sub_eq ((h [] i z).symm)]; abel
include p
private lemma walkPaid {L:ℕ}{A:ℝ}(hp:0≤A)(W:Walk)(w:W.length≤L)(i:Axis)(hv:∀ i j z,Laurent.size z ≤ L → paidX H (F [i,j] z)≤A): paidX H (F [i] (stop (0:Cover) W)-F [i] 0)≤ W.length*A:=by
 induction W using List.reverseRecOn with
 | nil => simp [stop,paidX]
 | append_singleton l s ih =>
    simp only [List.length_append,List.length_singleton] at w; have hp0:= ih (by omega); let z:=stop (0:Cover) l; let x:=stop z [s]; let g(x):=F [i] x
    have hk:x=z+s.vec:=rfl
    have hz: paidX H (g x-g z) ≤ A:=by
       cases s with | mk j b=>
        cases b
        · rw [hk]; change paidX H (F [i] (z+ step j)-F [i] z)≤_; rw [←h]; exact hv _ _ _ ((worth l).trans (by omega))
        rw [p_abs g z x]; have hw:z=x+step j:=by rw [hk]; change z=z+ -(step j)+step j; abel
        rw [hw, show g (x+step j)- g x=F [j,i] x from (h ..).symm] -- tune
        exact hv _ _ x (by rw [show x=stop (0:Cover) (l++[⟨j,true⟩]) from ?_]; exact (worth _).trans (by simpa); rw [stop_append])
    rw [stop_append, List.length_append, List.length_singleton]; change paidX H (g x - g 0)≤ _; rw [show g x-g 0=(g x-g z)+(g z-g 0) by abel]; refine (p_sum p _ _).trans ((add_le_add hz hp0).trans ?_); push_cast; exact le_of_eq (by ring)
lemma walkPaid_p {L:ℕ}{A:ℝ}(hp:0≤A)(W:Walk)(w:W.length≤L)(hv:∀ i j z,Laurent.size z ≤ L → paidX H (F [i,j] z)≤A): paidX H (thorn F (stop (0:Cover) W)) ≤ W.length*((L:ℝ)*A):=by
 induction W using List.reverseRecOn with
 | nil=> simp [stop,thorn_o,paidX]
 | append_singleton l s ih=>
    have hy:l.length ≤ L:=by rw [List.length_append,List.length_singleton] at w; omega
    let z:=stop (0:Cover) l; let x:=stop z [s]; have hp':= ih hy
    have he:paidX H (thorn F x - thorn F z) ≤ L*A:=by
       cases s with | mk j b=>
        cases b
        · rw [show x=z+step j from rfl,thorn_w F h]; refine (walkPaid p F h hp l hy _ hv).trans ?_; gcongr -- tune
        rw [p_abs]; have hx:z=x+step j:=by change z=z+ -(step j)+step j; abel
        rw [hx, thorn_w F h j]; rw [show x=stop (0:Cover) (l++[⟨j,true⟩]) from (by rw [stop_append])]; refine (walkPaid p F h hp _ w j hv).trans ?_; gcongr
    rw [List.length_append,List.length_singleton,stop_append]; change paidX H (thorn F x) ≤ _; rw [show thorn F x=thorn F x-thorn F z+thorn F z from (by abel)]; refine (p_sum p _ _).trans ((add_le_add he hp').trans ?_); push_cast; exact le_of_eq (by ring)
end YM.CF.Tap
