import YM.CF.Cascade.Oars
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
def hike (p: Momentum):Site n→ℂ:=fun x=> mode p (lift x)
lemma addI (G:Ratio c f)(i:Site G.count)(p:Site c)(x y:Site f):let g:=hike (aliasAt (mon p) i); g (x+y)=g x*g y:=by
 intro g; unfold g hike; rw [←mode_shift]; exact mesh_alias G p i (by rw [wrap_lift,map_add,wrap_lift,wrap_lift])
lemma singI (x y:Site n)(u:Momentum)(t:Cover)(h:x=y+wrap n t)(g:∀ t:Cover,mode u (n.val • t)=1): hike u x=hike u y*mode u t:=by -- general
 subst x; unfold hike; rw [←mode_shift]
 obtain ⟨i,he⟩:=cover_of_eq (lift (y+wrap n t)) (lift y+t) (show wrap n _= _ by rw [wrap_lift,map_add,wrap_lift]); rw [he,mode_shift,g,mul_one]
lemma apart (G:Ratio c f)(h:Odd G.count.val)(p:Site c)(u v:Site G.count)(e:u≠v): ∃ t:Cover, mode (aliasAt (mon p) u) (2 • t)≠ mode (aliasAt (mon p) v) (2 • t):=by
 obtain ⟨i,f⟩:= step_picks (u-v) (sub_ne_zero_of_ne e)
 obtain ⟨r,s⟩:=h
 let T:Cover:= (r+1) • step i; refine ⟨T,fun g=>f ?_⟩
 rw [aliasAt,aliasAt,mode_phase,mode_phase] at g
 have he:wrap G.count (2 • T)=step i:=by
    unfold T; rw [←mul_smul,show 2*(r+1)=G.count.val+1 from by omega, add_smul, map_add,joint_heads,one_smul, wrap_step,zero_add]
 have hx:= mul_left_cancel₀ (Complex.exp_ne_zero _) g
 rw [←he,cell_sub,cell_wrap,cell_wrap,hx]; exact mul_inv_cancel₀ (Complex.exp_ne_zero _)
local notation "Z" => coord (1:Axis)
abbrev Sky(n:Side):= Body 1 n →ℂ
def alto(p:Momentum): Sky n:= fun x=> if x.2=Z then hike p x.1 else 0
lemma rot_col(p:Site n)(x: Body 1 n): rotations n _ x (p,Z)= alto (mon p) x:=rfl
lemma pines(p:0<k)(r:4≤j)(s:4≤t)(P:Flight j t)(w:f.val=c.val * P.L.val)(x:Site c)(h:mon x 1=0): let G:=P.visitRatio w; approached (installed G (Flight.duo k P).A0) *ᵥ alto (mon x)= ∑ l:Site P.L, angel k P (mon x) l • (alto (n:=f) (aliasAt (mon x) l)):=by
 intro G
 obtain ⟨H,-⟩:= secure_both k p r s
 have ht:= P.sail_run w H r 1; let U:= approached (installed G (Flight.duo k P).A0); let F':= rotations c (TypeFace 1); let R:= readings G (TypeFace 1); let A:= solo c (P.fromBank (Flight.pilot k) 1)
 have hu:U * F'= R*A:=ht; funext ⟨v,y⟩; change (U*F') (v,y) (x,Z)=_; rw [hu, Matrix.mul_apply]
 change ∑ i: Site c× Co P.L (TypeFace 1),R (v,y) i*A i (x,Z)= _
 rw [Fintype.sum_prod_type,sum_eq_single x]; swap; intro i _ g; simp [A,solo,fiber,g]; swap; simp
 change ∑ z:Site P.L×TypeFace 1,_= _; rw [Fintype.sum_prod_type,Finset.sum_apply]; apply sum_congr rfl; intro i _; rw [sum_eq_single Z]; swap; intro j _ g; simp [A,solo,Flight.fromBank,fiber,downAlias, aheadQ P _ h i j g]; swap; simp
 have he : A (x,i,Z) (x,Z)=angel k P (mon x) i:=by unfold A angel; simp [solo,fiber,downAlias, Flight.fromBank]
 rw [he]; change R (v,y) (x,i,Z)*_= _ * alto _ _; rw [mul_comm]; congr 1; exact sample ..
open Cube
lemma mon0 (p:3≤(More n).val): mon (step 0: Site (More n))= port n:=by
 unfold mon; rw [lift_step p]; funext i; by_cases h:i=0; · subst i; simp [port,spark,reciprocal,pinch,More]; field_simp
 simp [port,spark,h,reciprocal,pinch]
lemma slideN(G:Ratio n f):pinch f=pinch n/G.count.val:=by unfold pinch; rw [G.exact_size,Nat.cast_mul,div_div]
lemma slideK (G: Ratio n f):aliasAt (port n) (0:Site G.count)=port f:=by
 funext i; by_cases h:i=0; · subst i; simp [port,spark,aliasAt, slideN G]; ring
 simp [port,spark,aliasAt,h]
lemma areaC(n:Side):lengthSq (port n)=pinch n^2:=by
 unfold lengthSq; rw [sum_eq_single (0:Axis)]; simp [port,spark]; intro i _ g; simp [port,spark,g]; simp
lemma norm_p(n:Side):‖port n‖=pinch n:=by
 apply le_antisymm; · apply (pi_norm_le_iff_of_nonneg (pinch_pos _|>.le)).mpr; intro i; by_cases h:i=0<;>simp [port,spark,h,abs_of_pos (pinch_pos _),(pinch_pos _).le]
 refine le_trans ?_ (norm_le_pi_norm (port n) 0); simp [port,spark,abs_of_pos (pinch_pos _)]
lemma neck {a:ℝ}(p:0<a):∃ j:ℕ,∀ n:Side,j≤n.val→pinch n<a:=by obtain ⟨j,h⟩:=exists_nat_gt (Real.pi/a); exact ⟨j,fun n s=> (div_lt_iff₀ (side_pos _)).2 ((div_lt_iff₀ p).mp (h.trans_le (by exact_mod_cast s)) |>.trans_eq (mul_comm ..))⟩ -- length suppress
end YM.CF.Cascade
