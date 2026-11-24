import YM.CF.Sods.Pail
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sods
open Function Filter Metric Finset Kea Lat Lattice Laurent Fir Rush Tulip Cube SU
open scoped Topology BigOperators Matrix ContDiff Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{k:ℝ}
abbrev Cart(N:Side):=Site N→E
def drift(x:Site N)(i:Axis):Prop:= natural x i +1=N.val
def cyclic(N:Side)(i:Axis):Walk:= List.replicate N.val (posDir i)
def roller(x:Site N):Walk:=route 0 (natural x) 1
def yolk(U:Bkg N)(i:Axis): E:=travel U 0 (cyclic N i)
def layout(U:Bkg N):Cart N:= fun i=> travel U 0 (roller i)
instance(x:Site N)(i:Axis):Decidable (drift x i):=by unfold drift; infer_instance
def wob(N:Side)(P:Axis→ E):Bkg N:=fun x=> if drift x.1 x.2 then P x.2 else 1
lemma swifts(n:ℕ)(a:Axis)(x:Cover):stop x (List.replicate n (posDir a))=x+n • step a:=by induction n generalizing x <;> simp_all [List.replicate_succ,stop,add_mul] <;> abel
lemma end_C(N:Side)(a:Axis):stop (0:Cover) (cyclic N a)= N.val • step a:=by simp only [cyclic,swifts,zero_add]
lemma end_fn(N:Side)(a:Axis):stop (0:Site N) (cyclic N a)=0:=by nth_rw 1 [←map_zero (wrap N)]; rw [←wrap_stop_cover,end_C,map_nsmul]; ext i; change (N.val:ℕ) • (_:Per N) =0; simp
lemma end_roll(x:Site N): stop (0:Site N) (roller x)=x:=by rw [←map_zero (wrap N),← wrap_stop_cover,roller,route_end,nat_true]
lemma cyc_money(U:Bkg N)(p:0≤k)(f:PlaqBound firstF U k)(i j:Axis):Switch (fund (yolk U i)) (fund (yolk U j)) (32*N.val^2*k):=by
 let u:=cyclic N i; let v:=cyclic N j; have hx:stop (0:Cover) (u++v)=stop 0 (v++u):=by rw [stop_append,stop_append]; unfold u v cyclic; simp [swifts,add_comm] -- tune
 have he:=near_hop p f 0 (u++v) (v++u) hx; rw [travel_append,travel_append,show stop (0:Site N) u=0 from end_fn ..,show stop (0:Site N) v=0 from end_fn ..] at he; refine he.trans_eq ?_; simp only [u,v,List.length_append,cyclic,List.length_replicate]; push_cast; ring
lemma adjoins(x:Site N)(a:Axis): natural x+step a=natural (x+step a)+(if drift x a then N.val • step a else 0):=by
 funext i; by_cases h:i=a; swap; · unfold natural; by_cases t:drift x a <;> simp [h,t,Lattice.step_apply]
 subst i
 have he: (x+step a:Site N) a=x a+1:=by simp
 change _ = (↑(((x+step a:Site N) a).val):ℤ)+_
 let R:=(x a).val; have hx:R<N.val:=ZMod.val_lt _; rw [he,show x a +1=((R+1:ℕ):Per N) from (by simp [R])]; rw [ZMod.val_natCast]; simp only [Pi.add_apply, Lattice.step_apply,ite_true]; change ((R:ℤ)+1)= _ + _; split_ifs with h; change (R:ℤ)+1=N.val at h; change _=(↑((R+1)%N.val):ℤ)+ (N.val:ℕ) • ((step a:Cover) a); simp only [step_apply,ite_true,nsmul_eq_mul,mul_one]; rw [show R+1=N.val by omega,Nat.mod_self,h]; simp
 change ¬ ((R:ℤ)+1=N.val) at h; rw [Nat.mod_eq_of_lt (show R+1<N.val by omega)]; simp
lemma roll_size(x:Site N):(roller x).length≤4*N.val:=by apply Cube.route_size; intro i; unfold natural; simp only [Pi.zero_apply,sub_zero,Int.natAbs_natCast]; exact (ZMod.val_lt (x i)).le
lemma paleB(U:Bkg N)(p:0≤k)(f:PlaqBound firstF U k)(x):cmp firstF (gauge (layout U) U x) (wob N (yolk U) x)≤ (400*(N.val:ℝ)^2)*k:=by
 obtain ⟨x,a⟩:=x; let y:=x+step a; let b:= drift x a; let w:= if drift x a then cyclic N a else []; let D:= roller x++[posDir a]; let Z:=w++roller y
 have hx:stop (0:Cover) D= stop 0 Z:=by
    unfold D Z; rw [stop_append,stop_append,roller,roller,route_end,Lattice.stop,Step.vec_pos,Lattice.stop,adjoins]
    have ht:=stop_trans (stop (0:Cover) w) 0 (roller y); rw [add_zero,roller,route_end] at ht; rw [ht]; unfold w; split <;> simp only [end_C, Lattice.stop] <;> rw [add_comm];
 have hv:travel U 0 D=layout U x*U (x,a):=by unfold D; rw [travel_append,end_roll,travel,Step.pos_read,travel,mul_one,layout]
 have hr:travel U 0 Z=wob N (yolk U) (x,a)*layout U y:=by unfold Z; rw [travel_append]; unfold w wob; by_cases h:drift x a <;> simp only [h,ite_true,ite_false,end_fn] <;> rfl
 have he:= near_hop p f 0 D Z hx
 have hg:(D.length:ℝ)≤5*N.val:=by unfold D; simp only [List.length_append,List.length_cons,List.length_nil]; exact_mod_cast (by norm_num; have hx:=roll_size x; have ht:1≤N.val:=N.property; omega : (roller x).length + (0+1) ≤ 5*N.val)
 have hm:(Z.length:ℝ)≤5*N.val:=by
    have hs:w.length ≤ N.val:=by unfold w; split<;> simp [cyclic]
    have ht:= roll_size y; unfold Z; rw [List.length_append]; exact_mod_cast show w.length+ _≤5*N.val by omega
 rw [hv,hr] at he; rw [← cmp_right firstF (gauge _ _ _) (wob _ _ _) ((layout U) y)]; unfold Lattice.gauge; change cmp _ (layout U x*U (x,a)*(layout U y)⁻¹*layout U y) _ ≤ _; rw [inv_mul_cancel_right]; refine he.trans ?_; rw [←add_mul]; apply mul_le_mul_of_nonneg_right _ p; nlinarith [pow_le_pow_left₀ (by positivity) hg 2,pow_le_pow_left₀ (by positivity) hm 2]
end YM.CF.Sods
