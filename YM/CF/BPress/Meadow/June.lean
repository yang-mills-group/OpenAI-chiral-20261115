import YM.CF.BPress.Meadow.Arch
/- "Mark H° with joint path prices exact; no local regularity in making extension assumed" -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Meadow
open Function Finset Filter NormedSpace Metric SU SU.Pair Mesa Fock Lattice Cube Lat Spin Spin.Paint Dial Grid Grid.Entity Delivery Lute Lute.Kite Lute.Fort MeasureTheory Net Tent Sheet Frame Lute.Music
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s:Side}{T:Sheet.Atlas}{L y C C':ℝ}{b:ℕ}(W:Tunnel s)(F:Net s T L y C C' b) (U: Micro s)(p:Duo s)(k:Tiling s){v x :ℝ}
namespace Frame
open Tunnel
def stalk(v:ℝ): Paint s:= fun x => if x∈cloak W (body W) then swivelC ((haloM W p) x)⁻¹ (theme (depthP W x,v)) else fullM (ferns W F U p k x).val
def whole(v:ℝ): Paint s:= rotateC (W.axial U)⁻¹ (stalk W F U p k v)
local notation "P"=> stalk W F U p k
local notation "D"=>haloM W p
local notation "T₀"=>ferns W F U p k
lemma stalk_spec(x:ℝ): MatPlan (P x):=by intro i; unfold stalk; split; exact turn_plan (theme_v _) _; exact Spin.Sym.full _ (vote_unit _)
lemma whole_spec(x:ℝ): MatPlan (whole W F U p k x):= fun i=> turn_plan (stalk_spec W F U p k x i) _
lemma stalk_smooth (x:Site s) :ContDiff ℝ ∞ (fun v=> P v x):=by unfold stalk; split; exact (swivel_smooth _).comp (theme_s.comp (f:=fun v=>(depthP W x,v)) (by fun_prop)); exact contDiff_const
lemma whole_smooth (x:Site s) :ContDiff ℝ ∞ (fun v=> whole W F U p k v x):=(swivel_smooth _).comp (stalk_smooth ..)
lemma beginning_stalk (x:Site s): P 0 x= fullM (T₀ x).val:=by
 unfold stalk; split; next h=> rw [ferns,if_pos h,headM, shuffle,shuffle_r,theme_entry]; rw [show (headS s x).val=embed from rfl]; rfl
 next h=> rfl
lemma beginning_whole (x:Site s):whole W F U p k 0 x=fullM (sprigs W F U p k x).val:=by unfold whole rotateC; rw [beginning_stalk]; exact (shuffle_r ..).symm
lemma stationary_p (u:ℝ)(h:1 ≤u): stalk W F U p k u=P 1:=by funext i; unfold stalk; split; rw [theme_exit h]; rfl
lemma stationary_W (u:ℝ)(h:1≤u): whole W F U p k u=whole W F U p k 1:=by unfold whole; rw [stationary_p _ _ _ _ k u h]
lemma stalk_m (x:ℝ)(i:Site s): Measurable (fun u:Micro s × Duo s=> stalk W F u.1 u.2 k x i):=by
 unfold stalk; split; swap; · exact full_cont.measurable.comp (f:=fun u:Micro s × Duo s=> (ferns W F u.1 u.2 k i).val) (measurable_subtype_coe.comp ((measurable_pi_apply i).comp (ferns_m ..)))
 exact swivel_cont.measurable.comp (f:=fun u: Micro s×Duo s=> ((haloM W u.2 i)⁻¹,theme (depthP W i,x))) ((((measurable_pi_apply i).comp ((halo_meas W).comp measurable_snd)).inv).prodMk measurable_const)
lemma whole_m (x:ℝ)(i:Site s): Measurable (fun u:Micro s × Duo s=> whole W F u.1 u.2 k x i):= swivel_cont.measurable.comp (f:=fun u:Micro s × Duo s=> ((W.axial u.1 i)⁻¹,stalk W F u.1 u.2 k x i)) ((((measurable_pi_apply i).comp (W.axial_cont.measurable.comp measurable_fst)).inv).prodMk (stalk_m W F k x i))
lemma price_path (i:Site s) : LipschitzOnWith κ_theme (fun u=> P u i) Meadow.active:=by
 apply LipschitzOnWith.of_dist_le_mul; intro x a y b; unfold stalk; split; next h =>
    rw [dist_eq_norm,Paint.iso,←dist_eq_norm]; let Z(z:ℝ):ℝ×ℝ:=(depthP W i,z); apply (Meadow.charge.choose_spec.dist_le_mul (Z _) ⟨depth_cap ..,a⟩ (Z _) ⟨depth_cap ..,b⟩).trans_eq; unfold Z; rw [Prod.dist_eq]; simp [κ_theme]
 next h => rw [dist_self]; positivity
lemma price_W (i:Site s) : LipschitzOnWith κ_theme (fun u=> whole W F U p k u i) Meadow.active:=by
 apply LipschitzOnWith.of_dist_le_mul; intro x a y b; dsimp only [whole,rotateC]; rw [dist_eq_norm,Paint.iso, ←dist_eq_norm]; exact (price_path W F U p k i).dist_le_mul x a y b
lemma gauge_stalk(a : Mach s)(v:ℝ): stalk W F (gauge a U) (p*(W.framesE a)⁻¹) k v= rotateC (W.branchM a) (P v):=by
 funext x; unfold rotateC; simp only [stalk]; split; next h=> rw [gauge_halo]; rw [Pi.mul_apply, Pi.inv_apply, mul_inv_rev,inv_inv,Paint.turn_add]; -- tune
 next h=> rw [gauge_fern]; exact shuffle_r ..
lemma gauge_whole(a:Mach s)(v:ℝ): Set.EqOn (whole W F (gauge a U) (p*(W.framesE a)⁻¹) k v) (rotateC a (whole W F U p k v)) W.mem:=by
 unfold whole; rw [gauge_stalk,rotate_s,rotate_s]; intro i h; have ht:= W.overlap U a h; let A:=W.axial (gauge a U); let B:=W.branchM a; let C:=W.axial U; have he:A i*a i=B i*C i:=ht
 change swivelC ((A i)⁻¹*B i) _= swivelC (a i*(C i)⁻¹) _; rw [show B i=A i*a i*(C i)⁻¹ from by rw [he]; group]; congr 1; group -- group
lemma stalk_l (V:Micro s)(h:Lattice.Agrees W.mem U V) : stalk W F U p k=stalk W F V p k:=by unfold stalk; rw [fern_local _ _ _ _ k V h]
lemma whole_l (V:Micro s)(h:Lattice.Agrees W.mem U V) : whole W F U p k=whole W F V p k:=by unfold whole; rw [stalk_l _ _ _ _ k V h,W.axial_only U (fun i t=>h _ ((inside_iff ..).mp (W.stores_sub t)).1 ((inside_iff ..).mp (W.stores_sub t)).2)]
lemma mantle_bone (x:Site s)(p:x∈W.mem)(h:W.n.val ≤6* burial W x)(u:ℝ) : theme (depthP W x,u)=fullM embed:=by
 apply theme_last; refine (le_div_iff₀ (nPos W.n)).mpr ?_ ; have hx:(W.n.val:ℝ) ≤6*burial W x:=by exact_mod_cast h
 linarith
lemma confine_data (u:ℝ)(i:Link s)(h:i∉ inside (cloak W (body W)))(q:i∈inside W.mem)(p':30 ≤ W.n.val)(x:Site s)(vx:x=i.1∨x=endAt i): P u x=fullM (T₀ x).val:=by
 unfold stalk; split; swap; · rfl
 rename_i e; have hp:= (mem_filter.mp e).1; rw [mantle_bone W x hp _ u,ferns, if_pos e,headM, shuffle, shuffle_r]; rfl
 obtain ⟨a,b⟩:=inside_iff ..|>.mp q; have ht:= stepDeep W i q; have he:= mt (inside_iff ..|>.mpr) h; rw [cloak_mem W a, cloak_mem W b] at he; rcases vx with rfl|rfl <;> (unfold Tent.body at *; simp only [endAt] at *; omega)
-- budget; later $p^M$ terms use r and 8r
abbrev january(y:ℝ)(W:Tunnel s):= κ_theme*(W.n.val:ℝ)⁻¹+(2*sphereRate)*(amt y)
def tagC(r s:Side)(y:ℝ) := κ_theme*(s.val:ℝ)⁻¹+(2*sphereRate)*(amt y)+κ_tri*inheritance r -- combined, chooses instead max
lemma price_inside (K:Launch W F U p k)(v:ℝ)(t:v∈Meadow.active)(i:Link s)(h:i∈inside (cloak W (body W))) : fare (W.orient U) (P v) i≤ january y W:=by
 let B:= gauge D (W.orient U); let Q:= rotateC D (P v); have hb : ∀ x∈cloak W (body W),Q x=theme (depthP W x,v):=fun x p=>by unfold Q rotateC; rw [stalk,if_pos p,←turn_add,mul_inv_cancel,turn_one]
 obtain ⟨a,b⟩:= inside_iff ..|>.mp h; have hv: i∈inside W.mem:=inside_cov (cloak_sub ..) h
 have ht(V:Op SU.Slot)(x:Spin.Sym V) : ‖V‖=1:=norm_κ V x; have he: chord (B i) 1 ≤ amt y:=by
    let S':= cloak W W.lips; have he:cloak W (body W)⊆ S':= fun i t=> mem_filter.mpr ⟨(mem_filter.mp t).1, (mem_filter.mp t).2.trans (Nat.le_add_right ..|>.trans K.wardK.2.1)⟩; exact inside_cost W F U p K.toFirm i (he a) (he b)
 rw [←runway (W.orient U) i D]; apply (fare_plain B Q i).trans; rw [hb _ a,hb _ b, ht _ (theme_v _)]; exact add_le_add (credit W i hv v t) (by simp only [mul_one]; gcongr; have he:=sphereRate_cost.positive; positivity)
lemma price_H (K:Launch W F U p k)(w:30≤W.n.val)(v:ℝ)(t:v∈Meadow.active)(i:Link s)(h:i∈inside W.mem) : fare (W.orient U) (P v) i ≤ max (january y W) (κ_tri * inheritance k.b) := by
 by_cases f:i∈inside (cloak W (body W)); exact le_trans (price_inside W F U p k K v t i f) (le_max_left ..)
 apply le_trans ?_ (le_max_right ..); unfold fare; rw [confine_data W F U p k v i f h w _ (Or.inl rfl),confine_data W F U p k v i f h w _ (Or.inr rfl)]; exact (fee_base.choose_spec s _ T₀ i).trans (mul_le_mul_of_nonneg_left (flowering W F U p k K i h) κ_tri.property)
lemma price_Z (K:Launch W F U p k)(w:30≤ W.n.val)(v:ℝ)(t:v∈ Meadow.active)(i:Link s)(h:i∈inside W.mem) : fare U (whole W F U p k v) i≤ max (january y W) (κ_tri * inheritance k.b):=by
 rw [←runway U i (W.axial U),whole,rotate_s,mul_inv_cancel, show rotateC (1:Mach s) (P v)=P v by funext x; exact Paint.turn_one _]; exact price_H W F U p k K w v t i h -- tune
end Frame
end YM.CF.BPress.Meadow
