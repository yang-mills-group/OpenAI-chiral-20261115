import YM.CF.BPress.Meadow.Aroma
import YM.CF.Jet.Operetta
import YM.CF.BPress.Spin.Energy
/- Matrix layer fees. trueX* on each point. Strengthening of needed $q_H/8$ across all parameters. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Meadow
open Function Finset Filter NormedSpace Metric SU SU.Pair Mesa Fock Lattice Cube Lat Spin Spin.Paint Dial Grid Grid.Entity Delivery Lute Lute.Kite Lute.Fort MeasureTheory RG Net Tent Sheet Frame
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s:Side}(W:Tunnel s){v:ℝ}
@[fun_prop] lemma swivel_cont : Continuous (fun x:E× Op SU.Slot => swivelC x.1 x.2):=by unfold swivelC; simp_rw [congrC]; exact ((matter_cont.comp continuous_fst).mul continuous_snd).mul (matter_cont.comp continuous_fst).matrix_transpose
lemma swivel_smooth (i:E) : ContDiff ℝ ∞ (swivelC i):=by unfold swivelC congrC; exact (contDiff_const.mul contDiff_id).mul contDiff_const
lemma shuffle_r (g:E) (x:Sprout):fullM (scaledV g x).val=swivelC g (fullM x.val):= full_cong ..
lemma smooth_const (A:Type)[NormedAddCommGroup A][NormedSpace ℝ A] (Q: Op SU.Slot) : ContDiff ℝ ∞ (fun _:A=>Q):=contDiff_const
lemma rotate_s {a b:Mach s}{P:Paint s} : rotateC a (rotateC b P)=rotateC (a*b) P:= funext fun i=> (turn_add ..).symm
abbrev fare(U:Micro s)(P:Paint s)(i:Link s):= ‖P i.1-swivelC (U i) (P (endAt i))‖
lemma runway (U:Micro s)(x:Link s)(a:Mach s)(P:Paint s):fare (gauge a U) (rotateC a P) x=fare U P x:=by unfold fare rotateC Lattice.gauge; rw [← turn_add, mul_assoc,inv_mul_cancel,mul_one,turn_add, Paint.iso] -- tune endAt
lemma fare_plain(U:Micro s)(P:Paint s)(i:Link s): fare U P i≤ ‖P i.1 - P (endAt i)‖+2*sphereRate*chord (U i) 1*‖P (endAt i)‖:=by unfold fare; apply (norm_sub_le_norm_sub_add_norm_sub _ (P (endAt i)) _).trans; rw [norm_sub_rev (P (endAt i)) (swivelC (U i) (P (endAt i)))]; exact add_le_add le_rfl (Bend.moving ..) -- tune
lemma Fare_cheap (c:E)(U A: Op SU.Slot)(L:ℝ)(p:‖U-A‖≤ L): ‖swivelC c U-swivelC c A‖≤ L:=by rwa [Paint.iso]
lemma fee_base : ∃ K:ℝ≥0, ∀ (s:Side)(U:Micro s)(H:marks s)(i:Link s), fare U (fun i=>fullM (H i).val) i ≤ K*urgent U i H:=by
 obtain ⟨K,k⟩:= Smooth.lip_near (isCompact_sphere (0:Vect) 1) (f:= fullM) (fun _ _ => Jet.full_k (k:=1) |>.contDiffAt); refine ⟨K,fun s U H i=>?_⟩; let x:= H i.1; let y:= scaledV (U i) (H (endAt i)); unfold fare; rw [←shuffle_r, ←dist_eq_norm, urgent, dist_comm]; exact k.dist_le_mul y.val y.property x.val x.property
abbrev κ_tri:= fee_base.choose
lemma norm_κ(A:Op SU.Slot)(p:Spin.Sym A):‖A‖=1:= CStarRing.norm_of_mem_unitary p.gate
-- pocket $u(t,y)$ for N paths. s horizon param based on depth ratio. joint smooth.
abbrev ramp0 (v:ℝ):= 1-jogger (1/10) (1/6) v
def theme (x:ℝ×ℝ):=B_theme (ramp0 x.1 * α x.2)
lemma theme_s : ContDiff ℝ ∞ theme:= shape_cost.smooth.comp (f:=fun x:ℝ×ℝ=> ramp0 x.1*α x.2) (by unfold ramp0; fun_prop)
lemma theme_v (x:ℝ×ℝ) : Spin.Sym (theme x):= shape_cost.special _
lemma theme_entry (u): theme (u,0)=fullM embed:=by unfold theme; simp only [al0,mul_zero,shape_cost.head]
lemma theme_o (u v:ℝ)(p:u≤1/10): theme (u,v)=B_theme (α v):=by unfold theme ramp0; rw [jog_lo (by norm_num) p,sub_zero, one_mul] -- tune tuple reduc
lemma theme_last (u v:ℝ)(p:1/6≤u): theme (u,v)=fullM embed:=by unfold theme ramp0; rw [jog_hi (by norm_num) p,sub_self, zero_mul,shape_cost.head]
lemma theme_exit (p:1≤v) (x:ℝ):theme (x,v)=theme (x,1):=by have he:=alpha_final (show 1/2≤v by linarith); unfold theme; rw [he,al1]
-- pay tag cost. 
abbrev active := Set.Icc (-1:ℝ) 3
lemma charge :∃ K:ℝ≥0,LipschitzOnWith K theme (Hotel ×ˢ active):= Smooth.lip_near (isCompact_Icc.prod isCompact_Icc) fun _ _=> theme_s.contDiffAt.of_le (by norm_num) -- ENNReal top simp
abbrev κ_theme:=charge.choose

def depthP (x:Site s):ℝ:= (burial W x:ℝ)/W.n.val
lemma depth_cap (x:Site s) : depthP W x∈ Hotel:=by
 unfold depthP; refine ⟨by positivity, (div_le_one (Lat.nPos W.n)).mpr ?_⟩; unfold burial distanceQ; exact_mod_cast ((min_le_right ..).trans (Nat.sub_le W.n.val (corner W x)))
lemma depth_step (i:Link s) (p:i∈ inside W.mem): |depthP W i.1-depthP W (endAt i)| ≤ (W.n.val:ℝ)⁻¹:= by
 unfold depthP; rw [←sub_div,abs_div,abs_of_pos (nPos W.n),←one_div]; apply div_le_div_of_nonneg_right _ (nPos W.n).le; obtain ⟨a,b⟩:= Tent.stepDeep W i p; have ht:(burial W i.1:ℝ) ≤ burial W (endAt i)+1:=by exact_mod_cast a
 have he:(burial W (endAt i):ℝ) ≤ burial W i.1+1:=by exact_mod_cast b
 rw [abs_le]; constructor <;> linarith
lemma credit (i:Link s)(p:i∈ inside W.mem)(v:ℝ)(t:v∈ active) : ‖theme (depthP W i.1,v)-theme (depthP W (endAt i),v)‖≤ κ_theme*(W.n.val:ℝ)⁻¹:=by
 let V(x:Site s) : ℝ×ℝ:=(depthP W x,v); have ht(x):V x∈Hotel×ˢactive:=⟨depth_cap W x,t⟩
 rw [←dist_eq_norm]; apply (charge.choose_spec.dist_le_mul _ (ht i.1) _ (ht (endAt i))).trans
 apply mul_le_mul_of_nonneg_left _ κ_theme.property; unfold V; rw [Prod.dist_eq, Real.dist_eq]; exact max_le (depth_step W i p) (by simp [Lat.nPos])
end YM.CF.BPress.Meadow
