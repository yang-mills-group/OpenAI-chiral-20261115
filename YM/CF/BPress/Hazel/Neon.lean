import YM.CF.BPress.Meadow.August
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}{u v γ : ℝ} (z: Fin 5)
abbrev remainderW := fun p:ℝ×ℝ => p.1*β p.2*(1-Lute.Kite.bound (p.2-1))
def neonT(p:ℝ × ℝ):= hopper z (remainderW p/2) * dict z (1,p.2) * (hopper z (remainderW p/2))ᵀ
lemma beta_ret (h:1 ≤ u) : β u=1:=by unfold β; rw [comp_apply,bound_hi (by linarith), β_1] -- tune
abbrev trip (γ u:ℝ):= γ+(1-γ)*Lute.Kite.bound (u-1)
lemma neon_early (p:u ≤ 1/2) : neonT z (γ,u)=swivelC (orb z) (B_theme (α u)):=by
 rw [neonT]; dsimp only [remainderW]; rw [beta_start p, mul_zero,zero_mul, zero_div,edge_lower z p,hopper, rot_0,Matrix.transpose_one,mul_one,one_mul]
lemma neon_junction(p:1/2≤u)(t:u≤1): neonT z (γ,u)= tap z (1-(1-γ)*β u):=by
 rw [neonT,edge_middle z p t,Kite.mix_shift]; unfold remainderW; rw [bound_lo (show u-1 ≤ 1/8 by linarith)]; congr 1; ring
lemma neon_future (p:1≤u) : neonT z (γ,u)= tap z (trip γ u):=by rw [neonT,edge_upper z p,Kite.mix_shift]; unfold remainderW trip; rw [beta_ret p]; congr 1; ring
lemma neon_traces(u γ:ℝ): Spin.Sym (neonT z (γ,u)):=by rcases le_or_gt u (1/2) with h|h; rw [neon_early z h]; exact turn_plan (shape_cost.special _) _; rcases le_or_gt u 1 with g|g; rw [neon_junction z h.le g]; exact payoff ..; rw [neon_future z g.le]; exact payoff ..
lemma neon_smooth : ContDiff ℝ ∞ (neonT z):=by
 let f:=fun p:ℝ×ℝ=>hopper z (remainderW p/2); have he: ContDiff ℝ ∞ f:= ((smooth_h z).of_le le_top).comp (f:=fun p:ℝ×ℝ=>remainderW p/2) (by unfold remainderW; fun_prop); let g(p:ℝ×ℝ):=dict z (1,p.2); have ht:ContDiff ℝ ∞ g:=contDiff_iff_contDiffAt.mpr (fun p=> ((dict_s z (1,p.2) H1).2).comp p (f:=fun t:ℝ×ℝ=>(1,t.2)) (by fun_prop))
 refine (he.mul ht).mul ?_; exact contDiff_iff_contDiffAt.mpr fun p=> Lute.mat_smooth _ _ fun i j=>(key_entry j i).contDiffAt.comp p he.contDiffAt -- tune
lemma neon_plain (v:ℝ) : neonT z (1,v)= swivelC (orb z) (B_theme (α v)):=by
 by_cases h: v ≤ 1/2; exact neon_early z h; rw [alpha_final (by linarith),shape_cost.tail]; rcases le_or_gt v 1 with h'|h'; rw [neon_junction z (by linarith) h']; simp only [sub_self,zero_mul,sub_zero, close_t]; rw [neon_future z h'.le]; simp only [trip,sub_self,zero_mul,add_zero, close_t]
lemma neon_face(v:ℝ) : neonT z (0,v)=dict z (1,v):=by simp only [neonT,remainderW,zero_mul,zero_div, hopper,rot_0,Matrix.transpose_one,mul_one,one_mul] -- tune
lemma neon_last (γ:ℝ)(h:2 ≤ u): neonT z (γ,u)=Music.wave z:=by rw [neon_future z (by linarith : 1≤u), trip,bound_hi (by linarith : 1-1/8 ≤ u-1),mul_one,add_sub_cancel,close_t] -- tune
-- geometry chord-frame comparison
abbrev closeC (h:E)(z:Fin 5):= h⁻¹ * Mag.center z
abbrev castN (h:E)(z: Fin 5)(γ v:ℝ) := swivelC (closeC h z) (neonT z (γ,v))
lemma cast_plan (h:E): Spin.Sym (castN h z γ v):= turn_plan (neon_traces ..) _
lemma usual_cast (h:E)(z:Fin 5)(A:Op SU.Slot): swivelC (closeC h z) (swivelC (orb z) A)=swivelC h⁻¹ A:=by rw [←turn_add,closeC,orb, mul_assoc,mul_inv_cancel, mul_one]
lemma cast_final (h:E) (t:2≤u): castN h z γ u=swivelC h⁻¹ Music.basis:=by rw [castN, neon_last z _ t]; exact usual_cast ..
lemma cast_pure(v:ℝ)(h:E):castN h z 1 v= swivelC h⁻¹ (B_theme (α v)):=by rw [castN,neon_plain,usual_cast]
lemma cast_seed (h:E): castN h z γ 0=fullM (scaledV h⁻¹ Seed).val:=by rw [castN,neon_early z (by norm_num : (0:ℝ) ≤ 1/2),usual_cast,al0,shape_cost.head,shuffle_r]; rfl
lemma close_cost_q (h:E): chord (closeC h z) 1=chord h (Mag.center z):=by
 conv_lhs => arg 2; rw [← inv_mul_cancel h]
 rw [closeC,chord.left,chord.comm] -- tune
abbrev μH := 2*sphereRate
lemma close_cost (h:E)(P: Op SU.Slot) {a:ℝ}(t:chord h (Mag.center z)≤ a): ‖swivelC (closeC h z) P-P‖≤ μH*a*‖P‖:=by refine (Bend.moving ..).trans ?_; rw [close_cost_q]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left t (by positivity [sphereRate_cost.positive])) (norm_nonneg _)
lemma swift(h:E)(P:Op Slot) (p:Spin.Sym P){a:ℝ}(t:chord h (Mag.center z)≤ a): ‖swivelC (closeC h z) P-P‖≤ μH*a := (close_cost z h P t).trans (by rw [norm_κ _ p,mul_one]) -- le rfl
-- Room norm bound for `till k`; choose purchase σ=3
lemma till_norm : ‖till z‖≤3:=by
 apply (norm_le_norm_sub_add (till z) Music.basis).trans; have hx:= Lute.Music.bill z 0 H0; rw [open_t,norm_sub_rev] at hx; rw [norm_κ _ basis_acts]; linarith -- tune
end YM.CF.BPress.Hazel
