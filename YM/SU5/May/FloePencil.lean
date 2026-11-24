import YM.SU5.May.FloeRange
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
open Stationary (Gaia)
open Buffered.Lifted
lemma gleams: ∃ C:ℝ,∀ x:Gaia,‖gleamV x‖ ≤ C*‖x‖:=by
 let A:= ∑ i:Axis, ‖gammaOp i‖; refine ⟨‖minA‖*A, fun x=> (norm_mul_le ..).trans ?_⟩; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg minA); unfold A; rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_); rw [norm_smul,Complex.norm_real,mul_comm]; exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x _) (norm_nonneg _)
lemma printed (ε:ℝ)(p:0<ε): ∀ᶠ E:ℝ in atTop,∀ x:Gaia,E ≤ ‖x‖→‖Onyx.pencil x‖ ≤ ε:=by
 obtain ⟨C,H⟩:= gleams; have he:Tendsto (fun r:ℝ=> C/(Real.pi^2*r^3)) atTop (𝓝 0):= tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (n:=3) (by decide)).const_mul_atTop (by positivity : (0:ℝ)<Real.pi^2)) -- n name
 filter_upwards [eventually_gt_atTop (0:ℝ),Filter.eventually_forall_ge_atTop.mpr (he.eventually (ge_mem_nhds p))] with E a h x w -- helper nonexistent
 apply le_trans _ (h ‖x‖ w); unfold Onyx.pencil; rw [norm_smul, Real.norm_of_nonneg (by positivity : 0≤ (Real.pi^2*‖x‖^4)⁻¹)]
 have hp:= a.trans_le w; apply le_trans (mul_le_mul_of_nonneg_left (H _) (by positivity)) (le_of_eq ?_); field_simp -- tune
lemma plotFar (s t:Personality)(ε:ℝ)(p:0<ε):∀ᶠ D:ℝ in atTop,∀ x:Gaia, D ≤ ‖x‖ → ‖toward x s t‖ ≤ ε:=by
 let C:=1+‖s.voice‖*‖t.voice‖; set v:=ε/C; have hb:0<C:=by unfold C; positivity
 have he:0<v:=div_pos p hb; refine (printed v he).mono (fun D u x w=>?_); unfold toward; split; swap; · rw [norm_zero]; exact p.le
 apply (norm_inner_le_norm (𝕜:=ℂ) ..).trans; have hk:= (Flare.opy (Onyx.pencil x) t.voice).trans (mul_le_mul_of_nonneg_right (u _ w) (norm_nonneg _)); apply le_trans (mul_le_mul_of_nonneg_left hk (norm_nonneg s.voice));
 rw [mul_left_comm ‖s.voice‖]; exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one : ‖s.voice‖*‖t.voice‖≤ C) he.le).trans_eq (div_mul_cancel₀ ε hb.ne')
lemma posterFare (s t:Personality)(ε:ℝ)(p:0<ε):∀ᶠ D:ℝ in atTop,∀ (x y:Gaia), D ≤ ‖x-y‖→‖poster x y s t‖ ≤ ε:=by
 filter_upwards [plotFar s t ε p, plotFar t s ε p] with D h g x y t; unfold poster; split
 · rw [norm_zero]; exact p.le
 split; exact h _ t; rw [norm_neg]; exact g _ ((norm_sub_rev x y) ▸ t)
variable {j:ℕ}{N:Side}(x y:Cover) (p: Odd N.val)(c d : Trace j N)
include p
lemma ticked (A:ℝ)(n:ℕ)(h:n ≥ A+j)(e:x-y∉ box n): A ≤ ‖nature N x c-nature N y d‖:=by -- include p!!!
 have he:∃ i:Axis, ¬ (- (n:ℤ) ≤(x-y) i ∧ (x-y) i ≤ (n:ℤ)):= by
    contrapose! e; rw [box_test]; exact ⟨fun i=>(e i).1,fun i=>(e i).2⟩
 obtain ⟨i,v⟩:=he; let V(i:Axis):=(x-y) i; have hv : |↑(V i)| ≥ (n:ℝ):= by have ht: n≤ |V i|:=(by unfold V; exact le_of_not_gt fun w=>v ((abs_lt.mp w).imp (fun h=>h.le) (fun h=>h.le))); exact_mod_cast ht -- coe unresolved
 let z:=nature N x c-nature N y d; have hp: |(↑(V i):ℝ)| ≤ j+|z i|:=by
    refine le_trans (?_ : _ ≤ |(↑(V i):ℝ) - z i| +|z i| ) (add_le_add_left (cost_coord x y p ..) _); nth_rw 1 [show (↑(V i):ℝ) = ↑(V i)-z i+ z i from by ring]; exact abs_add_le ..
 change A ≤ _; exact le_trans (b:=|z i|) (by linarith only [hp,hv,h]) (PiLp.norm_apply_le z i)
omit p in
lemma all_poster (s t:Personality)(ε:ℝ)(e:0<ε):∃ n:ℕ,∀ (x y:Cover)(u:x-y∉ box n),∀ (N:Side)(p: Odd N.val) (c d:Trace j N), ‖poster (nature N x c) (nature N y d) s t‖ ≤ ε:=by
 obtain ⟨D,h⟩:=(posterFare s t ε e).exists; obtain ⟨n,u⟩:=exists_nat_gt (D+(j:ℝ)); exact ⟨n, fun x y g N p c d=> h _ _ (ticked x y p c d D _ u.le g)⟩
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.all_poster
