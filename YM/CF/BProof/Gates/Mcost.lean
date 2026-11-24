import YM.CF.BProof.Gates.Flags
import YM.CF.BProof.Charge.Mark

/- prechosen purchases for Mark support factors. Mark W frame toll remains h.F (no
 Fock defs). Sup nonoffset per slot; total gauge K all fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gates.Stage.Setup
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing Micro Push.AbsoluteSums Moment
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}(P:Entice S L a d y){s:Side}(Y:S.Setup L a s d y)
variable (T:PathData G)(θ:ℝ)(U:Config G s)(i:Y.yard.Index)(F:Y.yard.FaceS)
-- on nonzero density in either frame. used building additional kernels at operators even before fixing.
include P
lemma eye_price (p:¬Y.yard.D i→ lifts (Y.yard.u i) Y.yard.long y Y.hall U (F i))(h:Y.yard.toll i y Y.hall U F ≠0) : Calm (Y.yard.u i) Y.yard.long U (thresh y/2):=by
 let D:=Y.yard; have hu : ∀ t:ℝ, t ≤ thresh y/2 → Calm (Y.yard.u i) Y.yard.long U t→ Calm (Y.yard.u i) Y.yard.long U (thresh y/2):=fun t p h=> ⟨fun x y j v=> (h.1 x y j v).trans p,fun x y j v=> (h.2 x y j v).trans p⟩
 unfold Yard.toll at h; split at h
 · rename_i k; let t:=S.scene.charge*mA y; let q:=t-4*xi y; apply hu (q+4*xi y) (by rw [show q+4*xi y=t from sub_add_cancel ..]; exact (P.dull.home 0).2); exact calm_D _ _ y U D.lL q (fun i k=> Angular.shut_pays _ _ y U h i ((mem_wash ..).1 k)) (fun i=> by unfold q t; linarith only [(P.dull.home i).1]) -- tune
 rename_i k; have hx:=P.dull.frame s Y.hall rfl rfl (Y.sized P) P.Fqual (D.u i) U (F i); rw [← length P Y] at hx; obtain ⟨v,e,q⟩:= hx (p k); exact hu _ q (calm_N _ _ y _ U _ D.lL D.long_pos (stream_pays _ _ y _ U _ h) v (Face.blend_p ..).le e)
-- entropy fees
abbrev piT (l:ℕ)(y:ℝ) := Real.log ((4/xi y)^matDim G)*((l+1:ℕ)*4)
lemma shell_fee : Y.yard.toll i y Y.hall U F ≤ Real.exp (piT (DP L a y) y * (s.val:ℝ)^3):=by
 apply le_trans (Y.yard.toll_pay _ y _ _ _ P.dull.smallXi).2; apply le_of_eq; rw [Y.length P]; unfold piT; let k:=((4/xi y)^matDim G); have he:0<k:=by unfold k; have hv:= coin_pos y (-3/2) 0 0; positivity -- tune `k : ℝ`
 rw [show _*((_:ℝ)^3)=(((DP L a y+1)*s.val^3*4:ℕ):ℝ)*Real.log k from ?_,Real.exp_nat_mul, Real.exp_log he]; unfold k; push_cast; ring
lemma toll_local (W:Config G s)(z: Eyes s) (h: Agrees ↑(Y.yard.band i) U W) (G':Y.yard.FaceS)(v:F i=G' i): Y.yard.toll i y Y.hall U F=Y.yard.toll i y Y.hall W G':=by unfold Yard.toll; split; exact shut_local (Y.yard.u i) Y.yard.long y U W h; rw [v]; exact stream_local (Y.yard.u i) Y.yard.long y Y.hall U _ Y.yard.lL W h
variable (β:ℝ)(A:T.Bounds c w R v)(q:BudgetPoint)(h: q.threshold=thresh y)
lemma outlay_fee (t:0≤β)(p:β≤2*y): ‖outlay Y.yard i c q T (S.M y) β U (fogBill (y:=y) S.M T β A q (permits P q h))‖ ≤
    mCost c R (2*y) (Weights.rent y S.M R w v) (DP L a y)*(s.val:ℝ)^3:=by
 let f:= Y.yard; apply (outlay_cost Y.yard i c q T (S.M y) β U _ t q.threshold_le A (a:=(uPull_p w S.W (S.M y)).le) (b:=weak_p c q T (S.M y) β A _ s)).trans; rw [Y.length P,h]; unfold mCost
 have hr:= c.quadratic_pos; have ht:= share_pos; gcongr; unfold Weights.rent; apply Charge.rate_le w R v S.W (S.M y) (coin_pos ..).le _ _ _; rw [abs_of_nonneg t,abs_of_nonneg (t.trans p)]; exact p; exact S.T; exact S.V -- tune
omit P
-- upfront y price b: simple polynomial. combine exp logs per slot.
lemma buyM (S:Gates.Stage c w R v)(L:Side)(a:ℕ):
    ∀ᶠ y:ℝ in atTop, piT (DP L a y) y ≤ y^4 ∧ mCost c R (2*y) (Weights.rent y S.M R w v) (DP L a y) ≤ y^4:=by
 let C'(y:ℝ):=Real.log ((4/xi y)^matDim G); have H:PL C':=by
    unfold C'; simp_rw [Real.log_pow,Real.log_div (four_ne_zero) (coin_pos ..).ne',sub_eq_add_neg]; exact (PL.const _).mul ((PL.const _).add (log_pl .. |>.neg)) -- tune
 let K:ℝ:= (Fintype.card PlaqAxes:ℝ)*(2*(c.direct*2))+ ((Fintype.card Signed:ℝ)*Fintype.card PlaqAxes)*(2*share*((R*2)^2/2)); have hK:0≤K:=by unfold K; have := c.quadratic_pos; have hp:= share_pos; positivity
 filter_upwards [coin_strongLt (a:=1) (b:=0) (by norm_num) H, scale_domain L a, S.uniform.limit.eventually (ge_mem_nhds one_pos), eventually_ge_atTop (4*(K+1)), eventually_ge_atTop (64:ℝ)] with y hv he hk hx hy
 have hl:0<y:=by positivity
 rw [coinY hl] at hv; have hp : (DP L a y:ℝ)+1≤3*y:=by
    have hz:(DP L a y:ℝ) ≤ LP L y:= Nat.cast_le.mpr (by have h:=he.1.2; omega); have h':sizeP y≤ y:=(le_trans (Real.exp_monotone (by nlinarith only [sq_nonneg (Real.log (Real.log y))] : Real.log y*1+Real.log (Real.log y)^2*(-2)+Real.log (Real.log y)*0 ≤ Real.log y)) (Real.exp_log hl).le); linarith only [h',he.2.2.1.upper,hz, hy]
 have hw:0≤K*y+1:=by positivity
 have hi : K+1≤ y:=by linarith
 have hh:y^2≤y^3:= by gcongr; linarith; decide
 refine ⟨?_,?_⟩
 · unfold piT; change C' y * (_:ℝ)≤_; push_cast; nlinarith [mul_le_mul_of_nonneg_right (show C' y≤y from (le_abs_self _).trans hv.le) (show 0≤(DP L a y:ℝ)+1 by positivity)] -- tune
 unfold mCost; have hv' : (Fintype.card PlaqAxes:ℝ)*(2*y*(c.direct*2)) + Fintype.card Signed* (Fintype.card PlaqAxes:ℝ)*(2*y*share*((R*2)^2/2))=K*y:= by unfold K; ring; -- tune
 rw [hv']; apply le_trans (b:=(↑(DP L a y)+1)*(K*y+1)) (mul_le_mul_of_nonneg_left (add_le_add le_rfl hk) (by positivity)); apply le_trans (mul_le_mul_of_nonneg_right hp hw); nlinarith [mul_le_mul_of_nonneg_right hx (sq_nonneg y)]
end YM.CF.BProof.Gates.Stage.Setup
