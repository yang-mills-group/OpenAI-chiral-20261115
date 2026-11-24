import YM.CF.BPress.Port.Sailing
/-! per-column short weak terms estimates. Read-set prices on micro columns and arranged later on $Λ$ (and solve global requirements later). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Branch
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(J:ChartRatio group)(F A:Fare X)
-- bookkeeping per angular block and v issues
lemma offer_pair (v w:RaySpace X): inner ℝ v w = ∑ i, inner ℝ (offer X v i) (offer X w i):=by
 rw [PiLp.inner_apply]; simp_rw [PiLp.inner_apply]; rw [← Fintype.sum_prod_type (f:=fun (i:X.Hcols × Stack B.D)=> inner ℝ (offer X v i.1 i.2) (offer X w i.1 i.2))]; -- tune
 exact (Fintype.sum_equiv (stem X) _ _ (fun i=>by rw [stem_expr]; change _=inner ℝ _ _; rw [← offer_hit X v i,←offer_hit X w i]; rfl))
def rTerm (x:Fills X)(S:Seal X.Hcols)(i:X.Hcols) := inner ℝ (x i) (wjson (errorT X (A S) (F S)) x i)/2
lemma Rterms (S:Seal X.Hcols)(x:Fills X): Rcoord X (A S) F S x=∑ i,rTerm X F A x S i:=by
 let v:=(offer X).symm x; unfold Rcoord; dsimp only; rw [offer_pair,Finset.sum_div]; simp only [MeasurableEquiv.apply_symm_apply]; rfl
lemma rT_meas (S:Seal X.Hcols)(i:X.Hcols) : Measurable (fun x=>rTerm X F A x S i):= (((Continuous.measurable (continuous_inner (𝕜:=ℝ))).comp ((measurable_pi_apply i).prodMk ((measurable_pi_apply i).comp (wjson_meas _))))).div_const _ -- tune namespace
variable {X}
def Wander (r m:ℕ):= (r+m)+r
def errAt (S:Seal X.Hcols):=errorT X (A S) (F S)
variable {F A}
lemma err_seen {r m:ℕ}(p:Connect X A m)(v:Connect X F r): Connect X (errAt F A) (Wander r m):= Connect.one.sub ((v.walk p).walk v)
def smallRead (v:Fills X→Seal X.Hcols→ X.Hcols→ℝ) (r:ℕ): Prop:= ∀ u V S T i, let L:=columnBall X i r; state L S T→(∀ j∈L,u j= V j)→v u S i=v V T i
lemma rTerm_loc {r m:ℕ}(p:Connect X A m)(v:Connect X F r): smallRead (rTerm X F A) (Wander r m):=by
 intro u V S T i L e g; unfold rTerm; have ht:=see_run (F:=errAt F A) (err_seen p v) _ _ i e u V g; unfold errAt at ht; rw [ht,g _ (column_self ..)] -- tune

def rMaxV (D r:ℕ)(y:ℝ):=truncv y* (faith D*( (n_ang D*taxArea r*y⁻¹^2)*(truncv y)))/2
lemma rMax_paid (y:ℝ){r m:ℕ}(p:Connect X A m)(v:Connect X F r)(S:Seal X.Hcols)(t:‖errorT X (A S) (F S)‖ ≤ y⁻¹^2) (x:Fills X)(i:X.Hcols)(h:Barrel X y x) : |rTerm X F A x S i| ≤ rMaxV B.D (Wander r m) y:=by
 let W:= Wander r m; let C:= (n_ang B.D:ℝ)* taxArea W *y⁻¹^2; let L:=errAt F A
 have he: ∀ i,∑ j, |rowM X (L S) i j| ≤ C:=by
   intro i; let V:=coverPrice X (columnBall X (zSite X i) W); rw [←sum_subset (Finset.subset_univ V)]; swap
   · intro j _ v'; exact abs_eq_zero.mpr <| (err_seen p v).reaches S i j (fun v=> v' (mem_filter.mpr ⟨mem_univ j,v⟩))
   have h':V.card≤ n_ang B.D* taxArea W:=(cover_count X _).le.trans (Nat.mul_le_mul_left _ (cost_bay X _ _)); apply le_trans (sum_le_sum (g:=fun _=> y⁻¹^2) ?_) ?_
   · intro j _; exact (entry_cap X _ i j).trans t
   rw [sum_const,nsmul_eq_mul]; refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h') (sq_nonneg _)) (Eq.le ?_); unfold C; rw [Nat.cast_mul]
 let d:=truncv y; have hd:0 ≤ d:= zero_le_one.trans (trunc_pos _); have hp:‖wjson (L S) x i‖ ≤ faith B.D*(C*d):= ray_mobile _ _ _ _ _ he (fun j _ l _=>by rw [offer_symm]; exact (point_cost ..).trans (h _)) hd (by unfold C; positivity); unfold rTerm rMaxV; rw [abs_div,abs_of_pos (show (0:ℝ)<2 from zero_lt_two)]; exact div_le_div_of_nonneg_right ((abs_real_inner_le_norm ..).trans (mul_le_mul (h i) hp (norm_nonneg _) hd)) zero_le_two -- tune
lemma tax_arg (D:ℕ)(r:ℝ→ℕ)(p:PL fun i=>(r i:ℝ)) : NPL fun i=> rMaxV D (r i) i:=by
 have he:= npl_drift_g 4 4 (by norm_num); have hz : PL (fun i:ℝ=>faith D * n_ang D * taxArea (r i) * (1/2)):= (PL.mul ((PL.const _).mul (show PL fun i=>(taxArea (r i):ℝ) from (by simpa only [grassRate,inv_inv] using gr_PL r p))) (PL.const _)); refine npl_congr ((eventually_gt_atTop (0:ℝ)).mono (fun i p=>?_)) (hz.times he); unfold rMaxV truncv; rw [←gscale p.le]; norm_num; ring -- tune
end YM.CF.BPress.Port
