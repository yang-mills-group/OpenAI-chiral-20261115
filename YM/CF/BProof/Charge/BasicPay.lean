import YM.CF.BProof.Charge.Ferry

/-! Loss in severe bill uses substitution on severe columns, hence no bound on log there. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge.Form
open Function Filter RG Wilson Lattice Finset Work Micro Moment MeasureTheory Mag Angular Angular.Yard AnalyticBridge.SectorAffine -- root clashes
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {s:Side} (K:Chart G)(M:ℕ)(T:PathData G)(c:Clip)(p:BudgetPoint)(l:Tile s)(β y:ℝ){w C P D:ℝ}
def fixed₀ := 1+∑ σ:Signed,∑ i:PlaqAxes, ‖mark σ i‖
lemma fixed_pos :0<fixed₀:=by unfold fixed₀; positivity
lemma mark_bound (σ:Signed)(i:PlaqAxes) : ‖mark σ i‖ ≤ fixed₀:= le_trans ((single_le_sum (f:=fun i=>‖mark σ i‖) (fun _ _=> norm_nonneg _) (mem_univ i)).trans (single_le_sum (f:=fun σ: Signed=>∑ i:PlaqAxes,‖mark σ i‖) (fun _ _=> Finset.sum_nonneg (fun _ _=>norm_nonneg _)) (mem_univ σ))) (by unfold fixed₀; simp)
def hull (P:ℝ):= (P+1)*fixed₀
lemma hull_pos (p:0≤ P) : 0<hull P:=mul_pos (by linarith) fixed_pos
variable (k:Ink K C y)(u:T.Bounds c w P D)(hc:p.threshold=thresh y)(hb:0≤β)(ht:thin C y≤ mA y)
include u
lemma grouped_fee (a:Lam s) (f: Slot → Lie) {v:ℝ} (hp:0≤v)(h:∀ i∈Stack.allShort M,‖f i‖≤v): ‖∑ i∈Stack.allShort M, coeff T a.2.1 i • f i‖≤P*v:= by
 apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right (grouped_cost c T M u a.2.1) hp); rw [sum_mul]; exact sum_le_sum fun i hx=> (norm_smul ..).trans_le (mul_le_mul_of_nonneg_left (h i hx) (norm_nonneg (coeff ..)))
lemma root_p : ‖root T M l‖≤ hull P:=by
 have hv:=Push.AbsoluteSums.budget_nonneg u.three; cases l with
 | inl l=> exact le_trans (mark_bound 1 l.2) (le_mul_of_one_le_left fixed_pos.le (by linarith))
 | inr l=> exact (grouped_fee M T c u l (fun i=>mark l.1 i.plaq) fixed_pos.le (fun i _=> mark_bound l.1 i.plaq)).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) fixed_pos.le)

lemma line_p (W:Argument s) (U:ℝ)(h:∀ i,‖W i‖≤U): ‖linear T M l W‖ ≤ (P+1)*(4*U):=by
 have hu:0≤U:=le_trans (norm_nonneg _) (h (vert 0 0)) -- tune type
 have hP:= Push.AbsoluteSums.budget_nonneg u.four
 have H(σ: Signed)(l:Cell s): ‖curlP σ l W‖≤4*U:=by
   have hv(b:Bond s): ‖Form.part σ b W‖ ≤U:= (turn_size ..).trans_le (h (sendEdge σ 0 b)); rw [curl_px]; refine (norm_sub_le ..).trans ((add_le_add ((norm_sub_le ..).trans (add_le_add (norm_add_le ..) le_rfl)) le_rfl).trans ?_); linarith only [hv (positions l 0),hv (positions l 1),hv (positions l 2),hv (positions l 3)]
 cases l with
 | inl l=> exact le_trans (H 1 l) (le_mul_of_one_le_left (by positivity) (by linarith))
 | inr l=> change ‖ray T M l W‖≤ _; rw [rays]; apply le_trans (grouped_fee _ T c u l _ (by positivity : 0≤4*U) (fun i hi=>H ..)); exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

include k ht
abbrev bard (P y:ℝ) := (P+1)*((fixed₀+1)*mA y)
private lemma fog (σ: Signed)(a:Cell s) : SU.group.chord (faceValue (lRead σ (mag y)) a) ≤ (fixed₀+1)*mA y:=by
 have g:= expense (k.draw σ a.2); rw [fixed_face]; rw [cd_one,norm_smul, Real.norm_of_nonneg (coin_pos ..).le] at g; have hp:=mark_bound σ a.2; change |_ - mA y*‖mark σ a.2‖|≤_ at g; linarith [(abs_le.mp g).2,mul_le_mul_of_nonneg_left hp (show 0≤mA y from (coin_pos ..).le)]
lemma basic_p : value T M (mag y) l ≤ bard P y:=by
 have hv:=Push.AbsoluteSums.budget_nonneg u.four; have hg:0≤(fixed₀+1)*mA y:=by have := fixed_pos; have hx:0<mA y:=coin_pos ..; positivity
 cases l with
 | inl l=>
   have he:=fog K T c y k u ht 1 l -- tune includes
   unfold lRead at he; rw [pull_id] at he; exact he.trans (le_mul_of_one_le_left hg (by linarith))
 | inr l=>
   let U:=lRead l.1 (mag (s:=s) y); change ‖Pressure.shorten T M 1 U (ref l)‖≤_
   rw [shorten_data c T M _ u]; refine le_trans (grouped_fee _ T c u l (fun i=> i.atSite U _) hg (fun i h=>?_)) (mul_le_mul_of_nonneg_right (by linarith) hg)
   rw [F03.atSite_path,Gauge.norm_adjoint]; exact (SU.group.curvature_norm _).trans (fog K T c y k u ht l.1 _) -- tune
omit k ht u
include hb
lemma unit_p : 0≤ unit c β l ∧ unit c β l≤ β*(c.direct+share):=by
 unfold unit; have he:= share_pos; have hx:=c.quadratic_pos; cases l <;> dsimp only [Sum.elim_inl,Sum.elim_inr] <;> constructor <;> nlinarith
include u
lemma L_pay (W:Argument s)(h:∀ i, ‖W i‖≤ thresh y): |L T M c β y l W| ≤ β*(c.direct+share)*(mA y*hull P *((P+1)*(4*thresh y))):=by unfold L; obtain ⟨ht,v⟩:= unit_p c l β hb; rw [abs_mul,abs_of_nonneg ht]; refine mul_le_mul v (le_trans (abs_real_inner_le_norm ..) ?_) (abs_nonneg _) (ht.trans v); rw [norm_smul,Real.norm_of_nonneg (coin_pos ..).le]; have h0:=root_p M T c l u; exact mul_le_mul (mul_le_mul_of_nonneg_left h0 (coin_pos ..).le) (line_p M T c l u W _ h) (norm_nonneg _) (by have hp:= hull_pos (Push.AbsoluteSums.budget_nonneg u.three); have :=coin_pos y (-1/2) (3/4) 0; unfold mA; positivity)
include k ht hc
lemma cloud_p (e:ValidR c p M): sound y c p T M β l ≤ β*(c.direct+share)*((bard P y)^2/2):=by obtain ⟨hu,hb',q,h'⟩:= issue K y (0:Argument s) c p T M (mag y) k hc e u l (lamp0 ..) β hb; unfold sound; rw [q]; have hv:=basic_p K M T c l y k u ht; refine mul_le_mul (unit_p c l β hb).2 (by gcongr) (by positivity) (le_trans hu (unit_p c l β hb).2)
end YM.CF.BProof.Charge.Form
