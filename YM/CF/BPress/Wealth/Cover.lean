import YM.CF.BPress.Wealth.Severe
/-! Eq:B-Sbill and heavy costs regular. Uniform unassigned accounted leftover bill (K and magnetic linear evaluated even at irregular roots). Positive proof requires β prefactor. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(M:ℕ)(R:PathData group)(d:Clip)(p:BudgetPoint)(β y:ℝ)(S:Finset X.Hcols) (w : Directions group s) {σ C Λ:ℝ}(H:R.Bounds d σ C Λ) {κ ζ D:ℝ}(q:Dividend D κ ζ y)
def dueL (ζ C:ℝ) := d.direct*ζ^2/2+ chPrice*(ζ*C)^2/2
def dueK (ζ D C:ℝ):= (d.direct+chPrice) * (ζ+ζ*C) * (coefH 0 C*D)
include H q
lemma bgHigh (u:p.threshold=temp y)(f:0 ≤ β)(i:Root s) : due M R d p β y i ≤ β* dueL d ζ C*mA y^2:=by
 have hz:= q.posC; have ht:= mA_pos q.young; have hc:= d.quadratic_pos; have hC:=budget_nonneg H.three; have hd:= chPrice_pos
 rcases i with i|⟨v,i⟩
 · change hide d _ _ (background y) i ≤ _; unfold hide hideH PathData.clipped; have hp:= q.bgChord s 1 i; rw [faceR,pull_id] at hp; rw [u,if_pos (hp.trans (mA_small q))]; apply le_trans (b:= β * (d.direct*(ζ*mA y)^2/2)) (by gcongr; exact group.chord_nonneg _); unfold dueL; nlinarith only [show 0≤ β*(chPrice*(ζ*C)^2)*mA y^2 by positivity]
 change kept d p R β M v _ i≤ _; unfold kept keepR; split; next t=>
    apply le_trans (b:=chPrice*β*((ζ*mA y*C)^2/2)) _; · unfold dueL; nlinarith only [show 0 ≤ β*d.direct*ζ^2*mA y^2 by positivity]
    gcongr; exact rankBack M v R H q i
 next t=> rw [mul_zero]; unfold dueL; positivity
lemma base_price (i:Root s) : ‖base R M i‖ ≤ ζ+ ζ*C:=by have he:= q.posC; have ht:=budget_nonneg H.three; cases i with|inl i=> exact (q.fixed 1 i.2).trans (le_add_of_nonneg_right (by positivity))|inr v=> exact (baseC M v.1 R H q v.2.2).trans (le_add_of_nonneg_left he.le)
lemma lin_charge (h:∀ x, ‖w x‖ ≤ D*temp y)(u:0<D)(f:0≤ β)(i:Root s): |first R d M β y i w| ≤ β * dueK d ζ D C * (mA y*temp y):=by
 let A:= mA y • base R M i; have hp:= q.posC; have hm:= mA_pos q.young; have ht:= temp_pos q.young; have hv:0≤ C:=budget_nonneg H.three; have hs:= weight_price d i; have hh:= d.quadratic_pos; have hz: ‖A‖≤ mA y*(ζ+ζ*C):=by unfold A; rw [norm_smul, Real.norm_of_nonneg hm.le]; exact mul_le_mul_of_nonneg_left (base_price M R d y H q i) hm.le
 unfold first; rw [abs_mul,abs_of_nonneg (by positivity : 0≤ wgt d i*β)]; apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_right (direct_price d i) f) ((abs_real_inner_le_norm A _).trans (mul_le_mul hz (range_price M R H i w (D*temp y) h) (norm_nonneg _) (by positivity))) (abs_nonneg _) (by positivity [chPrice_pos])); exact Eq.le (by unfold dueK coefH; ring)
-- uniform `Kμ+Lμ` bound o(β*t²), times counted; convenient factor m*t. L declaration kept at p and R.
def stipend (ζ D C:ℝ):= dueL d ζ C+ dueK d ζ D C
omit H q
lemma stipend_pos (ζ D C:ℝ)(h:0 < ζ)(p:0<D)(t:0 ≤ C): 0 < stipend d ζ D C:=by unfold stipend dueL dueK coefH; positivity [d.quadratic_pos,chPrice_pos]
include H q
lemma roots_safe (h:∀ x, ‖w x‖ ≤ D*temp y)(u:0<D)(f:0≤ β)(v:p.threshold=temp y)(x:Root s): due M R d p β y x + first R d M β y x w ≤ β*stipend d ζ D C*(mA y*temp y) :=by
 have hp:=q.posC; have he:=budget_nonneg H.three; have hb:=mA_pos q.young; refine (add_le_add (bgHigh M R d p β y H q v f x) ((le_abs_self _).trans (lin_charge M R d β y w H q h u f x))).trans ?_; unfold stipend; rw [mul_add,add_mul]; apply add_le_add_left; rw [pow_two]; gcongr; unfold dueL; positivity [d.quadratic_pos,chPrice_pos]; exact q.mag -- tune add_left

variable {U V:Micro s}{x : Bills X E}
def severeP (κ:ℝ)(D:ℕ) := κ/(2*D)
def sever (κ:ℝ)(D:ℕ) := loss d (severeP κ D) /2
lemma storm (c:High B M) (z:0<D)(u:0<κ)(f:0≤β)(g:p.threshold=temp y)(t:Mission X y x V U)(P: ToneNoise y V)
 (v:xi y≤ κ*temp y/2)(r:(counted M B.D:ℝ)* stipend d ζ D C*mA y≤sever d κ B.D*temp y)(h:∀ x, ‖w x‖ ≤ D*temp y)(i:X.Hcols)(l:i ∈ chosen X κ y x):
 pays X M R d p β y (chosen X κ y x) w U i ≤ -(sever d κ B.D*β*(temp y)^2):=by
 let S:= chosen X κ y x; let K:=κ/(2*(B.D:ℝ)); have hx:=q.young; have ht:=temp_pos hx; have hc:=q.posC; have hp:=budget_nonneg H.three; obtain ⟨j,e,s'⟩:= billing_vert y t P u hx v i ((marksev ..).1 l); let b:Root s:=.inl (vert X j); let Y:=bookS X M S i; have hk : b∈ Y:= by unfold Y; rw [←e]; exact pays_V S c j (e.symm ▸ l)
 -- positivity of heavy didn't need Checks. formulate
 have hs(x:Root s): 0 ≤ heavy R d p β M x U:=by cases x; exact h_pos d p β _ f U; exact kept_budget d p R β M U _ f _
 let a:= stipend d ζ D C; let T :=temp y; let z':=sever d κ B.D; have hD:(0:ℝ)<B.D:=by exact_mod_cast B.D_pos
 have hK : 0<K:=by unfold K; positivity
 have hy : 2*z'*β*T^2 ≤ heavy R d p β M b U:= by
    change _ ≤ hide d p β U _; unfold hide hideH; rw [g]; have he: K*T≤ _:=s'; apply le_trans _ (mul_le_mul_of_nonneg_left (losses d y _ ((mul_pos hK ht).trans_le he) hx K hK s') f); unfold z' T sever; change 2*(loss d K /2)*_*_≤_; exact Eq.le (by ring)
 unfold pays spent; change ∑ i∈Y, _ ≤ _; rw [sum_sub_distrib]; have hh:= (sum_le_sum (s:=Y) (f:=fun i=>due M R d p β y i + first R d M β y i w) (g:=fun _=>β*a*(mA y*T)) (fun i (_:i∈ Y)=> roots_safe M R d p β y w H q h z f g i)); rw [sum_const,nsmul_eq_mul] at hh
 refine (sub_le_sub (hh.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (book_cost S c i)) (by have hs : 0 < a:=stipend_pos _ _ _ _ hc z hp; positivity [mA_pos q.young,temp_pos q.young]))) (hy.trans (single_le_sum (f:=fun x=>heavy R d p β M x U) (fun x _=> hs x) hk))).trans ?_; change _ ≤ -(z'*β*T^2); have hu: (counted M B.D:ℝ)*a*mA y≤z'*T:=r; nlinarith only [mul_le_mul_of_nonneg_left hu (mul_nonneg f ht.le)] -- tune T implicit
end YM.CF.BPress.Wealth
