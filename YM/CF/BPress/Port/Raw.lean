import YM.CF.BPress.Port.Ribbon
/-! Raw-bad; reject even before frame data, and reach local rule after mixing. `eq:B-Sbill2` wrapper later. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Branch Metric
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal ContDiff
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(J: ChartRatio group)(P:Weave.Budget)(κ y:ℝ)
def rawBad (S:Seal X.Hcols)(x:Fills X)(i:X.Hcols) := i∈ S ∨ heigh y ≤ ‖x i‖
def destiny (F:Fare X)(S:Seal X.Hcols)(v:Quarters X)(i:X.Hcols) := i∈ S ↔ checked X κ y i (bodyBase X y F S v i)
lemma light_eq (F:Fare X)(S:Seal X.Hcols)(v:Quarters X): aware X κ y F S v ↔ ∀ i,destiny X κ y F S v i:=by unfold aware destiny; nth_rw 1 [eq_comm]; rw [Finset.ext_iff]; simp only [pick_eq]
private lemma exp_fare1 : ∃ K:ℝ, 0<K∧ ∀ x:ink, ‖x‖≤1→group.chord (group.lieExp x)≤ K*‖x‖:=by
 obtain ⟨K,h⟩:= chord.exp_lip group 1; refine ⟨ K/group.colorScale+1,by have ht:=group.colorScale_pos; positivity, fun x hx=>?_⟩; have ht:= h.dist_le_mul x (show x∈closedBall 0 1 from (by simpa)) 0 (mem_closedBall_self (by norm_num)); simp only [chord.emb,dist_eq_norm,mat_lieExp_zero,sub_zero] at ht; unfold Gauge.chord; refine (div_le_div_of_nonneg_right ht group.colorScale_pos.le).trans ?_; rw [mul_div_right_comm]; gcongr; exact le_add_of_nonneg_right zero_le_one
structure CheckWind (K:ℝ): Prop where
 hK : 0<K
 young: 0<y
 law(x:ink): ‖x‖≤1→group.chord (group.lieExp x)≤ K*‖x‖
 adult : strideCost D P (heigh y) y ≤ 1
 cap : K* strideCost D P (heigh y) y≤ wc y
 convert : wc y ≤ κ*temp y
lemma check_buy (t:0<κ): ∃ K:ℝ, ∀ᶠ i in atTop, CheckWind D P κ i K:=by
 obtain ⟨K,k,h⟩:= exp_fare1; have hp:= npl_wc; have hd: NPL fun i=> strideCost D P (heigh i) i / wc i:=by
   have he:= ((P.buy_for D).times (npl_power heigh_npl 3 (by norm_num))).const_mul (faith D); refine npl_congr ?_ he; filter_upwards [eventually_gt_atTop (0:ℝ)] with i pi; unfold strideCost; rw [root_price pi,wc_price pi]; field_simp [ (root_pos pi).ne', (heigh_pos i).ne']<;> ring
 have hf: NPL fun i=>wc i/temp i:= npl_congr (F:=fun i=>(heigh i)⁻¹^4) (by
   filter_upwards [eventually_gt_atTop (0:ℝ)] with i p; rw [wc_price p,temp_price p]; field_simp [(root_pos p).ne',(heigh_pos i).ne']<;> ring) (npl_power heigh_npl 4 (by decide))
 refine ⟨K,?_⟩; filter_upwards [hp.drop.eventually (ge_mem_nhds k), hd.drop.eventually (ge_mem_nhds (inv_pos.mpr k)), hf.drop.eventually (ge_mem_nhds t),eventually_gt_atTop (0:ℝ)] with i a b c p; have ht: 0 < wc i:=by rw [wc_price p]; positivity [root_pos p,heigh_pos i]
 have hu:temp i>0:=temp_pos p; let V:= strideCost D P (heigh i) i; have he:V≤K⁻¹ * wc i := (div_le_iff₀ ht).mp b; have hV: K*V≤wc i:= by apply le_trans (mul_le_mul_of_nonneg_left he k.le); field_simp; rfl
 refine ⟨k,p,h, le_of_mul_le_mul_left (by rw [mul_one]; exact hV.trans a) k,hV,(div_le_iff₀ hu).mp c⟩
variable {P X κ y}{F:Fare X}
namespace CheckWind
variable {K:ℝ}(t:CheckWind B.D P κ y K)(H:Summer X F P.upper (P.low y) (P.reach y) (P.chunks y))(S:Seal X.Hcols)(v:Quarters X)(i:X.Hcols)(p:∀ j∈columnBall X i (P.reach y),¬ rawBad X y S v.1 j)
include H t p
lemma open_gate : i∉ S ∧ (∀ j, chord (bodyBase X y F S v i j) (bMag B.D y j) ≤ wc y) ∧ destiny X κ y F S v i:=by
 let h(j:X.Hcols)(q):= not_or.mp (p j q); have he(φ:Hub B.D): chord (bodyBase X y F S v i φ) (bMag B.D y φ)≤ wc y:=by
   unfold bodyBase issueT; rw [if_neg (h i (column_self ..)).1]; let v':= hew B.D y (wjson (F S) v.1 i) φ; change chord (bMag B.D y φ * group.lieExp v') (bMag B.D y φ)≤_; nth_rw 2 [←mul_one (bMag B.D y φ)]; rw [chord.left,chord.one]; have hv:‖v'‖≤ strideCost B.D P (heigh y) y:= stride_s H t.young v.1 i (heigh_pos y).le (fun i h'=> le_of_not_ge (h i h').2) φ; exact (t.law _ (hv.trans t.adult)).trans ((mul_le_mul_of_nonneg_left hv t.hK.le).trans t.cap)
 have hp: i∉ S:= (h i (column_self ..)).1; refine ⟨hp,he,iff_of_false hp ?_⟩; rintro ⟨j,h⟩; exact h.not_ge ((he j).trans t.convert)
end CheckWind
lemma body_reads {r:ℕ}(p:Connect X F r)(S T:Seal X.Hcols)(x y':Quarters X)(i:X.Hcols)(q:state (columnBall X i r) S T)(Y:∀ j∈columnBall X i r, x.1 j=y'.1 j)(t:x.2 i=y'.2 i) : bodyBase X y F S x i=bodyBase X y F T y' i:=by unfold bodyBase issueT; have l:=q i (column_self ..); rw [see_run p S T i q x.1 y'.1 Y,t]; simp only [l]
end YM.CF.BPress.Port
