import YM.SU5.Relativistic.Disappear

/-! Vanishing of averaged obstruction
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Finset Set Filter Metric MeasureTheory
open MeshClock Germ Vacancy _root_.YM.SelectionAnalysis
open scoped Topology Classical BigOperators NNReal ENNReal InnerProductSpace
section subcubes
variable {I : Type*}[Fintype I](M:Mesh)
local notation "L"=> M.L
local notation "Q" s:max=> (I→ Fin (M.L^s))
local notation "N" t:max k:max=> notch M t k

noncomputable def boxBetween (s k:ℕ): ((I→Fin (M.L^s)) ×(I→ Fin (M.L^k))) ≃ (I→ Fin (M.L^(s+k))) := (Equiv.arrowProdEquivProdArrow I (fun _=> Fin (M.L^s)) (fun _=> Fin (M.L^k))).symm.trans
    (Equiv.piCongrRight (fun _=> finProdFinEquiv.trans (finCongr (pow_add ..).symm)))
lemma between_val (s k:ℕ)(x:Q s)(y:Q k)(i:I) : (boxBetween M s k (x,y) i).val=(y i).val+ M.L^k*(x i).val:=rfl
lemma within_val (s k:ℕ)(x:Q s)(y:Q k)(i:I): smallCorner (L^(s+k)) (boxBetween M s k (x,y)) i = smallCorner (L^s) x i + (smallCorner (L^k) y i)/(L^s:ℕ):=by
 unfold smallCorner; rw [between_val, Nat.cast_pow,Nat.cast_add,Nat.cast_mul,pow_add]; push_cast;
 have h:0 < (L:ℝ):= by exact_mod_cast (show 0<L from lt_of_lt_of_le (by decide) M.Llarge)
 field_simp; ring
lemma withinCon (s k:ℕ)(x:Q s)(y:Q k): smallCorner (L^(s+k)) (boxBetween M s k (x,y))∈ nearBox (L^s) x:= by
 intro i _
 change smallCorner _ _ _ ≤ smallCorner _ _ _ ∧ smallCorner _ _ _ < bigCorner _ _ _
 rw [within_val]
 have hi:= (nearBox_inside (L^k) (avg_num M k) y (corner_in_box _ (avg_num M k) y)) i (Set.mem_univ _)
 constructor
 · exact le_add_of_nonneg_right (by exact div_nonneg hi.1 (by positivity))
 have hx: (smallCorner (L^k) y i / ((L^s:ℕ):ℝ)) < ((L^s:ℕ):ℝ)⁻¹:=(div_lt_div_of_pos_right hi.2 (show 0<((L^s:ℕ):ℝ) from by exact_mod_cast avg_num M s)).trans_eq (one_div _)
 linarith only [spans (L^s) (avg_num M s) x i,hx]
end subcubes
section average
variable {I K:Type*}[Fintype I]{H:Hilbert}(M:Mesh)(P:Alliance K (marks M) H)(e:K→I)
local notation "L"=> M.L
local notation "Q" t:max => (I→ Fin (M.L^t))
local notation "N" t:max k:max=> notch M t k
local notation "U" t:max=> P.raw t
variable (F:(I→ℝ)→H)(l:List K)(n:ℕ)(u:K→Stamp M)
local notation "π"=> P.stackS l
local notation "D" t:max f:max=> fun k:K=> u k+notch M (n+t) ((f (e k)).val:ℤ)
local notation "V" t:max i:max=> smallCorner (M.L^t) i
local notation "f" t:max i:max=> F (V t i)
lemma variable_gap (p:ContinuousOn F (UBox I))(t:l.Nodup) (h:Injective e) :
    Tendsto (fun i:ℕ=> Average.center (fun x: Q i=> P.raw l (D i x) ((f i x)-π (f i x)))) atTop (𝓝 0):=by
 let G(z:I→ℝ):= F z- π (F z); have hp:ContinuousOn G (UBox I):=p.sub ((π).continuous.comp_continuousOn p)
 apply Metric.tendsto_nhds.mpr
 intro ε hv; let R:= ε/2
 obtain ⟨d,hd,a⟩:= Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hp) R (half_pos hv)
 obtain ⟨s,(hs:((L^s:ℕ):ℝ)⁻¹<d)⟩:= (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt (show 1<L from lt_of_lt_of_le (by decide) M.Llarge)))).eventually (gt_mem_nhds hd)|>.exists -- type ℕ tune
 let X:=(Q s); haveI:Nonempty X:=by haveI:=avg_lives M s; change Nonempty (I→ Fin _); infer_instance
 let A(k:ℕ)(x:X):H:= Average.center (fun y: Q k=> P.raw l (D (s+k) (boxBetween M s k (x,y))) (G (smallCorner _ x)))
 have ha(x:X): Tendsto (fun k:ℕ=>A k x) atTop (𝓝 0):=by
    let b:=D s x
    have hy(k:ℕ)(y:Q k): (D (s+k) (boxBetween M s k (x,y)))= (b+(fun i:K=> N (n+s+k) (((y (e i)).val:ℤ)))):=by
       funext i
       simp only [Pi.add_apply,b]; rw [add_assoc, Nat.add_assoc n s k,SelectionAnalysis.transmit M n s k]; rfl
    unfold A; simp_rw [hy]
    exact constant_gap M P e l t h b (F _) (n+s)
 have ht:Tendsto (fun k=>Average.center (A k)) atTop (𝓝 0):=by
    have hi:=tendsto_finsetSum (Finset.univ:Finset X) (fun i _=> ha i)
    unfold Average.center; simpa using hi.const_smul ((Fintype.card X:ℂ)⁻¹)
 obtain ⟨j,hj⟩:=eventually_atTop.mp (Metric.tendsto_nhds.mp ht R (half_pos hv))
 filter_upwards [eventually_ge_atTop (s+j)] with m h
 obtain ⟨k,rfl⟩:= Nat.exists_eq_add_of_le (show s≤m by omega); specialize hj k (by omega)
 change dist (Average.center (fun x: Q (s+k)=> P.raw l (D (s+k) x) (G (smallCorner _ x)))) 0< _
 rw [← Average.trade (boxBetween M s k),Average.domino]
 apply lt_of_le_of_lt (dist_triangle _ (Average.center (A k)) _); refine (add_lt_add_of_le_of_lt ?_ hj).trans_eq (add_halves ε)
 apply Average.norm_dist; intro x
 haveI : Nonempty (Q k):=by haveI:=avg_lives M k; change Nonempty (I→ Fin _); infer_instance
 apply Average.norm_dist
 intro y; rw [dist_eq_norm,←map_sub,raw_norm,←dist_eq_norm,dist_comm]; have he:= withinCon M s k x y
 let Z:= halfBox (nearBox_inside _ (avg_num M s) x (corner_in_box _ (avg_num M s) x))
 exact (a _ Z _ (halfBox (nearBox_inside _ (avg_num M s) x he)) ((nearBox_small _ (avg_num M s) x he).trans_lt hs)).le
end average
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.variable_gap
