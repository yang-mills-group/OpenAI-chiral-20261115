import YM.Gauge.Size
import YM.Gauge.Chart
import YM.LocalH.Chart
import YM.RG.Masks
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function Filter Lattice Gauge MeasureTheory LocalH
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff ENNReal Classical
attribute [local instance] frobInner
variable {G : Gauge}

def chord (u v : G.El) := G.chord (u*v⁻¹)
namespace chord
variable (u v w z : G.El)
lemma mat_eq : chord u v= ‖G.mat u-G.mat v‖/G.colorScale := by
  unfold chord Gauge.chord; rw [G.mat_mul, ← show G.mat v * G.mat v⁻¹=1 from by simp,
    ←sub_mul,frob_mul_eq _ _ (G.mat_mul_star v⁻¹)]; rfl
-- don't use the L2Operator norm in this lemma
lemma scale_mul : G.colorScale * chord u v= ‖G.mat u-G.mat v‖:= by rw [mat_eq,mul_comm, div_mul_cancel₀ _ G.colorScale_pos.ne']
@[simp] lemma refl : chord u u=0:=by simp [chord]
@[simp] lemma one : chord u 1=G.chord u:=by simp [chord]
lemma positive : 0 ≤ chord u v:= G.chord_nonneg _
lemma comm : chord u v=chord v u:=by rw [mat_eq,mat_eq,norm_sub_rev]
lemma triangle : chord u w ≤ chord u v+chord v w:=by rw [mat_eq,mat_eq,mat_eq,←add_div]; exact div_le_div_of_nonneg_right (norm_sub_le_norm_sub_add_norm_sub ..) G.colorScale_pos.le
lemma le_two : chord u v ≤ 2:= G.chord_le_two _
@[simp] lemma inv : chord u⁻¹ v⁻¹=chord u v:=by rw [mat_eq,mat_eq,G.mat_inv,G.mat_inv,←star_sub,norm_star]
@[simp] lemma left : chord (w*u) (w*v)=chord u v:=by rw [mat_eq,mat_eq,G.mat_mul,G.mat_mul,←mul_sub,mul_frob_eq _ _ (G.mat_star_mul w)]
@[simp] lemma right : chord (u*w) (v*w)=chord u v:=by rw [mat_eq,mat_eq,G.mat_mul,G.mat_mul,←sub_mul,frob_mul_eq _ _ (G.mat_mul_star w)]
lemma product : chord (u*w) (v*z)≤chord u v+chord w z:=by simpa using triangle (u*w) (v*w) (v*z)
lemma eq_of_zero (p : chord u v=0) : u=v:= by
  apply G.mat_injective; exact sub_eq_zero.mp (norm_eq_zero.mp (by rw [←scale_mul,p,mul_zero]))
@[fun_prop] lemma cont : Continuous (fun x : G.El × G.El => chord x.1 x.2):=by unfold chord; fun_prop

-- Lie log. Use the FiniteGaugeData chart in color coordinates. Want Lipschitz(a neighborhood),
-- conjugation. In purchases can always take any smaller open chord-ball.
lemma to_ball {S : Set G.El} (h : S∈𝓝 (1:G.El)) : ∃ r : ℝ, 0 < r ∧ G.shell r ⊆ S:=by
 have he : Topology.IsInducing G.mat:= (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.isInducing
 rw [he.nhds_eq_comap,mem_comap] at h
 obtain ⟨W,w,H⟩:= h; obtain ⟨r,p,R⟩:= Metric.mem_nhds_iff.mp w
 refine ⟨(r/2)/G.colorScale, by have e:=G.colorScale_pos; positivity,?_⟩; intro i hi; apply H; apply R;
 have hx:G.chord i ≤ _:=hi; have hu:‖G.mat i-1‖ ≤ r/2:= (div_le_div_iff_of_pos_right G.colorScale_pos).mp hx; rw [Metric.mem_ball, dist_eq_norm, G.mat_one]; linarith

-- face comparisons through on-support links
variable {s : Side} (U V : Wilson.Config G s)
def Close (S : Support s) (r : ℝ) := ∀ e : Edge (Site s), e.1∈S → e.1+step e.2 ∈S → chord (U e) (V e)≤ r
lemma Close.smaller {r : ℝ} {S T : Support s} (h : T ⊆ S) (p : Close U V S r) : Close U V T r:= fun i a b=> p i (h a) (h b)
lemma path (w : Walk) (x : Site s) (r : ℝ) (P : Close U V (visits x w).toFinset r) :
    chord (travel U x w) (travel V x w) ≤ w.length*r:= by
 induction w generalizing x with
 | nil=> simp [travel]
 | cons i w ih=>
   have h: (visits (x+i.vec) w).toFinset⊆ (visits x (i::w)).toFinset:= by rw [visits,List.toFinset_cons]; apply Finset.subset_insert
   refine (product (i.read U x) (i.read V x) (travel U (x+i.vec) w) (travel V (x+i.vec) w)).trans ((add_le_add (show chord _ _ ≤ r from ?_) (ih _ (Close.smaller U V h P))).trans (Eq.le ?_)) -- tune
   · have he:x∈(visits x (i::w)).toFinset:=by simp [visits]
     have ht:x+i.vec∈(visits x (i::w)).toFinset:=h (by cases w <;> simp [visits])
     cases i with | mk j b=>
      cases b
      · exact P (x,j) he ht
      simp only [Step.read, if_true, inv]; exact P (_,j) (by change x-step j∈_; simpa [sub_eq_add_neg,Step.vec] using ht) (by simpa using he)
   simp [add_mul]; ring -- tune
lemma face (p : Face (Per s)) (r : ℝ) (H : Close U V (RG.touched p) r) :
    chord (faceValue U p) (faceValue V p) ≤ 4*r:=by
  refine (path U V (square ..) p.1 r H).trans_eq ?_; norm_cast -- tune

-- Use closed-ball densities (equalities included, as licensed in VolumeB).
def charge (G : Gauge) (r : ℝ) := (G.probHaar.real (G.shell r))⁻¹
def ballDensity (r : ℝ) (o x : G.El) := if chord x o≤r then charge G r else 0
lemma charge_pos {r : ℝ} (h : 0<r) (p : r≤1) : 0< charge G r:= inv_pos.mpr ((pow_pos (show 0<r/4 by positivity) _).trans_le (G.shell_ge r h p))
lemma charge_high {r : ℝ} (h : 0<r) (p : r≤1) : 1 ≤ charge G r:= by
 have ht:=charge_pos (G:=G) h p; unfold charge at *; apply (one_le_inv₀ _).mpr ((measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ); exact inv_pos.mp ht
lemma density_meas (r : ℝ) : Measurable (fun x : G.El × G.El => ballDensity r x.1 x.2):= by
 let S := {x:G.El × G.El| chord x.2 x.1 ≤ r}
 have h : MeasurableSet S:= (isClosed_le ((cont (G:=G)).comp continuous_swap) continuous_const).measurableSet
 exact (Measurable.ite h measurable_const measurable_const) -- tune
lemma bound (r : ℝ) : |ballDensity r u v|≤charge G r:=by unfold ballDensity; have h:0≤ charge G r:=inv_nonneg.mpr measureReal_nonneg; split <;> simp [abs_of_nonneg h,h]
lemma density_nonneg (r : ℝ) : 0≤ballDensity r u v:=by unfold ballDensity; split; exact inv_nonneg.mpr measureReal_nonneg; rfl
lemma density_ne (r : ℝ) (p : ballDensity r u v≠0) : chord v u ≤ r:=by contrapose! p; rw [ballDensity,if_neg (not_le.mpr p)]
lemma density_integral {r : ℝ} (p : 0<r) (q : r≤1) : ∫ v, ballDensity r u v ∂G.probHaar=1:=by
 let S := (fun x:G.El => x*u⁻¹) ⁻¹' G.shell r
 have hb : MeasurableSet S:= measurable_mul_const u⁻¹ (G.shell_meas r)
 have he : G.probHaar.real S=G.probHaar.real (G.shell r):=congrArg ENNReal.toReal ((measurePreserving_mul_right G.probHaar u⁻¹).measure_preimage (G.shell_meas r).nullMeasurableSet)
 have hy : ballDensity r u=S.indicator (fun _=> charge G r):=by ext x; by_cases h:x ∈ S; rw [Set.indicator_of_mem h]; exact if_pos h; rw [Set.indicator_of_notMem h]; exact if_neg h
 rw [hy, integral_indicator hb,setIntegral_const,smul_eq_mul,he,charge,mul_inv_cancel₀ (inv_pos.mp (charge_pos p q)).ne']
end chord
end YM.CF.BPress
