import YM.CF.Pic.Firm
import YM.CF.BPress.Chord
/- Link distances: on B-op's Spin stages sum chords (avoids hypotheses exchanging the two
 representations), makes A inputs Bkg. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter Finset Lattice SU Lat Fock Cube Branch Tulip Tenant Scroll
open scoped Topology BigOperators InnerProductSpace
section C
open scoped Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
lemma curv_diff (u v: E): ‖group.curvature u-group.curvature v‖ ≤ chord u v:=by
 unfold Gauge.curvature; rw [← map_sub, ← smul_sub,sub_sub_sub_comm]; apply (group.project_norm _).trans; rw [norm_smul, Real.norm_of_nonneg (by positivity), chord.mat_eq, Gauge.mat_inv, Gauge.mat_inv,←star_sub]
 let a:= group.mat u-group.mat v; change (1/2:ℝ)*‖a-star a‖/group.colorScale≤_; apply div_le_div_of_nonneg_right _ group.colorScale_pos.le; have he:= norm_sub_le a (star a); rw [norm_star] at he; change 1/2 * _ ≤ ‖a‖; linarith
-- small-import variant Nova/Era
lemma boundedFrame:∃ C:ℝ,0<C∧∀ u:E,∀ i j, ‖fund u i j-(1: Op SU.F) i j‖ ≤ C * SU.group.chord u:=by
 refine ⟨Real.sqrt SU.group.repDim,SU.group.colorScale_pos,fun u i j=>?_⟩; unfold Gauge.chord; rw [mul_div_cancel₀ _ (show Real.sqrt (↑SU.group.repDim:ℝ) ≠ 0 from SU.group.colorScale_pos.ne')]; -- tune
 let A:=fund u-1; change ‖A i j‖ ≤ ‖A‖; apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1; rw [Gauge.frob_sq]
 have he: (A*star A).trace.re= ∑ i:SU.F,∑ j:SU.F,‖A i j‖^2:=by unfold Matrix.trace; simp only [Complex.re_sum,Matrix.diag_apply,Matrix.mul_apply]; apply sum_congr rfl; intro i _; exact sum_congr rfl fun j _=> inner_self_eq_norm_sq (𝕜:=ℂ) (A i j) -- tune
 rw [he]; exact le_trans (single_le_sum (f:=fun j=> ‖A i j‖^2) (fun j _=>sq_nonneg _) (mem_univ _)) (single_le_sum (f:=fun i=>∑ j, ‖A i j‖^2) (fun i _=> sum_nonneg fun _ _=>sq_nonneg _) (mem_univ _))
end C
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

structure OrbRate (C:ℝ) : Prop where
 positive : 0<C
 bot (u v:E) : ‖(matter u).val-(matter v).val‖≤ C* chord u v
 top (u v:E) : ‖fund u-fund v‖≤ C*chord u v
 con (u:E) : group.chord u≤ C*‖fund u-1‖
lemma op_chord : ∃ C:ℝ,0<C∧∀ a b:E,Cube.cmp firstF a b≤ C*chord a b:=by
 obtain ⟨C,h,H⟩:= boundedFrame
 refine ⟨5*C,mul_pos (by norm_num) h,fun a b=>?_⟩; unfold chord; rw [←cmp_right firstF a b b⁻¹,mul_inv_cancel]; let y:=a*b⁻¹
 refine (le_trans (b:=Fintype.card SU.F*(C*group.chord y)) (Sods.cost_D (E:=SU.F) _ (H y) (mul_nonneg h.le (group.chord_nonneg _))) (le_of_eq (by simp [F]; ring)))
theorem orbital : ∃ C, OrbRate C:=by
 obtain ⟨C,h,H⟩:= op_chord; obtain ⟨A,a,L⟩:=Pic.gulf; obtain ⟨b,p,Q⟩:=Pic.zeta; refine ⟨max (A*C) b,⟨lt_max_of_lt_right p,fun u v=>?_,fun u v=>?_,fun u=>?_⟩⟩
 · exact (L u v).trans ((mul_le_mul_of_nonneg_left (H u v) (zero_le_one.trans a)).trans ((mul_assoc ..).symm.le.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (chord.positive ..))))
 · exact (H u v).trans (mul_le_mul_of_nonneg_right ((le_mul_of_one_le_left h.le a).trans (le_max_left ..)) (chord.positive ..))
 exact (Q u _ (fun i j=>norm_entry (fund u-1) i j)).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
variable {C:ℝ}
def sphereRate:= orbital.choose
lemma sphereRate_cost : OrbRate sphereRate := orbital.choose_spec

variable {N:Side}(S : Seal (Site N))(U V:Bkg N)
def invitation:= ∑ i∈leaks S,chord (U i) (V i)
namespace invitation
variable {U V S}
lemma positive : 0 ≤ invitation S U V:= sum_nonneg fun _ _=> chord.positive ..
lemma mono {T}(p:S⊆ T) : invitation S U V≤ invitation T U V:= by
 refine sum_le_sum_of_subset_of_nonneg (fun i hi=> mem_filter.mpr ⟨mem_univ _,p (mem_filter.mp hi).2.1,p (mem_filter.mp hi).2.2⟩) (fun _ _ _=>chord.positive ..)
lemma test (i : Edge (Site N))(l:i∈leaks S):chord (U i) (V i)≤ invitation S U V:= single_le_sum (f:=fun i=> chord (U i) (V i)) (fun _ _=> chord.positive ..) l
lemma near : chord.Close U V S (invitation S U V):= fun i p q=> test _ (mem_filter.mpr ⟨mem_univ _,p,q⟩)
lemma follows {T}(s:T⊆ S) : chord.Close U V T (invitation S U V):= chord.Close.smaller U V s near
lemma agrees (h:∀ i∈leaks S,U i=V i): invitation S U V=0:= sum_eq_zero fun i hi=> by rw [h i hi, chord.refl]
lemma iso (f g:Bkg N)(t:Site N→ E) : invitation S (gauge t f) (gauge t g)= invitation S f g:= sum_congr rfl fun ⟨i,j⟩ _=>by unfold Lattice.gauge; rw [chord.right,chord.left]
lemma size {r:ℝ}(f:0≤r)(p:chord.Close U V S r): invitation S U V ≤ 4*S.card*r:=by
 refine (sum_le_sum (fun i hi=>p i (mem_filter.mp hi).2.1 (mem_filter.mp hi).2.2)).trans ?_
 rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ f; have he : (leaks S).card≤ (S×ˢ (univ:Finset Axis)).card:=card_le_card fun i hi=> mem_product.mpr ⟨(mem_filter.mp hi).2.1,mem_univ _⟩
 simp only [card_product, card_univ,Axis,Fintype.card_fin] at he; rw [mul_comm (4:ℝ)]; exact_mod_cast he
lemma forum_compare (h:OrbRate C): fare S (profile U) (profile V) ≤ C*invitation S U V:=by
 unfold invitation fare; rw [mul_sum]; refine sum_le_sum ?_; intro i _; let c:=C*chord (U i) (V i); have hc:0≤c:=mul_nonneg h.positive.le (chord.positive ..); have hu : ‖brand (U i)-brand (V i)‖ ≤ c:=by rw [Prod.norm_def]; exact max_le (h.bot ..) (h.top ..)
 apply (pi_norm_le_iff_of_nonneg hc).mpr; intro j; cases j; exact (by change ‖star _-star (brand _)‖≤_; rw [←star_sub,norm_star]; exact hu); exact hu
lemma gauge_uniform (h:OrbRate C)(k:ℕ)(p:2*k+2<N.val)(d:ℝ)(q:0≤d)(f:Guard U d)(x:Site N) : chord.Close (gauge (hue U x) U) 1 (bay (terr N) x k) (C*priceF k d):=by
 rintro ⟨i,j⟩ y z; let g:= gauge (hue U x) U; let u:=g (i,j); have hp:= gauge_light x i j k y z p U d q f
 rw [Prod.norm_def] at hp; change chord u 1 ≤ _; rw [chord.one]
 exact (h.con u).trans (mul_le_mul_of_nonneg_left ((max_le_iff.mp hp).2) h.positive.le)
end invitation
end YM.CF.BPress.Spin
