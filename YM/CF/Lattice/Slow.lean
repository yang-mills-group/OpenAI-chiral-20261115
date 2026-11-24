import YM.CF.Matter.Pair
import YM.CF.Lattice.Covariant

/-!
# Fermion band on a joint SU5 background

Use symplectic form from the spin intertwiner tensored with the equivariant
real structure for this representation. Estimate the angle **independently of
lattice size**. This works on gauge-covariantly slow fundamental unit fields;
the next obligation is producing such fields on any admissible U.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 6000
noncomputable section
namespace YM.CF.Lat
open Lattice SU SU.Pair
open scoped Matrix.Norms.L2Operator MatrixOrder Topology BigOperators Kronecker Matrix
attribute [local instance] opCStarAlgebra
variable {N : Side}
instance instSlotDec : DecidableEq Slot := inferInstance

abbrev Vect := Ket F
abbrev Bkg (N : Side) := RLink N E
abbrev Model (N : Side) := Tx N Slot

def turn (g:E) (x:Vect) := acts (fund g) x
lemma turn_norm (g x) : ‖turn g x‖=‖x‖ := by
  have he (g:E) (x:Vect) : ‖turn g x‖≤‖x‖ :=
    (ContinuousLinearMap.le_opNorm ..).trans <| by rw [acts, Matrix.l2_opNorm_toEuclideanCLM, CStarRing.norm_of_mem_unitary (fund_U g),one_mul]
  apply le_antisymm (he g x)
  have hG : turn g⁻¹ (turn g x) = x := by
    unfold turn
    rw [show ∀ A B: Op F, acts A (acts B x)=acts (A*B) x from fun A B => by
      unfold acts; rw [map_mul]; rfl]
    rw [← fund_mul,inv_mul_cancel,fund_one,acts,map_one]; rfl
  simpa only [hG] using he g⁻¹ (turn g x)
@[fun_prop] lemma turn_cont : Continuous (fun (p:E×Vect) => turn p.1 p.2) := by
  unfold turn acts
  apply Continuous.clm_apply _ continuous_snd
  have ht : Continuous (fun A:Op F => acts A) := (Matrix.toEuclideanCLM (n:=F) (𝕜:=ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact ht.comp (fund_cont.comp continuous_fst)

def localPair (x:Vect) : Op (SpinIdx × Slot) := spinJ ⊗ₖ fullM x
@[fun_prop] lemma localPair_cont : Continuous localPair := by
  refine continuous_matrix ?_; rintro ⟨i,x⟩ ⟨j,y⟩; exact continuous_const.mul (SU.Pair.full_cont.matrix_elem x y)
lemma localPair_skew (x:Vect) (h : ‖x‖=1) : (localPair x)ᵀ= -localPair x := by
  rw [localPair, ← Matrix.kroneckerMap_transpose,(SU.Pair.full_laws _ h).1,
    show spinJᵀ= -spinJ by
      have h := spinJ_real
      unfold cc at h; rw [← h, Matrix.transpose_transpose,h,spinJ_star], op_kron_neg]
lemma localPair_mem (x:Vect) (h : ‖x‖=1) : localPair x∈ unitary _ :=
  Matrix.kronecker_mem_unitary spinJ_unitary (SU.Pair.full_laws _ h).2.2
lemma localPair_turn (g:E) (x:Vect) : localPair (turn g x)=color matter g * localPair x * (color matter g)ᵀ := by
  simp only [localPair,color, ← Matrix.kroneckerMap_transpose,op_kron_mul,one_mul,Matrix.transpose_one,mul_one,
    turn,SU.Pair.full_cong]
lemma hop_mult (x : Vect) (z : Site N) (U : Bkg N) (cut) (i : Axis) :
    hop matter U cut i z * localPair x = localPair (turn (U (z,i)) x) * cc (hop matter U cut i z) := by
  let g := U (z,i)
  let G := color matter g
  have hi : Gᵀ * cc G = 1 := by
    rw [cc, ← Matrix.transpose_mul, show star G * G = 1 from (color_mem ..).1,Matrix.transpose_one]
  rw [hop, cc_smul,seam_real, localPair_turn, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,
    mul_assoc (G*localPair x)] -- check
  change _= _ • ((G*localPair x)*(Gᵀ * cc G)); rw [hi,mul_one]

def Cfield (v : Site N → Vect) : Op (Tx N Slot) := jump (Equiv.refl _) (fun x => localPair (v x))
lemma C_cont : Continuous (Cfield (N:=N)) :=
  (jump_cont _).comp (continuous_pi fun _ => localPair_cont.comp (continuous_apply _))
lemma C_unit (v : Site N → Vect) (hv : ∀ x, ‖v x‖=1) : Cfield v ∈ unitary _ :=
  jump_unitary _ _ fun x => localPair_mem _ (hv x)
lemma C_skew (v : Site N → Vect) (hv : ∀ x, ‖v x‖=1) : (Cfield v)ᵀ= -Cfield v := by
  ext ⟨x,i⟩ ⟨y,j⟩; by_cases e:x=y
  · subst y; simp only [Cfield,Matrix.transpose_apply,jump_apply,Equiv.refl_apply,ite_true,Matrix.neg_apply]
    exact Matrix.ext_iff.mpr (localPair_skew _ (hv _)) _ _
  simp [Cfield,jump_apply,e,Ne.symm e]
lemma C_gauge (v : Site N → Vect) (t : Site N → E) :
    Cfield (fun x => turn (t x) (v x)) = (conjG matter t).val * Cfield v * (conjG matter t).valᵀ := by
  rw [show (conjG matter t).valᵀ=jump (Equiv.refl _) (fun x => (color matter (t x))ᵀ) by
    ext ⟨x,i⟩ ⟨y,j⟩; by_cases h:x=y
    · subst y; simp [jump_apply,conjG]
    simp [jump_apply,conjG,h, Ne.symm h]]
  simp only [conjG,Cfield,jump_mul,Equiv.refl_trans,Equiv.refl_apply,localPair_turn]
lemma inter_spin (v : Site N → Vect) (A : Op SpinIdx) (h : A * spinJ=spinJ * cc A) :
    spin N Slot A * Cfield v = Cfield v * cc (spin N Slot A) := by
  simp only [spin,Cfield,jump_cc,jump_mul,Equiv.refl_trans,Equiv.refl_apply,localPair,op_cc_kron,
    op_kron_mul, one_mul,h,cc_one,mul_one]
/-- Slowness here is in covariant norm along the fermion steps. -/
def Slow (U : Bkg N) (v : Site N → Vect) (e : ℝ) : Prop :=
  ∀ x i, ‖turn (U (x,i)) (v (x+step i))-v x‖ < e
lemma inter_hop (ε : ℝ) (hε : 0 < ε) : ∃ δ>0, ∀ (N : Side) (cut : Site N) (U : Bkg N) (v : Site N → Vect),
    (∀ x, ‖v x‖=1) → Slow U v δ → ∀ i, ‖shift matter U cut i * Cfield v - Cfield v * cc (shift matter U cut i)‖ ≤ ε := by
  have he : UniformContinuousOn localPair {x | ‖x‖=1} :=
    (show IsCompact _ by rw [show {x : Vect | ‖x‖=1}=Metric.sphere 0 1 by ext; simp]; exact isCompact_sphere ..).uniformContinuousOn_of_continuous localPair_cont.continuousOn
  obtain ⟨δ,hδ,h⟩ := Metric.uniformContinuousOn_iff.mp he ε hε
  refine ⟨δ,hδ,?_⟩; intro N cut U v hv hs i
  unfold Cfield shift
  rw [jump_cc,jump_mul,jump_mul,Equiv.refl_trans,Equiv.trans_refl,← jump_sub]; apply jump_bound _ _ hε.le; intro x
  let y := v (x+step i); let g := U (x,i); let J := hop matter U cut i x
  change ‖hop matter U cut i x * localPair y - localPair (v x)*cc J‖ ≤ ε
  have ht : dist (turn g y) (v x) < δ := by rw [dist_eq_norm]; exact hs x i
  have hkey := h _ (show _ from Eq.trans (turn_norm g y) (hv _)) _ (show _ from hv x) ht
  change dist (localPair (turn g y)) (localPair (v x)) < _ at hkey
  rw [dist_eq_norm] at hkey
  rw [hop_mult]
  change ‖localPair (turn g y) * cc J - localPair (v x) * cc J‖ ≤ _
  rw [← sub_mul]
  apply (norm_mul_le ..).trans
  have hk : cc J ∈ unitary _ := (ccU ⟨J,hop_mem ..⟩).property
  rw [CStarRing.norm_of_mem_unitary hk,mul_one]; exact hkey.le

-- compare all linear combinations before projector.
section
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
def skewError (G : UNI n) (A : Op n) (r : ℝ) := ‖A*G.val-G.val*cc A‖ ≤ r
namespace skewError
variable {G : UNI n} {A B : Op n} {r s : ℝ}
lemma orth (h : skewError G A r) : skewError G (star A) r := by
  unfold skewError at *
  rw [← twist_sub] at *; rw [cc_star,map_star,← star_sub,norm_star]; exact h
lemma neg (h : skewError G A r) : skewError G (-A) r := by
  unfold skewError at *; rw [← twist_sub] at *; rw [cc_neg,map_neg,neg_sub_neg,norm_sub_rev]; exact h
lemma one (G : UNI n) : skewError G 1 0 := by simp [skewError]
lemma add (ha : skewError G A r) (hb : skewError G B s) : skewError G (A+B) (r+s) := by
  unfold skewError at *; rw [cc_add,mul_add,add_mul,add_sub_add_comm]
  exact (norm_add_le ..).trans (add_le_add ha hb)
lemma diff (ha : skewError G A r) (hb : skewError G B s) : skewError G (A-B) (r+s) := by rw [sub_eq_add_neg]; exact ha.add hb.neg
lemma times (ha : A*G.val=G.val*cc A) (he : ‖A‖=1) (hb : skewError G B r) : skewError G (A*B) r := by
  unfold skewError at *; rw [cc_mul, ← mul_assoc G.val, ← ha,mul_assoc A,mul_assoc A, ← mul_sub]
  exact (norm_mul_le ..).trans (by rw [he,one_mul]; exact hb)
lemma half (ha : skewError G A (r+r)) : skewError G ((1/2 : ℝ) • A) r := by
  unfold skewError at *; rw [cc_rsmul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,← smul_sub,norm_smul]
  exact (mul_le_mul_of_nonneg_left ha (norm_nonneg _)).trans (le_of_eq (WilsonFrame.half_step r))
lemma collect (F : Fin 4 → Op n) (h : ∀ i, skewError G (F i) r) : skewError G (∑ i, F i) (4*r) := by
  simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  rw [show 4*r=r+(r+(r+r)) by ring]
  exact (h _).add ((h _).add ((h _).add (h _)))
end skewError
end

/-- Pairing works uniformly on the full color representation, on all capped
components where the displayed covariantly slow field is available. -/
theorem compressible : ∃ δ:ℝ, 0<δ ∧ ∀ (N : Side) (cut : Site N) (U : Bkg N) (v : Site N → Vect),
    PlaqBound matter U (1/60) → (∀ x, ‖v x‖=1) → Slow U v δ →
    let P := projector (frame matter U cut).H; ‖P * Cfield v - Cfield v * cc P‖ ≤ 1/3 := by
  let e : ℝ := 1/400000
  obtain ⟨δ,hδ,h⟩ := inter_hop e (by unfold e; norm_num)
  refine ⟨δ,hδ,?_⟩; intro N cut U v hp hv hs P
  let W := frame matter U cut
  let G : UNI (Tx N Slot) := ⟨Cfield v, C_unit v hv⟩
  have hi (i) : skewError G (W.inc i) (e+e) := by
    have ht : skewError G (W.T i) e := h _ _ _ _ hv hs _
    have hx := (skewError.one G).diff (skewError.half (ht.add ht.orth)); rw [zero_add] at hx
    apply skewError.add hx; exact (skewError.half (ht.diff ht.orth)).times (inter_spin v _ (spinJ_inter i)) (W.gamma_norm _)
  have hb := (skewError.one G).neg.add (skewError.collect _ hi); rw [zero_add] at hb
  have he : skewError G W.H (4*(e+e)) := hb.times (inter_spin v _ spinJ_grading) W.chir_norm
  apply ((band _ _ _ hp).antiunitary G).trans
  apply (mul_le_mul_of_nonneg_left he (show (0:ℝ)≤16400 by norm_num)).trans; unfold e; norm_num
end YM.CF.Lat
