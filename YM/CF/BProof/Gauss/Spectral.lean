/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.BProof.Gauss.Host
import YM.CF.Operator.SignScalar
import YM.SectorNext.VACUUM_NORMALIZATION.Etch

/- Real spectral calculus for the column Gaussian change of variables. Uniform bounds
purchased before x. On an empty index space all norm statements allow zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss.RealM
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision Unitary
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {I : Type*} [Fintype I][DecidableEq I]
abbrev Move (I:Type*)[Fintype I][DecidableEq I] := ↥(unitary (Pool I))
variable (U:Move I) (d x:I→ℝ) (A:Pool I)
def shift := Unitary.conjStarAlgAut ℝ (Pool I) U
def dial : Pool I:= shift U (Matrix.diagonal d)
theorem dial_bound : ‖dial U d‖=‖d‖:=by simp only [dial,shift,Unitary.conjStarAlgAut_apply,← Unitary.coe_star,CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,l2_opNorm_diagonal] -- tune names
theorem dial_mono (p:d≤x): dial U d≤dial U x := by
 simp only [dial,shift,Unitary.conjStarAlgAut_apply]; apply star_right_conjugate_le_conjugate; rw [Matrix.le_iff, Matrix.diagonal_sub]; exact Matrix.PosSemidef.diagonal (fun i=>sub_nonneg.mpr (p i)) -- tune
theorem dial_reflect : (dial U d).IsHermitian:= by apply Matrix.isHermitian_iff_isSelfAdjoint.mpr; unfold dial; rw [isSelfAdjoint_iff,← map_star]; exact congrArg (shift U) ((Matrix.isHermitian_diagonal d).eq) -- tune
@[simp] theorem dial_one : dial U 1=1:=by simp [dial]
theorem dial_const (r:ℝ): dial U (fun _=>r)= r • 1:=by rw [show (fun _ : I=>r)=r • (1:I→ℝ) from funext fun x=> (mul_one r).symm,dial,diagonal_smul,map_smul,← dial,dial_one]
theorem dial_add : dial U (d+x)=dial U d+dial U x:=by unfold dial; rw [← map_add,diagonal_add]; rfl
theorem dial_sub : dial U (d-x)=dial U d-dial U x:=by unfold dial; rw [← map_sub,diagonal_sub]; rfl
theorem dial_mul : dial U (d*x)=dial U d*dial U x:=by unfold dial; rw [← map_mul,diagonal_mul_diagonal]; rfl
theorem dial_pow (p:ℕ): dial U (d^p)=dial U d^p:= by induction p with|zero=> simp|succ p ih=> rw [pow_succ,dial_mul,ih,pow_succ]
@[simp] theorem dial_zero : dial U 0=0:=by simp [dial]
theorem dial_smul (r:ℝ) : dial U (r • d)=r • dial U d:=by unfold dial; rw [diagonal_smul,map_smul]
theorem dial_sum {A:Type*}(t:Finset A)(v:A→(I→ℝ)) : ∑ a∈ t,dial U (v a)=dial U (∑ a∈t,v a):=by
 induction t using Finset.induction_on with |empty=>simp|insert i t h ih=> rw [sum_insert h,sum_insert h,dial_add,ih]
lemma norm_le {r:ℝ}(h:0≤r)(p:∀ i,|d i|≤ r): ‖dial U d‖≤r:=by rw [dial_bound,pi_norm_le_iff_of_nonneg h]; exact p
theorem dial_numeric {η r:ℝ}(h:∀ i,η ≤ d i)(p:∀ i,d i≤ r) : Numeric (dial U d) η r := by
 have ht (A B:Pool I)(h:A≤B)(x:I→ℝ): x ⬝ᵥ (A *ᵥ x)≤x ⬝ᵥ (B *ᵥ x):=by
    have hh:= (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x; rw [sub_mulVec, dotProduct_sub, sub_nonneg] at hh; simpa using hh -- star
 intro x
 have he(r:ℝ): x ⬝ᵥ ((dial U (fun _=>r))*ᵥ x)= r*(x ⬝ᵥ x):=by rw [dial_const,smul_mulVec,one_mulVec,dotProduct_smul]; rfl
 rw [←he,←he]; exact ⟨ht _ _ (dial_mono U (fun _=>η) d h) x,ht _ _ (dial_mono U d (fun _=>r) p) x⟩
lemma dial_receipt (H:A.IsHermitian) {η r:ℝ}(h:Numeric A η r): ∃ U: Move I,∃ d,A=dial U d ∧ ∀ i,η≤d i∧ d i≤r :=by
 exact ⟨H.eigenvectorUnitary,H.eigenvalues,H.spectral_theorem,fun i=> SectorNext.Vacuum.Panel.bill_quad H h i⟩
theorem entry (i j:I) : |A i j|≤‖A‖:=by
 let x:=EuclideanSpace.single j (1:ℝ); let w:= Matrix.toEuclideanCLM (𝕜:=ℝ) A x; have h:‖w‖≤‖A‖:=by
    have hx:‖x‖=1:=by simp [x]
    rw [← l2_opNorm_toEuclideanCLM]; apply le_trans ((Matrix.toEuclideanCLM (𝕜:=ℝ) A).le_opNorm x); rw [hx,mul_one]
 have e: |A i j|=‖w i‖:=by unfold w; simp only [Matrix.ofLp_toEuclideanCLM]; simp [x, Matrix.mulVec, dotProduct, Pi.single_apply] -- tune
 exact e.trans_le ((PiLp.norm_apply_le w i).trans h)
end YM.CF.BProof.Gauss.RealM
