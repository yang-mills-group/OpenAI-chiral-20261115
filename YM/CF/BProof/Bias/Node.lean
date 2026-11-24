import YM.CF.BProof.Bias.Zed
/-! Uniformity on n≥j: momentum test costs by recognition of pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint
open Fir Laurent Rush Bloch Next.Free BZ
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side} {j:ℕ}(M:Male)(h:1≤j)(x:Site N)
def mode_s := modality {x}
abbrev bird(x:Site N)(i:Axis):= wing i (x i)
lemma bird_l : bird x 0*bird x 1*bird x 2*bird x 3= mode_s x:=by
 unfold bird wing mode_s; rw [mode_inter,mode_inter,mode_inter]; apply congrArg; ext y; simp only [mem_inter,labelled,mem_singleton]; constructor; intro H; rcases H with ⟨⟨⟨h,g⟩,p⟩,q⟩; funext i; fin_cases i<;>assumption; rintro rfl; simp
lemma node_A_norm : ‖tickA N *mode_s x‖=1:=by
 let T:= tickA N; let U:=mode_s x; let V:= T*U; have ht: V=relic (fun i=> if i=x then sky else 0):=by
   dsimp only [V,T,U,mode_s,modality]; rw [sky_t,relic_mul]; apply congrArg; funext i; by_cases h:i=x <;> simp [thinK,h]
 apply sprojNorm (A:=V)
 · rw [ht]; constructor; · unfold IsIdempotentElem; rw [relic_mul]; apply congrArg; funext i; by_cases g:i=x <;> simp [g,sky_h.1.eq] -- tune
   unfold IsSelfAdjoint; rw [relic_star]; apply congrArg; funext i; by_cases g:i=x <;> simp [g,sky_h.isSelfAdjoint.star_eq]
 rw [ht]; let a:Slot:=Classical.arbitrary _; let i:Single N:=((x,0),a); intro g; rw [relic_plane,←map_zero (twist (air N))] at g; have hw:= Matrix.ext_iff.mpr ((twist (air N)).injective g) i i; unfold plane liftA sky at hw; simp only [i,Matrix.kronecker_apply,jump_apply,Equiv.refl_apply,ite_true,Matrix.one_apply_eq, Matrix.zero_apply] at hw; rw [←pill_plus] at hw; simp [pill,spHalf,cutM,plusHalf] at hw
include h
lemma node_zag : ‖Zenith j M N * mode_s x‖ = ‖zag j M x‖ := by
 let Z:= Zenith j M N; let R:=mode_s x; let d:=hat j M x; let T:=tickA N
 have he: star (Z*R)*(Z*R)= (d⁻¹-1) • (T*R):=by unfold Z R mode_s modality T; rw [sky_t,relic_mul,relic_star,relic_mul,relic_mul,relic_r]; apply congrArg; funext i; by_cases g:i=x<;> simp [thinK,g, zag_gram j M h x,d]
 rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),zag_norm j M h x,pow_two,← CStarRing.norm_star_mul_self,he,norm_smul,node_A_norm,mul_one]; exact Real.norm_of_nonneg (sub_nonneg.mpr (one_le_inv₀ (hat_p j M h x) |>.2 (hat_e ..)))
omit h in
lemma node_kin (w:Per N)(p:x∈Label 1 w) : AngleZ j M w * mode_s x= Zenith j M N * mode_s x:=by rw [AngleZ,mul_assoc,show haloW w * mode_s x=_ from mode_sub (singleton_subset_iff.mpr p)]; rfl
end YM.CF.BProof.Bias
