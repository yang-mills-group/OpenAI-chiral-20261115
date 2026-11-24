import YM.CF.BProof.Gauss.Vault

/- residual exponential weights and Jacobian part. Installed quadratic matches Eq (Heavy).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss.Beam
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision RealM SignScalar
open Prox (Base Show Scope Pup Solo)
open YM.SectorNext.Vacuum.Panel
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {s:Side}{Y:Yard s}(T:PathData SU.group) {M:ℕ}{c:Clip}(θ:ℝ){P y q w:ℝ} (U:Beam c P Y.short M y)(Z:Finset Y.Col)
variable (H:Room Y M)(u:T.Bounds c w P q)(h: θ∈Set.Icc (1/2) 2)(x:Plan Y)

def drive : Plan Y := ζ T θ U Z *ᵥ x
def black := 1- ζ T θ U Z * host Y T M c θ Z * ζ T θ U Z
def bill := (x ⬝ᵥ ((U.black T θ Z)*ᵥ x))/2
include H
lemma meter : Prox.Via (edge Y) (Scope.flags _) (black T θ U) (U.horizon'+6*M+U.horizon') := by
 let X:=ζ T θ U; exact (Prox.Via.one (k:=U.horizon'+6*M+U.horizon') (F:=edge Y) (S:=Scope.flags Y.Col)).sub (((ζ_v T θ U H).mul (hostP Y T M c θ H)).mul (ζ_v T θ U H))
lemma still (i: Stamp Y)(v:i.1∈Z): drive T θ U Z x i=x i:=by unfold drive; rw [Matrix.mulVec,dotProduct]; simp_rw [U.held T θ H Z _ _ v]; exact congr_fun (Matrix.one_mulVec x) i
lemma flown (b:Y.Col)(v:b∈Z){i}: lowerMap Y (drive T θ U Z x) (b,i)=lowerMap Y x (b,i):= PiLp.ext fun i=> still T θ U Z H x _ v -- tune
include h u
lemma wave : (host Y T M c θ Z).IsHermitian ∧ (U.black T θ Z).IsHermitian ∧ ‖U.black T θ Z‖≤y⁻¹^2 :=by
 obtain ⟨a,-,-,v⟩:= U.measured T θ H u h Z; have hH:=charge_H Y T M c θ Z; refine ⟨hH,?_,v⟩; unfold black Matrix.IsHermitian; rw [Matrix.conjTranspose_sub,conjTranspose_one,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,a.eq,hH.eq,mul_assoc]
lemma photo (i: Stamp Y)(v:i.1∈Z) : ∀ j,U.black T θ Z i j=0:=by
 intro j; unfold black; simp only [Matrix.sub_apply]; have hp: Bin.Badge 1 i (U.ζ T θ Z):=by intro j; rw [U.held T θ H Z _ _ v,one_smul]
 have hP: Bin.Badge 1 i (host Y T M c θ Z):=by intro j; rw [host_row Y T M c θ Z _ _ H v,one_smul] -- dots
 rw [((hp.kit hP).kit hp) j,mul_one,mul_one, one_smul,sub_self]
-- scaling identity with omission at Z already in good ledger. work definition theta homogeneous incl βg².
lemma journey : let w:=lowerMap Y x; -(work Y M Z c T θ (lowerMap Y (drive T θ U Z x))) = - ((∑ b∈ Zᶜ, fans Y w b)/2) + U.bill T θ Z x:=by
 intro w; let b:=U.ζ T θ Z; let A:=host Y T M c θ Z; let v:= drive T θ U Z x; let B:=U.black T θ Z; have hB:x ⬝ᵥ (B *ᵥ x)=dotProduct x x-dotProduct v (A *ᵥ v):= by
    have hx: dotProduct v (A *ᵥ v)= dotProduct x ((b * A * b)*ᵥ x):=by
       have hb:bᵀ=b:=by simpa using (U.measured T θ H u h Z).1.eq
       rw [mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,dotProduct_mulVec x b, ← mulVec_transpose,hb]; exact rfl
    change dotProduct x ((1-b*A*b)*ᵥ x)=_; rw [sub_mulVec,one_mulVec,dotProduct_sub,hx]
 have h':∑ i∈Z,fans Y w i=∑ i∈Z,fans Y (lowerMap Y v) i:=sum_congr rfl fun i hi=>by unfold fans; apply sum_congr rfl; intro j _; unfold w; rw [← U.flown T θ Z H x i hi] -- tune argument
 have e:= paycheck Y T M c θ Z v; rw [tally Y x] at hB; rw [← sum_add_sum_compl Z] at hB; change x ⬝ᵥ (B*ᵥ x) = (∑ i∈ Z,fans Y w i)+(∑ i∈ Zᶜ,fans Y w i)-_ at hB; rw [h'] at hB; change v ⬝ᵥ (A*ᵥ v)=(∑ i∈Z, fans Y (lowerMap Y v) i)+_ at e; rw [e] at hB; change -work Y M Z c T θ (lowerMap Y v)=-( (∑ i∈Zᶜ,fans Y w i)/2)+(x ⬝ᵥ (B *ᵥ x))/2; linarith only [hB]
omit h u H
lemma turn (β g:ℝ)(p: θ=β*g^2) (W:Y.Branch): work Y M Z c T β (g • W)=work Y M Z c T θ W:=by
 subst θ; apply sum_congr rfl; intro l hl; unfold Q; rw [map_smul,map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]; unfold unit; ring
end YM.CF.BProof.Gauss.Beam
