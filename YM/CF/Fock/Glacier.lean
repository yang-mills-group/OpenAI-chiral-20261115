import YM.CF.Fock.Dyad
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Transfer toward the positive band. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter
attribute [local instance] opCStarAlgebra
section core
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma breeze (U : UNI n) : Continuous (twist U) := by
  simp_rw [continuous_def] -- tune
  rw [←continuous_def]; have he : ⇑(twist U)=(fun A=>U.val*A*star U.val) := funext (twist_formula U); rw [he]; fun_prop
lemma breeze_exp (U : UNI n) (A : Op n) : twist U (exp A)=exp (twist U A) := by
  letI : NormedAlgebra ℚ (Op n) := NormedAlgebra.restrictScalars ℚ ℂ (Op n)
  exact map_exp (twist U) (breeze U) _
lemma wind_inv (A : Op n) : exp A*exp (-A)=1 := by
  letI : NormedAlgebra ℚ (Op n) := NormedAlgebra.restrictScalars ℚ ℂ (Op n)
  rw [← exp_add_of_commute (Commute.refl A).neg_right,add_neg_cancel,exp_zero]
def grow (A : Op n) (t : ℝ) := exp (t • A)
lemma phase_diag (f : n→ℂ) : exp (Matrix.diagonal f) = Matrix.diagonal (Complex.exp ∘ f) := by
  rw [Matrix.exp_diagonal]; congr 1; funext i; simp [Complex.exp_eq_exp_ℂ] -- tune
lemma staff (U : UNI n) (d : n→ℝ) : exp (spectral U d)=spectral U (Real.exp ∘ d) := by
  rw [spectral, ←breeze_exp,phase_diag]; unfold spectral; simp [Function.comp_def,Complex.ofReal_exp]
lemma glacial (U : UNI n) (d : n→ℝ) (t : ℝ) : grow (spectral U d) t=spectral U (fun i=>Real.exp (t*d i)) := by rw [grow,spectral_smul,staff]; rfl
variable [Nonempty n]
def monad (A : Op n) := A * polarity A
def decay (A : Op n) (t : ℝ) := grow (monad A) (-t)
lemma flat_energy (U : UNI n) (d : n→ℝ) (h : Safe (spectral U d)) : monad (spectral U d)=spectral U (fun i=> |d i|) := by
  rw [monad,polarity_spectral _ _ h,spectral_mul]; apply congrArg; funext i; by_cases g:0<d i
  · simp [signRoles,g,abs_of_pos]
  simp [signRoles,g, abs_of_nonpos (le_of_not_gt g)]
lemma aboard {A : Op n} (h : Safe A) (t : ℝ) : grow A t * (1-projector A) = (1-projector A)*decay A t ∧ star (grow A t)*(projector A*decay A t) = projector A := by
  obtain ⟨U,d,rfl⟩ := spectral_exists A h.self
  rw [glacial,projector_spectral _ _ h,decay,flat_energy _ _ h,glacial, ←spectral_one U,spectral_sub,show ∀ f:n→ℝ, star (spectral U f)=spectral U f from fun f=>(spectral_adjoint ..).star_eq]; simp only [spectral_mul]
  constructor <;> (apply congrArg; funext i; by_cases g:0<d i)
  · simp [occ,g]
  · simp [occ,g,abs_of_nonpos (le_of_not_gt g)]
  · simp only [Pi.mul_apply,occ,g,ite_true,abs_of_pos g,one_mul]; rw [←Real.exp_add]; ring_nf; rw [Real.exp_zero]
  simp [occ,g]
lemma slows {A : Op n} (h : Safe A) (t : ℝ) (g : 0 ≤ t) : ‖decay A t‖ ≤ Real.exp (-t/2) := by
  obtain ⟨U,d,rfl⟩ := spectral_exists A h.self
  rw [decay,flat_energy _ _ h,glacial]
  let f := fun i=> Real.exp (-t*|d i|)
  have p : 0≤spectral U f := by rw [←spectral_zero U,spectral_le]; exact fun i=>(Real.exp_pos _).le
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (Real.exp_pos _).le p).mpr
  rw [Algebra.algebraMap_eq_smul_one, ←spectral_one U,spectral_smul,spectral_le]; intro i
  have hp := h.margin; rw [spectral_pow, ←spectral_one U,spectral_smul,spectral_le] at hp
  have ht := hp i; simp only [Pi.one_apply,Pi.smul_apply,smul_eq_mul,mul_one,Pi.pow_apply] at ht
  change Real.exp (-t*|d i|)≤ _*(1:ℝ); rw [mul_one]; apply Real.exp_le_exp.mpr
  have he : 1/2 ≤ |d i| := by nlinarith [sq_abs (d i), abs_nonneg (d i)]
  nlinarith [mul_le_mul_of_nonneg_left he g]
end core

variable {n : Type*} [LinearOrder n] [Fintype n]
lemma powers_hi {j : ℕ} {x : Wave n} (h : Degree j x) (C : Op n) (k : ℕ) : Degree (j+k*2) (acts (coupl C ^ k) x) := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [pow_succ',act_mul,add_mul,one_mul, ←add_assoc]; exact ih.couplD C
lemma coupl_nil (C : Op n) (k : ℕ) (h : Fintype.card n<k) : coupl C^k=0 := by
  apply op_columns; intro i; rw [act_zero]; exact (powers_hi (basis_degree i) C k).too_big (by omega)
lemma stored (C : Op n) : acts (exp (coupl C)) (vacuum n)=pairWave C := by
  rw [exp_eq_tsum ℂ]; dsimp only
  rw [tsum_eq_sum (s:=range (Fintype.card n+1)),act_sum,pairWave]; simp_rw [act_smul,pairTerm]
  intro i hi; rw [mem_range] at hi; rw [coupl_nil C i (by omega),smul_zero]
lemma cut_warm (s : Finset n) {C : Op n} (g : Cᵀ= -C) (k : IsUnit (stage (cutM s) C)) : pairWave C=acts (exp (excite (cutM s) C)) (filled (cutM s) C) := by
  have he : filled (cutM s) C=pf C s • basisKet s := by rw [filled,cutLine,cut_oneAct]; rfl
  rw [he]; nth_rw 1 [freeze s g k]; rw [map_smul,←stored,swivel (flake s), flake_vac, breeze_exp, flake_excite k]
lemma exp_excite {P C : Op n} (h : IsStarProjection P) (g : Cᵀ= -C) (k : IsUnit (stage P C)) : pairWave C=acts (exp (excite P C)) (filled P C) := by
  obtain ⟨U,s,rfl⟩ := spot_projection P h
  let D := congrC (star U) C; let Q := cutM s; let A := twist U Q; change pairWave C=acts (exp (excite A C)) (filled A C)
  have he : C=congrC U D := by
    unfold D; conv_rhs => arg 1; rw [←star_star U]
    rw [congr_inv]
  have hg : IsUnit (stage Q D) := by
    have ht := live_cong (star U) k; rw [←stage_twist (star U),twist_inv] at ht; exact ht
  have hx : acts (quantU U).val (pairWave D)=pairWave C := by
    change acts (quant U.val) _=_; rw [pair_cov]; exact congrArg pairWave he.symm
  rw [←hx,cut_warm s (show Dᵀ= -D from skew_form g) hg, swivel (quantU U),breeze_exp,excite_cov hg,←filled_twist,←he]
lemma prong_ply (f : FN n) (S T : Op n) (i : n) : prong (prong f S) T i=prong f (S*T) i := by
  unfold prong; simp only [smul_sum,smul_smul,Matrix.mul_apply,sum_smul]; rw [sum_comm]; simp only [mul_comm]
lemma flux {A P Y : Op n} (g : A * (1-P)=(1-P)*Y) (i : n) : quant A * seekF P i = prong (seekF P) Y i * quant A := by
  unfold seekF; rw [prong_ply,←g,prong_p,prong_p,quant_create,act_mul]
lemma swell {A P Y : Op n} (g : star A*(P*Y)=P) (i : n) : quant A * hideF P i=prong (hideF P) (cc Y) i * quant A := by
  unfold hideF; rw [prong_ply,←cc_mul,prong_t,prong_t, quant_ann,←act_mul,g]
lemma dyad_carries (f j l m : FN n) (S : Op n) (U : FC n) (hf : ∀ i:n, U*f i=l i*U) (hj : ∀ i:n, U*j i=m i*U) :
    U*dyad S f j=dyad S l m*U := by
  unfold dyad; simp only [sum_mul,mul_sum,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]
  simp_rw [←mul_assoc U,hf,mul_assoc, hj]
lemma inning_carries (f j l m : FN n) (S T A : Op n) (U : FC n) (hf : ∀ i:n, U*f i=l i*U) (hj : ∀ i:n, U*j i=m i*U) : U * inning f j S T A=inning l m S T A*U := by
  unfold inning; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; congr 1
  simp only [mul_add,mul_sub,add_mul,sub_mul]
  rw [dyad_carries f f l l S U hf hf,dyad_carries f j l m T U hf hj,dyad_carries j f m l Tᵀ U hj hf,dyad_carries j j m m A U hj hj]
def nextX (P C Y : Op n) := inning (hideF P) (seekF P) (cc Y*reserve P C*(cc Y)ᵀ) (cc Y*driftB P C*Yᵀ) (Y*weldB P C*Yᵀ)
lemma exc_carries {A P C Y : Op n} (g : A * (1-P)=(1-P)*Y) (k : star A*(P*Y)=P) (h : IsStarProjection P) (e : IsUnit (stage P C)) :
    SemiconjBy (quant A) (excite P C) (nextX P C Y) := by
  unfold SemiconjBy nextX; rw [←in_sector h e, ←inning_lift]; exact inning_carries _ _ _ _ _ _ _ _ (swell k) (flux g)

variable [Nonempty n]
def flight (A : Op n) (t : ℝ) := Complex.exp ((t:ℂ)*(A*projector A).trace)
lemma line_flies {A : Op n} (h : Safe A) (t : ℝ) : quant (grow A t)*lineOp (projector A)= flight A t • lineOp (projector A) := by
  obtain ⟨U,d,rfl⟩ := spectral_exists A h.self
  let s := univ.filter fun i=> 0<d i; let P := cutM s; let D (i:n) := Real.exp (t*d i); let B := spectral U d
  have he : projector B=twist U P := by rw [projector_spectral U d h]; simp only [spectral]; congr 2; ext i; by_cases g:0<d i <;> simp [s,occ,g]
  let X := Matrix.diagonal fun i => (D i:ℂ)
  have ht : grow B t=twist U X := glacial U d t
  have hp : (B*projector B).trace=∑ i∈s,(d i:ℂ) := by
    rw [he]; unfold B spectral; rw [←map_mul, trace_twist]; unfold P cutM; rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,sum_filter]; apply sum_congr rfl; intro i _; by_cases g:0<d i <;> simp [s,g]
  have hx : (∏ i∈s, (D i:ℂ))=flight B t := by
    rw [flight,hp,mul_sum,Complex.exp_sum]; simp [D,Complex.ofReal_exp]
  change quant (grow B t) * lineOp (projector B)=flight B t • lineOp (projector B)
  rw [he,ht,line_twist,quant_twist, ←map_mul, ←twist_scalar]
  unfold X P; rw [quant_diag,cutLine]; apply congrArg
  ext i j; unfold cutM; rw [Matrix.diagonal_mul_diagonal]; by_cases g:i=j
  · subst j; by_cases k:i=s
    · subst i; simp [hx]
    simp [k]
  simp [g]
def shot (A C : Op n) (t : ℝ) := nextX (projector A) C (decay A t)
lemma pushed {A C : Op n} (h : Safe A) (g : Cᵀ= -C) (e : IsUnit (stage (projector A) C)) (t : ℝ) :
    acts (quant (grow A t)) (pairWave C)=flight A t • acts (exp (shot A C t)) (filled (projector A) C) := by
  have H := aboard h t
  let L := quant (grow A t); let K := excite (projector A) C
  have ht : L * exp K=exp (shot A C t)*L := by
    letI : NormedAlgebra ℚ (FC n) := NormedAlgebra.restrictScalars ℚ ℂ (FC n)
    exact (exc_carries H.1 H.2 h.projection e).exp_right.eq
  have hx : acts L (filled (projector A) C)=flight A t • filled (projector A) C := by rw [filled,←act_mul,line_flies h t,act_smul] -- tune
  change acts L (pairWave C) = _; rw [exp_excite h.projection g e,←act_mul,ht,act_mul,hx,map_smul]
end YM.CF.Fock
