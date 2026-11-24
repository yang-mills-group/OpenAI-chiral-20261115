import ForceSatin.ExactShear
import ForceSatin.HomeTilt
/-! quantitative alternate to truncating Fourier at low momentum. WA.11 needs
    an approximation of all transformed CAR letters, with the approximants buying
    polynomial Bessel cost and the discarded part power-suppressed. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Set Filter NormedSpace Fock Finset Cascade Thera Verses
open Lattice Laurent Bloch Lat Cube Rush SU Fir Nacre Ember Scroll Tulip Tenant BPress.Spin.Blank Dial
open Crest.Sleet
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra


lemma survive_weight {z : ℝ} (h : 0≤z) (p : z≤1) (k : ℕ) : k*z*(1-z)^k ≤ 1 := by
  have a : 0≤1-z:=sub_nonneg.mpr p
  have u:0≤1+z:=by linarith
  have b : 1+↑k*z ≤ (1+z)^k := one_add_mul_le_pow (by linarith) k
  apply le_trans (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_left zero_le_one).trans b) (pow_nonneg a _))
  rw [←mul_pow]; exact pow_le_one₀ (mul_nonneg u a) (by nlinarith)

lemma weight_gap {z : ℝ} {k:ℕ} (h : 0≤z) (p : z≤1) (g : k>0) :
    (1-z)^k * Real.sqrt z ≤ (Real.sqrt (k:ℝ))⁻¹ := by
  let t:= (1-z)^k
  let v:ℝ:=k; have ht:0≤t:=pow_nonneg (sub_nonneg.mpr p) _; have hv:0<v:=Nat.cast_pos.mpr g
  let d:= Real.sqrt z; have he:d^2=z:=Real.sq_sqrt h
  apply le_of_pow_le_pow_left₀ (by decide : (2:ℕ)≠0) (by positivity) ?_
  change (t*d)^2≤(Real.sqrt v)⁻¹^2; rw [mul_pow,he,inv_pow,Real.sq_sqrt hv.le]; rw [←one_div]; apply (le_div_iff₀ hv).mpr
  have hx: t^2≤t:=by
    rw [pow_two]; exact mul_le_of_le_one_left ht (pow_le_one₀ (sub_nonneg.mpr p) (by linarith) : t≤1)
  have hy:v*z*t ≤1:=survive_weight h p k
  nlinarith only [hy,mul_le_mul_of_nonneg_right hx (show 0≤v*z by positivity)]

section
variable (j:ℕ) (h: 1 ≤ j)
local notation "rₖ" k:max => (Real.sqrt (k:ℝ))⁻¹

-- `hoe` argument of Pincer.lean, use on both orientations of X
private lemma price {N:Side} (A:Momentum→Op SpinIdx) (c:ℝ)
    (t:∑ i:Site N, ‖A (mel i)‖^2 ≤ c*N.val^4)(i:Single N):
    ‖acts (lens A N) (basisKet i)‖^2 ≤ c := by
  obtain ⟨⟨x,i⟩,j⟩:=i
  rw [spice]; apply (mul_le_mul_of_nonneg_left (le_trans (sum_le_sum (g:=fun i=> ‖A (mel i)‖^2) (fun i h=>?_)) t) (by positivity)).trans_eq (by field_simp [nPos N|>.ne'])
  apply pow_le_pow_left₀ (norm_nonneg _); apply (ContinuousLinearMap.le_opNorm _ _).trans; unfold acts; rw [Matrix.l2_opNorm_toEuclideanCLM]; simp [basisKet]

include h
theorem neumann_truncation : ∃ C:ℝ,0<C∧∀ (k:ℕ), k>0 → ∀ (N:Side)(M:Tulip.Male),
    let P:=spar j M (1:Bkg (More N));let B:=tickA N;
    ∀ (p:IsStarProjection P) (l:Single N),let T:=flatComb j M N h p - Comb B P k; ‖acts T (basisKet l)‖^2 ≤ C*rₖ k ∧ ‖acts (star T) (basisKet l)‖^2 ≤ C*rₖ k:=by
  obtain ⟨C,hc,u⟩:= bills j h
  refine ⟨C,hc,?_⟩; intro k t N M P B p i T
  let c:ℝ:=C*rₖ k
  let F:= flatComb j M N h p; let X:=Comb B P
  have he(v:ℕ)(p':k≤v): ‖acts (X v-X k) (basisKet i)‖^2 ≤ c ∧ ‖acts (star (X v-X k)) (basisKet i)‖^2 ≤ c:=by
    let G(p:Momentum):=Comb (angle true) (bent true j M.val p) v-Comb (angle true) (bent true j M.val p) k
    have hx:X v-X k=lens G N:=by unfold X P B; rw [angledK h,angledK h,l_sub]
    let q:=rₖ k; have hq:0≤q:=by unfold q; positivity
    have hz: ∑ i:Site N, ‖G (mel i)‖^2 ≤ c*N.val^4:= by
      apply (sum_le_sum (g:=fun i=> q*(hard (zTar j M i))⁻¹) (fun i h'=>?_)).trans
        (le_trans (show _≤q*(C*N.val^4) by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (u N M) hq)
          (le_of_eq (by unfold c q; ring)))
      let z:=zTar j M i; let W:= Real.sqrt z; let d:=(1-z)^k; have ht:0<z:=amp j h _ _; have hv:=z_cap h p i
      have hd:0≤d:=pow_nonneg (sub_nonneg.mpr hv) _; have hy:d≤1:=pow_le_one₀ (sub_nonneg.mpr hv) (by linarith only [ht])
      have hl:d*W ≤ q:=weight_gap ht.le hv t; have hh:0<W:=Real.sqrt_pos.mpr ht
      apply (pow_le_pow_left₀ (norm_nonneg _) (zGap h p i k v p') _).trans; change (d*W⁻¹)^2 ≤ q*(W^3)⁻¹; field_simp; nlinarith only [mul_le_mul_of_nonneg_right hy (show 0≤d*W by positivity),hl]
    refine ⟨hx.symm ▸ price G c hz i,hx.symm ▸ ?_⟩
    rw [l_star]; apply price _ _ _ i
    simp only [norm_star]; exact hz
  let W (x : Op (Single N)):=‖acts (x-X k) (basisKet i)‖^2
  have ht:Tendsto X atTop (𝓝 F):= flatComb_tends j M N h p
  constructor
  · exact le_of_tendsto (((show Continuous W by unfold W; fun_prop).tendsto F).comp ht) ((eventually_ge_atTop k).mono fun i hi=> (he i hi).1)
  let W'(x:Op (Single N)):= ‖acts (star (x-X k)) (basisKet i)‖^2
  exact le_of_tendsto (((show Continuous W' by unfold W'; fun_prop).tendsto F).comp ht) ((eventually_ge_atTop k).mono fun i hi=> (he i hi).2)

end

section
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable {P B:Op I}(p:IsStarProjection P)(b:IsStarProjection B)
include p b
omit [Nonempty I] in
lemma comb_global (k:ℕ) : ‖Comb B P k‖ ≤ k := by
  let C:=P*B*P; let Q:=1-P
  have hP:‖P‖ ≤1:=p.norm_le _; have hB:‖B‖ ≤1:=b.norm_le _; have hQ:‖Q‖ ≤1:=p.one_sub.norm_le _
  have e (A B:Op I)(x:‖A‖≤1)(y:‖B‖≤1): ‖A*B‖≤1:= (norm_mul_le ..).trans (by nlinarith only [mul_le_of_le_one_right (norm_nonneg A) y,x])
  have hh(a:Op I)(h:IsStarProjection a):0≤P*a*P:=le_trans (star_mul_self_nonneg (a*P)) (le_of_eq (by rw [star_mul,p.isSelfAdjoint,h.isSelfAdjoint,←mul_assoc,mul_assoc P a a,h.isIdempotentElem.eq]))
  have m:‖1-C‖≤1:=by
    have h: 0≤1-C:= by
      rw [show 1-C=1-P+P*(1-B)*P from ?_]; exact add_nonneg p.one_sub.nonneg (hh (1-B) b.one_sub)
      rw [mul_sub P 1, mul_one,sub_mul,p.isIdempotentElem.eq]; unfold C; abel
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ h).mpr (sub_le_self 1 (hh B b))
  induction k with
  | zero => simp [Comb]
  | succ k ih=> rw [Comb,Nat.cast_add_one]; exact (norm_add_le ..).trans ((add_le_add (e _ P (e Q B hQ hB) hP) ((norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) m).trans ih))).trans_eq (add_comm ..))

lemma saber_op (k:ℕ) :
    ‖(Saber (B:=B) p k).sell‖ ≤ 1 + (k:ℝ) ∧ ‖(Saber (B:=B) p k).buy‖ ≤ 1 + (k:ℝ) := by
  unfold Saber; dsimp only
  exact ⟨(norm_add_le ..).trans (add_le_add norm_one.le ((norm_star _).le.trans (comb_global p b k))),
    (norm_sub_le ..).trans (add_le_add norm_one.le ((norm_star _).le.trans (comb_global p b k)))⟩
end
end YM.CF.Papyrus.Franc.SatinForce
