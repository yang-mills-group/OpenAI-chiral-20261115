import YM.CF.Fixed.RiftArea

/-!
# Failure of one heat-transfer estimate, triggered by gauges IN THE ACTUAL CAP

This test is on the projection at **exactly the operator-first heat** ingredient
of `FiberAnchor`'s pointwise positivity proof. It tests the suggested strengthening
providing the inverse flight multiplier by a reflection multiplier, either a
scalar constant or reflected square depending on half-configuration or a PSD
kernel. It fails even as an *estimate of relative comparison* on FiniteGaugeData masks.

IMPORTANT NOT a counterexample to positivity or universality of normalized
readings. The test here is before integration or taking words, not an argument
against techniques with any nonpositive pointwise kernels. The weight of the
pointwise equality (`Gauge.prior` etc) still matters. Support is winding test-sector
only (operator norm); we also want application along actual x/depth.

The positivity donors use different regulators. Their estimates won't be
invalidated or refuted by this! It specifically tests an attempted transfer on
FiniteGaugeData's own layout, in the neighborhood of those proofs.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Fixed.Rift
open Function NormedSpace Matrix Lattice Finset Filter Fock BZ Mir Lat Scroll SU Bulk
open Reed.Bare Cube
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {N:Side}{u v:ℕ}{x z y:ℝ}{p:Side}
-- actual applicant
variable (P:RG.BudgetPoint)
def Loft (N:Side)(V: Bkg (More N)):= (frame matter (Cube.links V) (anticut N)).H
def Motive (N:Side)(P:RG.BudgetPoint) (f:Bkg (More N)→ℂ):Prop:= ∀ W: Fin 2→ Fin 2→ Bkg (More N), SymmetricPair W → (∀ i j:Fin 2, RG.flags P.threshold (W i j)=∅) → Matrix.PosSemidef (fun i j=> f (W i j))
/-- `C` any common normalization, can be volume-dependent. `ε C` relative tolerance
in *operator norm*. -/
def DirectT (C:ℝ) (t ε:ℝ) (f:Bkg (More N)→ℂ) := ∀ V:Bkg (More N), RG.flags P.threshold V=∅ → ‖f V • quant (grow (Loft N V) t)- (C:ℂ) • (lineOp (projector (Loft N V)))‖ ≤ C*ε
lemma line_norm (A : Op (Model N))(p:Safe A): ‖lineOp (projector A)‖=1:=by
  let V:= lineOp (projector A); have he:=line_proj p.projection; have hx: V≠0:= by intro h; have ht:V.trace=1:=line_trace p.projection; rw [h,trace_zero] at ht; exact zero_ne_one ht
  have hp:0<‖V‖:= norm_pos_iff.mpr hx; have hf: ‖V*V‖ ≤ ‖V‖* ‖V‖ := norm_mul_le ..; rw [show V*V=V from he.isIdempotentElem] at hf; apply le_antisymm (he.norm_le _); nlinarith
lemma checkpoint (A : Op (Model N))(p:Safe A)(b:ℂ)(t:ℝ)(h:‖b • quant (grow A t)- (x:ℂ) • lineOp (projector A)‖ ≤ z): ‖b*flight A t-(x:ℂ)‖≤z:=by
  let V:=lineOp (projector A); let F:=quant (grow A t); have he:=line_norm _ p; have ht:‖(b • F -(x:ℂ) • V)*V‖≤z:=by apply (norm_mul_le ..).trans; rw [show ‖V‖=1 from he,mul_one]; exact h
  rw [sub_mul,Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, show F*V=_ from line_flies p t, show V*V=V from (line_proj p.projection).isIdempotentElem,smul_smul, ←sub_smul,norm_smul,show ‖V‖=_ from he,mul_one] at ht; exact ht
lemma moth_compare (N:Side)(P:RG.BudgetPoint)(h:N.val=2*p.val)(w:1<p.val)(Y:∀ V:Bkg (More N), RG.flags P.threshold V=∅ → Safe (Loft N V))(x:ℝ)(v:0<x)(u:x≤chip)(q:2*x≤ P.threshold)(C:ℝ)(g:0<C)(f:Bkg (More N)→ℂ) (F:Motive N P f) (t:ℝ)(Ht:0<t)(hy:DirectT P C t (1/2) f) : t * hearth N x ≤ Real.log 9:=by
  let W(i j:Fin 2):= airy N (qSide x i) (qSide x j); let X(i j:Fin 2):=Loft N (W i j); let F₁(i j:Fin 2):=Real.exp (t* energy (X i j)); let A:Matrix (Fin 2) (Fin 2) ℂ:=fun i j=>f (W i j)
  have he(i j): RG.flags P.threshold (W i j)=∅:=by
    have he(k:Fin 2): |qSide x k|≤ x:=by fin_cases k<;> simp [qSide,v.le,abs_of_nonneg v.le]
    exact motion_cap _ _ (he i) (he j) P q
  have hr(i j): Safe (X i j) := Y (W i j) (he i j); have hp:= harry h w x v u (hr 0 0) (hr 0 1) (hr 1 0) (hr 1 1)
  have hv(i j:Fin 2):0 < F₁ i j:= Real.exp_pos _
  have hk(i j:Fin 2) : C/2 ≤ ‖A i j‖*(F₁ i j)∧ ‖A i j‖*(F₁ i j) ≤ 3*C/2:=by
    have ht:= checkpoint (X i j) (hr i j) (f (W i j)) t (hy (W i j) (he i j)); rw [flight_real (hr i j)] at ht
    have hx:= abs_norm_sub_norm_le (A i j*(F₁ i j:ℂ)) (C:ℂ); have heV:|‖A i j*(F₁ i j:ℂ)‖-‖(C:ℂ)‖| ≤ C*(1/2):=hx.trans ht; rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg g.le,Real.norm_of_nonneg (hv i j).le] at heV; constructor <;> linarith [abs_le.mp heV]
  have hz: F₁ 1 1 * F₁ 0 0 ≤ 9 * (F₁ 0 1*F₁ 1 0):=by
    have ht:= diag_price A (F W (team_stamp (by omega)) he)
    have ha (i:Fin 2): ‖A i i‖≤ (3*C/2)/(F₁ i i):= by apply (le_div_iff₀ (hv i i)).mpr; exact (hk i i).2
    have hh (i j:Fin 2): (C/2)/F₁ i j ≤ ‖A i j‖ := (div_le_iff₀ (hv i j)).mpr (hk i j).1
    have hm := (mul_le_mul (hh 0 1) (hh 1 0) (div_nonneg (half_pos g).le (hv 1 0).le) (norm_nonneg _)).trans (ht.trans (mul_le_mul (ha 0) (ha 1) (norm_nonneg _) (div_nonneg (by positivity) (hv 0 0).le)))
    rw [div_mul_div_comm,div_mul_div_comm (3*C/2),div_le_div_iff₀ (mul_pos (hv 0 1) (hv 1 0)) (mul_pos (hv 0 0) (hv 1 1))] at hm
    apply (mul_le_mul_iff_right₀ (show 0 < C/2*(C/2) from by positivity)).mp; nlinarith only [hm]
  rw [← Real.exp_le_exp]; apply le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp Ht.le)); unfold F₁ at hz; rw [←Real.exp_add,←Real.exp_add,←Real.exp_log (show 0<(9:ℝ) by norm_num),←Real.exp_add] at hz -- danger loop
  have hh:= Real.exp_le_exp.mp hz; apply Real.exp_le_exp.mpr
  change t*(energy (X 1 1)+energy (X 0 0)-energy (X 0 1)-energy (X 1 0))≤ _; simp only [mul_sub, mul_add]; linarith -- X defeq energy
lemma no_color(P:RG.BudgetPoint)(h:N.val=2*p.val)(w:1<p.val)(Y:∀ V:Bkg (More N), RG.flags P.threshold V=∅ → Safe (Loft N V))(x:ℝ)(v:0<x)(u:x≤chip)(q:2*x ≤ P.threshold)(t:ℝ)(Ht:0<t)(K: Real.log 9 < t*hearth N x) : ∀ (C:ℝ),0<C →∀ f:Bkg (More N)→ℂ,Motive N P f → ¬DirectT P C t (1/2) f:= fun C g f p H=>(not_le.mpr K) (moth_compare N P h w Y x v u q C g f p t Ht H)
end YM.CF.Fixed.Rift
