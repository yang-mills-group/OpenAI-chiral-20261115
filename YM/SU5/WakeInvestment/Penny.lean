import YM.SU5.WakeInvestment.Tilt

/-!
Replace the split into high/low momentum at WA.11 by truncation of the *shear* (while keeping
exact, normalized shear in the actual spin test). Need recovery rate polynomial with
explicit powers in the tilt budget. Need it even on V transformed letters in the Wake price.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.WakeInvestment
open Function Set Filter Metric NormedSpace Fock Finset Lattice Laurent Bloch Lat BPress.Spin.Blank Cube Rush SU Fir Ember Scroll Tulip Fixed.Extensive Dial Tenant
open Papyrus Papyrus.Franc
open Crest.Sleet
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I] [Fintype I]
variable {A P:Op I}
variable {N:Side}{M:Tulip.Male}{j k:ℕ}
local notation "R" => spar j M (1:Bkg (More N))
local notation "Ω" => angle true
local notation "F" => bent true j M.val
local notation "Z" => zTar j M

private lemma gram_anti (f g:Op I) (a:ℝ) (_:0≤a)(b:‖f‖≤a)(q:‖g‖ ≤1) : ‖f*g‖≤a :=
  (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) q).trans b)

lemma counting_Comb [Nonempty I](p:IsStarProjection P)(a:IsStarProjection A)(k:ℕ) : ‖Comb A P k‖ ≤ k := by
  induction k with
  | zero => simp [Comb]
  | succ k ih =>
    have he : 0 ≤ P*A*P := (star_mul_self_nonneg (A*P)).trans_eq (by
      rw [star_mul,p.isSelfAdjoint,a.isSelfAdjoint, ←mul_assoc, mul_assoc P A A, a.isIdempotentElem.eq])
    have hk : ‖1-P*A*P‖ ≤ 1 := by
      have hf : P*A*P ≤ 1 := ((CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one he).mp
        (gram_anti _ P 1 zero_le_one (gram_anti P A 1 zero_le_one (p.norm_le _) (a.norm_le _)) (p.norm_le _))).trans_eq (map_one _)
      rw [CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one (sub_nonneg.mpr hf), map_one]; exact sub_le_self _ he
    rw [Comb, Nat.cast_succ, add_comm (k:ℝ)]
    exact (norm_add_le ..).trans (add_le_add (gram_anti _ P 1 zero_le_one (gram_anti (1-P) A 1 zero_le_one (p.one_sub.norm_le _) (a.norm_le _)) (p.norm_le _)) (gram_anti _ _ _ (Nat.cast_nonneg _) ih hk))

lemma counting_Saber [Nonempty I](p:IsStarProjection P)(a:IsStarProjection A)(k:ℕ) :
    let W := Saber (B:=A) p k; ‖W.sell‖ ≤ 1+(k:ℝ) ∧ ‖W.buy‖ ≤ 1+(k:ℝ) := by
  let B:=star (Comb A P k); intro w
  have h:‖B‖ ≤ k:= (norm_star ..).trans_le (counting_Comb p a _)
  exact ⟨(norm_add_le 1 B).trans (add_le_add norm_one.le h), (norm_sub_le 1 B).trans (add_le_add norm_one.le h)⟩

private lemma tail_one (k:ℕ) (z:ℝ) (_:0 ≤ z)(v:z≤1) :
    (1-z)^k*(1+k*z) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ, mul_assoc]; apply le_trans _ ih
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
    nlinarith only [sq_nonneg z, mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (sq_nonneg z)]

lemma stint_size (k:ℕ) (r z : ℝ) (h:r>0) (u:0<z)(v:z≤1)(hr:1 ≤ (k:ℝ)*r^2) :
    (1-z)^k * Real.sqrt z ≤ r := by
  have hh:= tail_one k z u.le v
  let t:=(1-z)^k; let R':=Real.sqrt z
  have hx: 0 ≤ t:= pow_nonneg (by linarith only [v]) _; have ht:t ≤ 1:= pow_le_one₀ (by linarith only [v]) (by linarith)
  have he' : 0 < (k:ℝ) := pos_of_mul_pos_left (zero_lt_one.trans_le hr) (sq_nonneg r)
  apply le_of_pow_le_pow_left₀ (n:=2) (by decide) h.le; rw [mul_pow,Real.sq_sqrt u.le]; change t^2*z ≤ _
  apply le_of_mul_le_mul_left _ he'; change _* (t^2*z) ≤ _
  apply le_trans _ hr
  have hw : (k:ℝ) * (t*z) ≤ 1 := by nlinarith only [hh,hx] -- unify
  nlinarith only [mul_le_mul_of_nonneg_left hw hx,ht]

-- extract internal criterion from proof of Pincer.net_c
private abbrev glitz {I:Type*}[LinearOrder I][Fintype I](b:Bool)(P:Op I):Op I:=if b then star P else P
private lemma hoe (C:ℝ) (Q:Momentum→Op SpinIdx)(b:Bool)(t:∑ i:Site N, ‖Q (mel i)‖^2 ≤ C*N.val^4)(i:Single N): ‖acts (glitz b (lens Q N)) (basisKet i)‖^2 ≤ C:=by
 obtain ⟨⟨x,i⟩,j⟩:=i; let G(p:Momentum):=glitz b (Q p); have hh(y):‖G y‖= ‖Q y‖:=by unfold G glitz; cases b; rfl; exact norm_star _
 rw [show glitz b (lens Q N)= lens G N from ?_]; swap; · cases b; rfl; exact l_star _
 rw [spice]; apply (mul_le_mul_of_nonneg_left (le_trans (sum_le_sum (g:=fun i=> ‖Q (mel i)‖^2) (fun i h=>?_)) t) (by positivity)).trans_eq (by field_simp [nPos N|>.ne'])
 apply pow_le_pow_left₀ (norm_nonneg _); rw [←hh]; apply (ContinuousLinearMap.le_opNorm _ _).trans; unfold acts; rw [Matrix.l2_opNorm_toEuclideanCLM]; simp [basisKet]
lemma actual_sums (j:ℕ)(h:1 ≤ j) : ∃ C:ℝ,0<C∧ ∀ (ε:ℝ) (k:ℕ),
      0<ε → 1 ≤ (k:ℝ)*(ε^2/C)^2 → ∀ (N:Side) (M:Tulip.Male), IsStarProjection (spar j M (1:Bkg (More N)))→∀ v:ℕ, k ≤ v →∀ i:Single N,
      let X:=Comb (tickA N) (spar j M (1:Bkg (More N)))
      ‖acts (X v-X k) (basisKet i)‖ ≤ ε ∧ ‖acts (star (X v-X k)) (basisKet i)‖ ≤ ε:=by
 obtain ⟨C,t,u⟩:=bills j h
 refine ⟨C,t,fun ε k p hKc N M p' v a i=>?_⟩
 let q:=ε^2/C; have hh:0<q:=by unfold q; positivity
 have hq:=hh
 intro X; let G(p:Momentum):=Comb (angle true) (bent true j M.val p) v-Comb (angle true) (bent true j M.val p) k
 have hx:X v-X k=lens G N:=by unfold X; rw [angledK h,angledK h,l_sub]
 have he: ∑ i:Site N, ‖G (mel i)‖^2 ≤ ε^2 * N.val^4:=by
    apply (sum_le_sum (g:=fun i=> q*(hard (zTar j M i))⁻¹) (fun i h'=>?_)).trans (le_trans (show _≤q*(C*N.val^4) by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (u N M) hh.le) (le_of_eq (by unfold q; field_simp)))
    let z:=zTar j M i; let W:= Real.sqrt z; let d:=(1-z)^k; have ht:0<z:=amp j h _ i; have hv:=z_cap h p' i
    have hd:0≤d:=pow_nonneg (sub_nonneg.mpr hv) _; have hy:d≤1:=pow_le_one₀ (sub_nonneg.mpr hv) (by linarith)
    have hl:d*W ≤ q:=stint_size k q z hq ht hv hKc; have hh:0<W:=Real.sqrt_pos.mpr ht
    apply (pow_le_pow_left₀ (norm_nonneg _) (zGap h p' i k v a) _).trans; change (d*W⁻¹)^2 ≤ q*(W^3)⁻¹; field_simp; nlinarith only [mul_le_mul_of_nonneg_right hy (show 0≤d*W by positivity),hl]
 exact ⟨le_of_pow_le_pow_left₀ (by decide) p.le (hx.symm ▸ hoe _ _ false he i), le_of_pow_le_pow_left₀ (by decide) p.le (hx.symm ▸ hoe _ _ true he i)⟩

/-- Cost for Wake Bessel pricing. Critical: station estimate **uniform in volumes** with a
quantified number of terms k, also as the exact tilt is varied. -/
lemma approximate_saber (j:ℕ)(h:1 ≤ j) : ∃ C:ℝ,0<C∧ ∀ (ε:ℝ) (k:ℕ),
      0<ε → 1 ≤ (k:ℝ)*(ε^2/C)^2 → ∀ (N:Side) (M:Tulip.Male) (p:IsStarProjection (spar j M (1:Bkg (More N)))),
         let e:=shear h p; let f:=Saber p (B:=tickA N) k
         ColumnDeal (e.sell-f.sell) ε ∧ ColumnDeal (star e.buy - star f.buy) ε := by
 obtain ⟨C,hC,H⟩:=actual_sums j h; refine ⟨C,hC,fun ε k he hp N M p=>?_⟩; intro e f
 let P:=spar j M (1:Bkg (More N)); let X:=Comb (tickA N) P; let h0:= H ε k he hp N M p
 have ht(i:Single N) (K: ℕ→Op (Single N))(A:Op (Single N))(hT:Tendsto K atTop (𝓝 A))(w:∀ᶠ k:ℕ in atTop, ‖acts (K k) (basisKet i)‖ ≤ ε):‖acts A (basisKet i)‖≤ε:=by
    have g : Continuous (fun P:Op (Single N) => acts P (basisKet i)) := acts_cont.clm_apply continuous_const; exact le_of_tendsto ((g.continuousAt.tendsto.comp hT).norm) w
 let E:=spineJet h p
 have hw:e.sell-f.sell=star (E-X k):=by
     change 1+star E - (1+star (X k))= _; rw [star_sub]; abel
 have hx:star e.buy - star f.buy= -(E-X k):=by
     change star (1-star E)-star (1-star (X k))=_; simp only [star_sub,star_star]; abel
 rw [hw,hx]
 constructor
 · constructor; intro i; exact ht i _ _ (( (pad_jet h p).sub_const (X k)).star) ((eventually_ge_atTop k).mono (fun v w=> (h0 v w i).2))
 constructor; intro i; rw [act_neg,norm_neg]; exact ht i _ _ ((pad_jet h p).sub_const (X k)) ((eventually_ge_atTop k).mono (fun v w=> (h0 v w i).1))

#print axioms approximate_saber
end YM.CF.WakeInvestment
