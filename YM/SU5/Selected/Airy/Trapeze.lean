import YM.SU5.Selected.Airy.Walk
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
local instance : Fact (0<φ):= ⟨piRank⟩
local notation "ρ" => Real.exp (-(1/2))
def tier (p: Side):roundC:= ↑(φ/(p.val:ℝ))
-- use integer grid D in fermion units. AP signs only for fermion. notation D
variable (D: Side) (w:roundC)
local notation "N"=>D.val
local notation "u"=> tier D
def avg (w:roundC)(D:Side)(f: roundC→ℂ):= (↑D.val:ℂ)⁻¹*∑ i∈ range D.val,f (w+i • tier D)
lemma mon_add (i:ℤ)(w x:roundC): fourier i (w+x)= fourier i w*fourier i x:=by simp only [fourier_apply,zsmul_add,AddCircle.toCircle_add,Circle.coe_mul]
lemma mon_walk (i:ℤ)(w:roundC)(s:ℕ): fourier i (s • w)= fourier i w^s:=by induction s with| zero=> rw [zero_smul,pow_zero,fourier_eval_zero] | succ s ih=> rw [add_smul,one_smul,mon_add,ih,pow_succ]
lemma mon_quit (i:ℤ) : avg w D (fourier i)= if (N:ℤ)∣i then fourier i w else 0:=by
 have hh:addOrderOf u=N:= AddCircle.addOrderOf_period_div (p:=2 * π) D.2
 have hp: N • u=0:= by have h:= addOrderOf_nsmul_eq_zero u; rwa [hh] at h
 have h₀:fourier i u=1 ↔ (N:ℤ)∣i:= by
    rw [←hh,addOrderOf_dvd_iff_zsmul_eq_zero, fourier_apply, ← show (↑(AddCircle.toCircle (0:roundC)):ℂ)=1 from (by simp : (@AddCircle.toCircle (2*π) 0:ℂ)=1)]
    exact Iff.trans Subtype.coe_inj (Injective.eq_iff (AddCircle.injective_toCircle piRank.ne'))
 unfold avg; simp_rw [mon_add,mon_walk,←mul_sum]; by_cases v: (N:ℤ) ∣ i
 · have he:=side_ne D; simp [v,h₀.mpr v, -fourier_apply,smul_eq_mul]; field_simp
 rw [geom_sum_eq (mt h₀.mp v), ←mon_walk,hp,fourier_eval_zero]; simp [v]
lemma dibble (i:ℤ)(x:Facet3)(p:x∈grounds):
 HasSum (fun j:ℤ=> if (N:ℤ)∣ j-i then embark x j * fourier (j-i) w else 0) (avg w D (fun t=> fourier (-i) t*slopeG x t)):=by
 let f (j:ℕ):= w+j • u;
 let z(k:ℕ)(j:ℤ):= embark x j*fourier (j-i) (f k)
 have hp(v:ℕ): HasSum (z v) (fourier (-i) (f v)*slopeG x (f v)):=by
    apply (Airy.paint p (f v)).mul_left (fourier (-i) (f v)) |>.congr_fun; intro i; unfold z; rw [sub_eq_add_neg,fourier_add]; ring
 apply HasSum.congr_fun ((hasSum_sum (s:=range N) (f:=z) (fun b _=> hp b)).mul_left ((N:ℂ)⁻¹)); intro j; unfold z; simp only [Finset.sum_apply, ←Finset.mul_sum]; rw [mul_left_comm, show (↑(N):ℂ)⁻¹*(∑ k∈_, fourier (j-i) (f k))= avg w D (fourier (j-i)) from rfl, mon_quit]; split <;> simp_all -- tune
-- key price order all fixed i: O(exp(-D/2)), not losing any transverse volume! can increase block separation D to dwarf inverse cost while keeping density N/D.
lemma tone_die : ρ<1:= Real.exp_lt_one_iff.mpr (by norm_num)
private lemma fares (i:ℤ) : ∃ C:ℝ,0<C∧∀ (j:ℤ), (Real.exp (-1))^j.natAbs ≤ C*ρ^(j-i).natAbs * ρ^j.natAbs:=by
 let A:= ρ; have hp:0< A:= by unfold A; positivity
 have ht(j:ℤ): (j-i).natAbs ≤ j.natAbs+i.natAbs:=by omega
 have hk : Real.exp (-1)=A*A:= by unfold A; rw [←Real.exp_add]; congr 1; norm_num
 refine ⟨(A^i.natAbs)⁻¹,inv_pos.mpr (pow_pos hp _),fun j=>?_⟩; rw [hk,mul_pow]; refine mul_le_mul_of_nonneg_right ?_ (pow_pos hp _).le; rw [mul_comm (A^_)⁻¹, ←div_eq_mul_inv]; exact (le_div_iff₀ (pow_pos hp _)).mpr (by rw [←pow_add]; exact pow_le_pow_of_le_one hp.le tone_die.le (ht j))
lemma fares_all (i:ℤ) : ∃ K:ℝ,0<K∧ ∀ D:Side,∀ w:roundC,∀ x∈grounds, ‖avg w D (fun t=> fourier (-i) t*slopeG x t)-embark x i‖ ≤ K * ρ^D.val :=by -- notation macro N binds D?
 obtain ⟨C,hC,v⟩:= dominates; obtain ⟨B,hB,e⟩:= fares i
 let S(j:ℤ):= ρ^j.natAbs; let b:= ∑' j,S j; have hg:= bleeds (Real.exp_pos _|>.le) tone_die; have hk(j:ℤ) : 0<S j:= by unfold S; positivity
 refine ⟨C*B*b, mul_pos (mul_pos hC hB) (hg.tsum_pos (fun i=> (hk i).le) 0 (hk 0)),fun D w x c=>?_⟩
 let U(j:ℤ):= if (D.val:ℤ)∣ j-i then embark x j * fourier (j-i) w else 0
 have h:HasSum U (avg w D (fun t=> fourier (-i) t*slopeG x t)):= dibble D w i x c; have hp:= h.sub (hasSum_pi_single i (embark x i));
 let s:= C*B*ρ^D.val; have ht(j:ℤ) : ‖U j - (Pi.single i (embark x i):ℤ→ℂ) j‖ ≤ s * S j:=by
    by_cases k:j=i; · subst j; simp only [U,sub_self, dvd_zero, ↓reduceIte, fourier_zero, mul_one, Pi.single_eq_same, norm_zero]; unfold s S; positivity -- tune
    rw [Pi.single_eq_of_ne k,sub_zero]; unfold U; split
    next z =>
        have hj:D.val≤(j-i).natAbs:= Nat.le_of_dvd (Int.natAbs_pos.mpr (sub_ne_zero.mpr k)) (by simpa using Int.natAbs_dvd_natAbs.mpr z) -- name
        rw [norm_mul,fourier_apply,Circle.norm_coe,mul_one]; apply (v x c j).trans; apply ((mul_le_mul_of_nonneg_left (e j) hC.le)).trans; unfold S s; rw [←mul_assoc, ←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) tone_die.le hj) (by positivity)) (by positivity)
    rw [norm_zero]; unfold s S; positivity
 calc
  _ ≤ ∑' j:ℤ, ‖U j - (Pi.single i (embark x i):ℤ→ℂ) j‖ := by rw [← hp.tsum_eq]; exact norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun i=> norm_nonneg _) ht (hg.mul_left s)) -- tune
  _ ≤ s*b:= hasSum_le ht hp.summable.norm.hasSum (hg.hasSum.mul_left s)
  _ = _ := by unfold s; ring
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms dibble
#print axioms fares_all
