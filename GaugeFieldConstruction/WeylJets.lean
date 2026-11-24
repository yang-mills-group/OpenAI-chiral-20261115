import GaugeFieldConstruction.Chart
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Polynomial cost: spatial jets have faithful chart costs
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Finset Function Complex
open scoped BigOperators
namespace Cauchy
abbrev P3 := MvPolynomial S3 ℂ
def slice (n : MI) : S3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![n.1,n.2.1,n.2.2]
lemma unslice : Injective slice := by
  intro i j he; unfold slice at he
  have h := Finsupp.equivFunOnFinite.symm.injective he
  exact Prod.ext (by simpa using congr_fun h 0) (Prod.ext (by simpa using congr_fun h 1)
    (by simpa using congr_fun h 2))

def mono3 (i : MI) : P3 := MvPolynomial.monomial (slice i) 1
def sample (q : Sp) : P3 →ₗ[ℂ] ℂ := (MvPolynomial.aeval q).toLinearMap
lemma sample_eq (q : Sp) (f : P3) : sample q f=MvPolynomial.eval q f := congr_fun (MvPolynomial.aeval_eq_eval q) f
lemma sample_mono (q : Sp) (i : MI) : sample q (mono3 i)=q 0 ^ i.1 * q 1 ^ i.2.1 * q 2 ^ i.2.2 := by
  simp only [sample_eq,mono3,MvPolynomial.eval_monomial,one_mul]; rw [Finsupp.prod_fintype]; swap; simp
  simp [Fin.prod_univ_succ, mul_assoc, slice]

def extr (n : MI) : P3 →ₗ[ℂ] ℂ where
  toFun p := p.coeff (slice n)
  map_add' := by intros; simp
  map_smul' := by intros; simp
@[simp] lemma extr_mono (n m : MI) : extr n (mono3 m)=if m=n then 1 else 0 := by
  change MvPolynomial.coeff (slice n) (mono3 m) = _
  simp only [mono3, MvPolynomial.coeff_monomial, unslice.eq_iff]

/-- Reusable: functional only tested where a denominator polynomial doesn't vanish. -/
lemma guard_ext (f p : P3) {x : Sp} (he : MvPolynomial.eval x p ≠ 0)
    (h : ∀ y, MvPolynomial.eval y p ≠0 → sample y f=0) : f=0 := by
  have hh : p*f=0 := MvPolynomial.funext fun y => by
    by_cases u : MvPolynomial.eval y p=0
    · simp [u]
    simp [← sample_eq y f, h y u]
  exact (mul_eq_zero.mp hh).resolve_left (fun e=>he (by rw [e]; simp))

lemma jet_view (f : P3) (h : ∀ q, Chart.RegularQ q → q 2 ≠ 0 → sample q f=0) : f=0 := by
  let v (i : S3) := (MvPolynomial.X i : P3)
  let w := v 0^2 + v 1^2
  let p := v 2 * (w + v 2^2)*w
  apply guard_ext f p (x:=![1,0,1])
  · norm_num [p,v,w]
    rw [show (![1,0,1] (2:Fin 3) : ℂ)=1 from rfl]; norm_num
  intro y hy
  simp only [p,v,w, map_mul,map_pow,map_add, MvPolynomial.eval_X, ne_eq,mul_eq_zero,not_or] at hy
  exact h y ⟨hy.2,hy.1.2⟩ hy.1.1

section Weyl
/-- Packet in spatial Fourier variables on just one spin index. -/
def booklet (a : Spin) : CJet →ₗ[ℂ] P3 := jet fun i : FIndex => if i.1=a then mono3 i.2 else 0
lemma captures (a : Spin) (z : MI) : extr z ∘ₗ booklet a = Finsupp.lapply (a,z) := by
  apply ket_ext
  rintro ⟨b,x⟩
  rw [LinearMap.comp_apply, booklet,on_ket]
  change extr _ _=ket _ _
  by_cases h : b=a <;> simp [h,ket,Finsupp.single_apply]

lemma coupon {b : Bool} (w : Weyl b) (q : Sp) (t : ℂ) (h : w.p=Chart.broad q t) (Y : CJet) :
    w.read Y=∑ i : Spin, w.u i * sample q (booklet i Y) := by
  let F := ∑ i : Spin, w.u i • (sample q ∘ₗ booklet i)
  have he : w.read=F := by
    apply ket_ext; rintro ⟨s,n⟩
    change w.read (C s n)=_
    simp only [C, Weyl.read, on_ket,F,LinearMap.sum_apply, LinearMap.smul_apply,smul_eq_mul,
      LinearMap.comp_apply, booklet,h,Chart.broad, power]
    rw [Finset.sum_eq_single s] <;> simp [(sample_mono ..)]
    all_goals try (simp_all [ne_comm])
  rw [he]; simp only [F,LinearMap.sum_apply, LinearMap.smul_apply,smul_eq_mul,LinearMap.comp_apply]

private lemma vanished (x y u v : ℂ) (h : x ≠ y) (e : -(x*u)+v=0) (k : -(y*u)+v=0) : u=0 ∧ v=0 := by
  have hr : (x-y)*u=0 := by linear_combination k-e
  have he : u=0 := (mul_eq_zero.mp hr).resolve_left (sub_ne_zero.mpr h)
  exact ⟨he,by simpa [he] using e⟩

/-- The exact tests of `RankSupplement`: no loss computing Weyl ranks
on the spatial jet basis. Don't presume any reader at degree six or higher. -/
theorem chart_Weyl (b : Bool) (X : CJet) (h : ∀ c : Chart,c.l≠0 → (c.fermi b).read X=0) : X=0 := by
  have prices (i : Spin) : booklet i X=0 := jet_view _ fun q hq _ => by
    obtain ⟨A⟩ := Chart.both q hq
    have u := h A.u A.hl
    have v := h A.v A.kl
    rw [coupon _ _ _ A.line] at u; rw [coupon _ _ _ A.raym] at v
    simp only [Chart.fermi, Chart.pol, Fin.sum_univ_succ
      ] at u v
    let Z (i : Spin) := sample q (booklet i X)
    have hv : Z 0=0 ∧ Z 1=0 := by
      cases b
      · simp at u v; exact vanished _ _ _ _ A.diffA u v
      simp at u v; exact vanished _ _ _ _ A.diffB u v
    fin_cases i
    · exact hv.1
    exact hv.2
  ext1 ⟨a,z⟩
  change Finsupp.lapply (R:=ℂ) _ X=0
  rw [← captures, LinearMap.comp_apply, prices,map_zero]
end Weyl
end Cauchy
end YM.GaugeFieldConstruction
