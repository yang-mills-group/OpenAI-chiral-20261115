import GaugeFieldConstruction.WeylJets

/-! Gauge chart pivot fidelity. -/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Finset Function Complex
open scoped BigOperators
namespace Cauchy
section Gauge

def leaflet (m : Bool) (i : S3) : GJet →ₗ[ℂ] P3 := jet fun j : GIndex =>
  if m=j.1 ∧ i=j.2.val.1 then mono3 j.2.val.2 else 0

lemma catches (u : GIndex) : extr u.2.val.2 ∘ₗ leaflet u.1 u.2.val.1 = Finsupp.lapply u := by
  apply ket_ext
  intro x
  rw [LinearMap.comp_apply, leaflet, on_ket]
  change _=ket x u
  by_cases e : x=u
  · subst x; simp [ket]
  have hv : ¬(u.1=x.1 ∧ u.2.val.1=x.2.val.1 ∧ u.2.val.2=x.2.val.2) := fun h=>
    e (Prod.ext h.1 (Subtype.ext <| Prod.ext h.2.1 h.2.2)).symm
  unfold ket; split_ifs with h; swap; simp [e]
  rw [extr_mono, if_neg (fun z => hv ⟨h.1,h.2,z.symm⟩)]
  simp [e]

def component (q : Sp) (m : Bool) (x : GJet) : Sp := fun i => sample q (leaflet m i x)
lemma reserve (w : Maxwell) (q : Sp) (t : ℂ) (h : w.p=Chart.broad q t) (Y : GJet) :
    w.read Y=∑ b:Bool, ∑ i:S3,w.a b i * component q b Y i := by
  let F := ∑ b:Bool, ∑ i:S3,w.a b i • (sample q ∘ₗ leaflet b i)
  have he : w.read=F := by
    apply ket_ext
    intro j
    simp only [Maxwell.read, on_ket, F,LinearMap.sum_apply, LinearMap.smul_apply,smul_eq_mul,
      LinearMap.comp_apply, leaflet,h,Chart.broad, power]
    rw [Finset.sum_eq_single_of_mem j.1 (mem_univ _), Finset.sum_eq_single_of_mem j.2.val.1 (mem_univ _)]
    · simp [sample_mono]
    all_goals intro i _ hi; simp [hi]
  rw [he]; simp only [F,LinearMap.sum_apply, LinearMap.smul_apply,smul_eq_mul,LinearMap.comp_apply,component]

lemma last_ind (m : Bool) {q r : Sp} (a : q 0=r 0) (b : q 1=r 1) (Y : GJet) :
    component q m Y 2 = component r m Y 2 := by
  have h : sample q ∘ₗ leaflet m 2= sample r ∘ₗ leaflet m 2 := by
    apply ket_ext
    intro j
    simp only [LinearMap.comp_apply, leaflet, on_ket]; split_ifs with h
    · simp only [sample_mono,j.2.property h.2.symm,a,b,pow_zero]
    simp
  exact DFunLike.congr_fun h Y
end Gauge

namespace Chart

lemma ray_simple (flag : Bool) (s : ℂ) (E : Sp) (h : ∑ i : S3, ray flag s i * E i=0) :
    let e₁ := pay flag (E 1)
    (I*E 0 + e₁) - 2*I*E 2*s + (-(I*E 0) + e₁)*s^2=0 := by
  dsimp only
  cases flag <;> simp [ray,Fin.sum_univ_succ] at h <;> simp only [pay_false,pay_true] <;>
    linear_combination h
private lemma line_poly (a b c x y : ℂ) (h : a-c*x+b*x^2=0) (k : a-c*y+b*y^2=0) (hp : x≠y) :
    c=b*(x+y) ∧ a=b*x*y := by
  have hy : (x-y)*(c-b*(x+y))=0 := by linear_combination k-h
  have hc := sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left (sub_ne_zero.mpr hp))
  refine ⟨hc,?_⟩; rw [hc] at h; linear_combination h

private def coeff (flag : Bool) (E : Sp) := -(I*E 0) + pay flag (E 1)

private lemma rays (flag : Bool) (x y : ℂ) (E : Sp) (hp : x≠y)
    (h : ∑ i:S3, ray flag x i * E i=0) (k : ∑ i:S3, ray flag y i * E i=0) :
    let b := coeff flag E
    2*I*E 2=b*(x+y) ∧ I*E 0+pay flag (E 1)=b*x*y :=
  line_poly _ _ _ x y (ray_simple flag x E h) (ray_simple flag y E k) hp

private lemma payL (b : Bool) (c a : ℂ) : pay b (c*a)=c*pay b a := by cases b <;> simp

/-- Two different ray parameters already isolate the line. -/
private theorem compare (flag : Bool) (x y : ℂ) (E U : Sp) (p : x≠y)
    (h : ∑ i:S3, ray flag x i * U i=0) (k : ∑ i:S3, ray flag y i * U i=0)
    (r : ∑ i:S3, ray flag x i * E i=0) (s : ∑ i:S3, ray flag y i * E i=0)
    (hv : U ≠ 0) : ∃ c : ℂ, E=c • U := by
  let a := coeff flag U; let b := coeff flag E
  have e₁ : a= -(I*U 0)+pay flag (U 1) := rfl
  have e₂ : b= -(I*E 0)+pay flag (E 1) := rfl
  obtain ⟨j,l⟩ := rays flag x y U p h k; change 2*I*U 2=a*(x+y) at j; change _=a*x*y at l
  obtain ⟨m,n⟩ := rays flag x y E p r s; change 2*I*E 2=b*(x+y) at m; change _=b*x*y at n
  have ha : a≠0 := by
    intro hr
    rw [hr] at j l e₁
    simp only [zero_mul,mul_eq_zero,I_ne_zero, OfNat.ofNat_ne_zero, or_self, false_or] at j l
    have eh : U 0=0 := by
      apply (mul_eq_zero.mp (?_ : I*U 0=0)).resolve_left I_ne_zero
      linear_combination (e₁+l) / 2
    have eh' : pay flag (U 1)=0 := by linear_combination l-I*eh
    cases hu : flag <;> simp [hu] at eh' <;> apply hv <;> funext i <;>
      fin_cases i
    all_goals first | exact eh | exact eh' | exact j
  refine ⟨b/a,?_⟩
  have H0 : a * E 0 = b * U 0 := by
    apply mul_left_cancel₀ I_ne_zero
    linear_combination (a*n - b*l + a*e₂ - b*e₁) / 2
  have H1 : a * E 1 = b * U 1 := by
    have hf : a * pay flag (E 1)= b * pay flag (U 1) := by
      linear_combination a*n - b*l - I*H0
    rw [← payL, ← payL] at hf
    simpa using congr_arg (pay flag) hf
  have H2 : a * E 2 = b * U 2 := by
    apply mul_left_cancel₀ (show 2*I≠0 by simp)
    linear_combination a*m - b*j
  have he (i : S3) : a* E i=b*U i := by
    fin_cases i; exact H0; exact H1; exact H2
  funext i
  change _=b/a*U i
  field_simp
  linear_combination he i

private lemma grants (X : GJet) (h : ∀ (c : Chart) flag, c.l≠0 → (c.face flag).read X=0)
    (q : Sp) (hq : RegularQ q) (flag : Bool) :
    ∃ c:ℂ, (component q false X + pay (!flag) (component q true X)) = c • q := by
  have he (c : Chart) (t : ℂ) (hu : c.mom=broad q t) (h₁ : c.l≠0) :
      let a := if flag then c.a else c.b; let E := ray flag a
      (∑ i:S3,E i * (component q false X + pay (!flag) (component q true X)) i=0) ∧ (∑ i:S3,E i * q i=0) := by
    dsimp only
    constructor
    · have hs := h c flag h₁
      rw [reserve (c.face flag) q t hu] at hs
      apply (mul_eq_zero.mp (?_ : c.l^2*_=0)).resolve_left (pow_ne_zero _ h₁)
      rw [← hs]
      cases flag <;>
        simp [magnetic, electrical, Fin.sum_univ_succ,face] <;> ring
    apply (mul_eq_zero.mp (?_ : c.l^2*_=0)).resolve_left (pow_ne_zero _ h₁)
    have hz := c.perpendicular flag false
    rw [← hz, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [electrical,hu,spatial_broad]; ring
  obtain ⟨Y⟩ := both q hq
  obtain ⟨l,s⟩ := he Y.u Y.t Y.line Y.hl
  obtain ⟨u,v⟩ := he Y.v (-Y.t) Y.raym Y.kl
  have hd : (if flag then Y.u.a else Y.u.b) ≠ (if flag then Y.v.a else Y.v.b) := by
    cases flag; exact Y.diffB; exact Y.diffA
  apply compare flag _ _ _ _ hd s v l u
  intro e; have hp := hq.1; simp [e] at hp

lemma collinear (X : GJet) (h : ∀ (c : Chart) flag, c.l≠0 → (c.face flag).read X=0)
    (q : Sp) (hq : RegularQ q) (m : Bool) :
    ∃ c:ℂ, component q m X=c • q := by
  obtain ⟨a,t⟩ := grants X h q hq false
  obtain ⟨b,u⟩ := grants X h q hq true
  cases m
  · refine ⟨(a+b)/2,?_⟩; funext i
    have h₁ := congr_fun t i; have h₂ := congr_fun u i
    simp at h₁ h₂ ⊢; linear_combination (h₁+h₂)/2
  refine ⟨(b-a)/2,?_⟩; funext i
  have h₁ := congr_fun t i; have h₂ := congr_fun u i
  simp at h₁ h₂ ⊢; linear_combination (h₂-h₁)/2
end Chart

/-- Faithfulness also for gauge legs, paying spatial transverse jets. -/
theorem chart_Maxwell (X : GJet) (h : ∀ (c : Chart) flag, c.l≠0 → (c.face flag).read X=0) : X=0 := by
  have he (m : Bool) (i : S3) : leaflet m i X=0 := jet_view _ fun q hq H => by
    let r := update q (2:S3) 0
    have t : q 0=r 0 := (update_of_ne (by decide : (0:S3)≠2) ..).symm
    have u : q 1=r 1 := (update_of_ne (by decide : (1:S3)≠2) ..).symm
    have v : r 2=0 := update_self ..
    have hp : Chart.RegularQ r := by
      simp only [Chart.RegularQ, Chart.norm3,←t,←u,v, ne_eq, show (0:ℂ)^2 = 0 from zero_pow (by decide), add_zero]
      exact ⟨hq.1,hq.1⟩
    obtain ⟨a,j⟩ := Chart.collinear X h r hp m
    obtain ⟨b,k⟩ := Chart.collinear X h q hq m
    have hy := last_ind m t u X
    rw [j,k] at hy; simp only [Pi.smul_apply, smul_eq_mul, v,mul_zero, mul_eq_zero] at hy
    change component q m X i=0
    rw [k,hy.resolve_right H,zero_smul]; rfl
  ext1 ⟨a,z⟩
  change Finsupp.lapply (R:=ℂ) _ X=0
  rw [← catches, LinearMap.comp_apply, he,map_zero]
end Cauchy
end YM.GaugeFieldConstruction
