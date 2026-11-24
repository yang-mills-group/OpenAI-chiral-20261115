import YM.CF.Support.Tour

/-! Uniform data costs in the integer-time boundary regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter NormedSpace
attribute [local instance] opCStarAlgebra
lemma grow_nat {I : Type*} [Fintype I] [DecidableEq I] (A : Op I) (n : ℕ) : grow A (-(n:ℝ))=grow A (-1) ^ n := by
  letI : NormedAlgebra ℚ (Op I) := NormedAlgebra.restrictScalars ℚ ℂ (Op I)
  rw [grow, grow,←exp_nsmul]; congr 1; simp only [neg_smul,one_smul,smul_neg,Nat.cast_smul_eq_nsmul] -- tune
namespace Tour
variable {Z : Type*} {y : Tour Z} {s t : ChartW y} {A B V : MapW y}
namespace Enters
lemma drift_steps (p : ample y) (h : Enters y s s A) (e : ∀ z x, Safe (A z x)) :
    ∃ a q m : ℝ, 0<a ∧ 0<q ∧ q<1 ∧ 0<m ∧ ∀ z i, RootedK (s z) (s z) a (m*q^i) (fun x=> decay (A z x) (i:ℕ)) := by
  let V : MapW y := fun z x=> decay (A z x) 1
  have he : Enters y s s V := ((h.join (hood p h e)).scaleR (-1)).fans
  let r := Real.exp (-1/2); have hp : 0<r := Real.exp_pos _; have hh : r<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  obtain ⟨a,q,m,g,t,l,w,N⟩ := orderV p he r hp hh fun z x=> slows (e z x) 1 zero_le_one
  exact ⟨a,q,m,g,t,l,w,fun z i=> by unfold decay; simp_rw [grow_nat]; exact N z i⟩
lemma stageLn (h : Enters y s s A) (e : Enters y s (partner s) B) (f : ∀ z x, IsStarProjection (A z x))
    (t : ∀ z x, ‖(body (A z x) (B z x)*star (body (A z x) (B z x))+(1-A z x))-1‖ ≤ 7/9) (p : ample y) :
    Enters y s s (fun z x=> pencil ((body (A z x) (B z x)*star (body (A z x) (B z x))+(1-A z x))-1)) := by
  let T : MapW y := fun z x=> (body (A z x) (B z x)*star (body (A z x) (B z x))+(1-A z x))-1
  have he : Enters y s s T := ((((h.bodyV e).join (h.bodyV e).starL).plus ((identity s).sub h)).sub (identity s))
  exact scrolled p he _ (show 0<(7:ℝ)/9 by norm_num) (by norm_num) t
-- kernels for comparisons
lemma relayLn (h : Enters y s s A) (e : Enters y s (partner s) B) (g : Enters y s (partner s) V) (q : ∀ z x, ‖stage (A z x) (B z x)-B z x‖≤1/3) (w : ∀ z x,B z x∈unitary _)
    (H : ∀ z x, ‖relay (A z x) (B z x) (V z x)-1‖≤1/2) (p : ample y) :
    Enters y s s (fun z x=> pencil (relay (A z x) (B z x) (V z x)-1)) := by
  let T : MapW y := fun z x=> relay (A z x) (B z x) (V z x)-1
  have he : Enters y s s T := ((((h.bodyV g).join (stageI p h e q w)).plus ((identity s).sub h)).sub (identity s))
  exact scrolled p he _ (show 0<(1:ℝ)/2 by norm_num) (by norm_num) H
end Enters

section launch
variable (p : ample y) (h : Enters y s s A) (e : Enters y s (partner s) B) (g : ∀ z x, Safe (A z x)) (w : ∀ z x, ‖stage (projector (A z x)) (B z x)- B z x‖ ≤ 1/3) (f : ∀ z x, B z x∈unitary _)
lemma coeff_main (p : ample y) (h : Enters y s s A) (e : Enters y s (partner s) B) (g : ∀ z x, Safe (A z x)) (w : ∀ z x, ‖stage (projector (A z x)) (B z x)- B z x‖ ≤ 1/3) (f : ∀ z x, B z x∈unitary _) :
    let P := fun z x=> projector (A z x)
    Enters y (partner s) s (fun z x=>reserve (P z x) (B z x)) ∧ Enters y (partner s) (partner s) (fun z x=>driftB (P z x) (B z x)) ∧
    Enters y s (partner s) (fun z x=>weldB (P z x) (B z x)) := by
  intro P; let Q : MapW y := fun z x=>1-P z x
  have he : Enters y s s P := Enters.site p h g
  have hp : Enters y s s Q := (Enters.identity _).sub he
  have ht : Enters y (partner s) s (fun z x=>reserve (P z x) (B z x)) := (Enters.stageI p he e w f).join he
  exact ⟨ht,((ht.join e).join hp.ccL).neg, (hp.join (e.sub ((e.join ht).join e))).join hp.ccL⟩
include p h e g w f
abbrev Kcc {I : Type*} [Fintype I] [DecidableEq I] (Y A : Op I) := cc Y*A*(cc Y)ᵀ
abbrev Kcg {I : Type*} [Fintype I] [DecidableEq I] (Y A : Op I) := cc Y*A*Yᵀ
abbrev Kgg {I : Type*} [Fintype I] [DecidableEq I] (Y A : Op I) := Y*A*Yᵀ
lemma tendX : ∃ a q K : ℝ, 0<a ∧ 0<q ∧ q<1 ∧ 0<K ∧ ∀ z n, let i : (y.MapW) := fun z x => decay (A z x) (n:ℕ); let P : y.MapW := fun z x=>projector (A z x); let c := K*q^n;
    RootedK (partner s z) (s z) a c (fun x => Kcc (i z x) (reserve (P z x) (B z x))) ∧
    RootedK (partner s z) (partner s z) a c (fun x => Kcg (i z x) (driftB (P z x) (B z x))) ∧
    RootedK (s z) (partner s z) a c (fun x => Kgg (i z x) (weldB (P z x) (B z x))) := by
  obtain ⟨a,q,m,H,hq,hv,hM,X⟩ := Enters.drift_steps p h g
  obtain ⟨⟨a₁,k₁,p₁,v₁,L₁⟩,⟨a₂,k₂,p₂,v₂,L₂⟩,⟨a₃,k₃,p₃,v₃,L₃⟩⟩ := coeff_main p h e g w f
  let d := min a (min a₁ (min a₂ a₃)); have hd : 0<d := by simp [d,H,p₁,p₂,p₃]
  let K := k₁+k₂+k₃; have hk : 0<K := by unfold K; positivity
  refine ⟨d,q*q,4*(m*K*m),hd,mul_pos hq hq,(by nlinarith),by positivity,?_⟩
  intro z n J R c
  have hi : RootedK (s z) (s z) d (m*q^n) (J z) := (X z n).drop (min_le_left ..)
  have hh i (t:i≤K) : 2*(2*(m*q^n*i)*(m*q^n)) ≤ c := by
    unfold c; rw [mul_pow]
    calc _ ≤ 2*(2*(m*q^n*K)*(m*q^n)) := by gcongr
         _ = _ := by ring
  have hx (x) : (J z x)ᵀ=star (cc (J z x)) := by rw [← cc_star,cc,star_star]
  refine ⟨?_,?_,?_⟩
  · unfold Kcc; simp_rw [ccT]; exact (((hi.ccUp.product ((L₁ z).drop (le_trans (min_le_right ..) (min_le_left ..))) hd.le).product hi.starUp hd.le).books (hh _ (by unfold K; linarith)))
  · unfold Kcg; simp_rw [hx]; exact (((hi.ccUp.product ((L₂ z).drop (le_trans (min_le_right ..) (le_trans (min_le_right ..) (min_le_left ..)))) hd.le).product hi.ccUp.starUp hd.le).books (hh _ (by unfold K; linarith)))
  unfold Kgg; simp_rw [hx]; exact (((hi.product ((L₃ z).drop (le_trans (min_le_right ..) (le_trans (min_le_right ..) (min_le_right ..)))) hd.le).product hi.ccUp.starUp hd.le).books (hh _ (by unfold K; linarith)))
end launch
end Tour
end YM.CF.Branch
