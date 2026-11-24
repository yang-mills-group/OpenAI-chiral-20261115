import YM.CF.Pastry.Sheet
import YM.CF.Support.Fleet

/-! Time-variable support bill for boundary exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pastry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Finset NormedSpace Petal Branch Tour Tour.Enters
attribute [local instance] opCStarAlgebra
variable {Z : Type*} {y : Tour Z} {s t : ChartW y} {A B : MapW y}
lemma ardeo (p : ample y) (h : Enters y s s A) (e : ∀ z x, Safe (A z x)) : ∃ a k w : ℝ, 0<a ∧ 0<k ∧ k<1 ∧ 0<w ∧ ∀ v:ℝ,∀ n:ℕ,n≤v→v≤n+1→∀ z, RootedK (s z) (s z) a (w*k^n) (fun x=> decay (A z x) v) := by
  let P : MapW y:= fun z x=> monad (A z x)
  have he : Enters y s s P := h.join (hood p h e)
  obtain ⟨d,K,H,L,W⟩:= he
  let F := fun n:ℕ=> ‖((n.factorial:ℂ)⁻¹)‖ * (Real.exp d * (2*K)^n)
  let V := ∑' i:ℕ,F i
  have hv : 0≤V := tsum_nonneg (fun i=> by unfold F; positivity)
  have hf (i : ℝ) (l : ‖i‖≤1) (z:Z) : RootedK (s z) (s z) d V (fun x=>decay (A z x) i) := by
    have hx (x) : (-i:ℂ) • P z x= (-i:ℝ) • P z x := by ext g w; simp [Complex.real_smul]
    have ht := (W z).raise (-i:ℂ); simp_rw [hx] at ht
    refine RootedK.wind H.le ?_ L.le; exact ht.books (by rw [norm_neg,Complex.norm_real]; exact mul_le_of_le_one_left L.le l)
  obtain ⟨a,k,m,p,h,g,c,X⟩:= drift_steps p h e
  refine ⟨min d a,k,2*(m*(V+1)),lt_min H p,h,g,by positivity,?_⟩; intro v n q u z
  let t := v-n
  have he : ‖t‖ ≤ 1 := by unfold t; rw [Real.norm_of_nonneg (by linarith)]; linarith
  have hk x : decay (A z x) v=decay (A z x) n * decay (A z x) t := by
    let B := monad (A z x)
    unfold decay grow
    letI : NormedAlgebra ℚ (Op (y.I z)):= NormedAlgebra.restrictScalars ℚ ℂ (Op (y.I z))
    rw [←exp_add_of_commute]; swap
    · exact ((Commute.refl B).smul_left (_:ℝ)).smul_right _
    rw [←add_smul]; congr 2; unfold t; ring
  simp_rw [hk]; apply (((X z n).drop (le_of_eq (show min d a=min d a from rfl)|>.trans (min_le_right d a))).product ((hf t he z).drop (min_le_left ..)) (le_min H.le p.le)).books
  have he : V≤V+1 := by linarith
  calc 2*(m*k^n*V) ≤ 2*(m*k^n*(V+1)) := by gcongr
       _ = _ := by ring
lemma wing (p : ample y) (h : Enters y s s A) (e : Enters y s (Tour.partner s) B) (g : ∀ z x, Safe (A z x)) (w : ∀ z x, ‖stage (projector (A z x)) (B z x)- B z x‖ ≤ 1/3) (f : ∀ z x, B z x∈unitary _) : ∃ a q K : ℝ, 0<a ∧ 0<q ∧ q<1 ∧ 0<K ∧ ∀ t:ℝ,∀ n:ℕ,n≤t→t≤n+1→∀ z, let i : (y.MapW) := fun z x => decay (A z x) t; let P : y.MapW := fun z x=>projector (A z x); let c := K*q^n;
    RootedK (Tour.partner s z) (s z) a c (fun x => Kcc (i z x) (reserve (P z x) (B z x))) ∧
    RootedK (Tour.partner s z) (Tour.partner s z) a c (fun x => Kcg (i z x) (driftB (P z x) (B z x))) ∧
    RootedK (s z) (Tour.partner s z) a c (fun x => Kgg (i z x) (weldB (P z x) (B z x))) := by
  obtain ⟨a,q,m,H,hq,hv,hM,X⟩ := ardeo p h g
  obtain ⟨⟨a₁,k₁,p₁,v₁,L₁⟩,⟨a₂,k₂,p₂,v₂,L₂⟩,⟨a₃,k₃,p₃,v₃,L₃⟩⟩ := coeff_main p h e g w f
  let d := min a (min a₁ (min a₂ a₃)); have hd : 0<d := by simp [d,H,p₁,p₂,p₃]
  let K := k₁+k₂+k₃; have hk : 0<K := by unfold K; positivity
  refine ⟨d,q*q,4*(m*K*m),hd,mul_pos hq hq,(by nlinarith),by positivity,?_⟩
  intro t n hr V z J R c
  have hi : RootedK (s z) (s z) d (m*q^n) (J z) := (X t n hr V z).drop (min_le_left ..)
  have hh i (t:i≤K) : 2*(2*(m*q^n*i)*(m*q^n)) ≤ c := by
    unfold c; rw [mul_pow]
    calc _ ≤ 2*(2*(m*q^n*K)*(m*q^n)) := by gcongr
         _ = _ := by ring
  have hx (x) : (J z x)ᵀ=star (cc (J z x)) := by rw [← cc_star,cc,star_star]
  refine ⟨?_,?_,?_⟩
  · unfold Kcc; simp_rw [ccT]; exact (((hi.ccUp.product ((L₁ z).drop (le_trans (min_le_right ..) (min_le_left ..))) hd.le).product hi.starUp hd.le).books (hh _ (by unfold K; linarith)))
  · unfold Kcg; simp_rw [hx]; exact (((hi.ccUp.product ((L₂ z).drop (le_trans (min_le_right ..) (le_trans (min_le_right ..) (min_le_left ..)))) hd.le).product hi.ccUp.starUp hd.le).books (hh _ (by unfold K; linarith)))
  unfold Kgg; simp_rw [hx]; exact (((hi.product ((L₃ z).drop (le_trans (min_le_right ..) (le_trans (min_le_right ..) (min_le_right ..)))) hd.le).product hi.ccUp.starUp hd.le).books (hh _ (by unfold K; linarith)))
end YM.CF.Pastry
