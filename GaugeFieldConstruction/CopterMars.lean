import GaugeFieldConstruction.LunulaMars
import GaugeFieldConstruction.DryLeafMars
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Set Filter MeasureTheory Measure Complex Analysis Points Bulb
open scoped ContDiff Topology BigOperators
variable {n:ℕ}
section Even
universe u
-- recursion accepted by quant at same universe
lemma PodKDMars (U:Set (Points n))(u:IsOpen U) (L:Set E4)(l:IsCompact L)(m:ℕ):
    ∀ {E: Type u} [NormedAddCommGroup E] [NormedSpace ℝ E][CompleteSpace E]
    (F:E4× Points n→ E)(e:∀ x∈U,∀ y:E4, y∉L→F (y,x)=0), (∀ x∈U,∀ y,ContDiffAt ℝ ∞ F (y,x))→ContDiffOn ℝ (↑m) (WrapMars F) U:=by
 induction m with
 | zero=>
    intro E _ _ _ F e h; simp only[Nat.cast_zero,contDiffOn_zero]; exact fun i j=> ((inventoryMars F U u L l h e i j).continuousAt).continuousWithinAt
 | succ m hs=>
    intro E _ _ _ F e h; push_cast; refine (contDiffOn_succ_iff_fderiv_of_isOpen u).mpr ⟨fun x hx=>(inventoryMars F U u L l h e x hx).hasFDerivWithinAt.differentiableWithinAt,(by simp),?_⟩
    exact (hs (CPderMars F) (CPSellMars F U u L h e) (CPSmoothMars F U u h)).congr fun x hx=> (inventoryMars F U u L l h e x hx).fderiv -- order tune
lemma PodDPMars (F:Points (n+1)→ℂ)(hf:ContDiffOn ℝ ∞ F (conf _))(b:Bulb)(k:Fin n)(a i:Axis)(K:Payroll n) : ContDiffOn ℝ ∞ (RyeMars F K b a i) {x|BreatherMars b k x} :=by
 apply contDiffOn_infty.mpr; exact fun m=>PodKDMars _ (BreathingMars b k) _ (LED b a).c m _ (fun x hx y Y=> SoilAreaMars _ _ _ _ _ _ Y _) (fun x hx y=>SoilCapMars F hf K b a i x k hx y)
end Even
abbrev CurlMars (n:ℕ):= Fin n×Axis
def FingerMars (v:CurlMars n):= direction v.1 v.2
section
variable {G : Type*}[NormedAddCommGroup G]
-- common capped logic not using Supplies
def CaporMars (F:Points n→ G):Prop:= ∃ C:ℝ,∃ m:ℕ,0 ≤ C  ∧ ∀ r:ℝ,0< r → r ≤ 1 → ∀ x:Points n,spaced r x→ ‖F x‖≤ C*r⁻¹^m
variable {T:Type*}
lemma aggDMars (K : Finset T)(F:T→ Points n→ G)(h:∀ i∈K,CaporMars (F i)):∃ A:ℝ,∃ m:ℕ,0≤A ∧ ∀ r:ℝ,0< r → r ≤ 1 → ∀ x:Points n,spaced r x→ ∑ i∈K,‖F i x‖ ≤ A*r⁻¹^m:=by
 classical
 induction K using Finset.induction_on with
 | empty => exact ⟨0,0,le_rfl,fun _ _ _ _ _=>by simp⟩
 | insert a K ha hs=>
    obtain ⟨A,m,hA,H⟩:=hs (fun i hi=>h i (Finset.mem_insert_of_mem hi)); obtain ⟨B,k,hB,V⟩:= h a (Finset.mem_insert_self ..)
    refine ⟨B+A,max k m,add_nonneg hB hA, fun r hy hv x hx=>?_⟩
    rw [Finset.sum_insert ha,add_mul]; have hi: 1≤r⁻¹:= one_le_inv₀ hy |>.mpr hv -- tune
    exact add_le_add ((V r hy hv x hx).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hi (le_max_left ..)) hB)) ((H r hy hv x hx).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hi (le_max_right ..)) hA))
variable [NormedSpace ℝ G]
private lemma curve_baseMars (x:Points n)(i:Fin n)(a: Axis):‖x i a‖ ≤ ‖x‖:= le_trans (PiLp.norm_apply_le ..) (PiLp.norm_apply_le ..)
lemma fullPaintMars (x:Points n): x=∑ i:CurlMars n, (x i.1 i.2) • FingerMars i:=by
 apply flatten.injective; simp only[_root_.map_sum,map_smul]; ext1 j; obtain ⟨s,t⟩:=j
 rw [WithLp.ofLp_sum, Finset.sum_apply]; symm
 rw [Finset.sum_eq_single (s,t)]
 · simp [FingerMars, direction, PiLp.single_apply]
 · rintro ⟨a,b⟩ hi hv; simp [FingerMars,direction,PiLp.single_apply] -- tune
   by_cases h:a=s
   · subst a; have he:b≠t:=fun k=> hv (by rw [k])
     simp [Ne.symm he]
   simp [Ne.symm h]
 · simp
lemma frameDMars {m:ℕ}(F:ContinuousMultilinearMap ℝ (fun _:Fin m=> Points n) G) :
    ‖F‖ ≤ ∑ i:Fin m → CurlMars n, ‖F (FingerMars ∘ i)‖:=by
 let S:=∑ i:Fin m→ CurlMars n, ‖F (FingerMars ∘ i)‖
 refine F.opNorm_le_bound (Finset.sum_nonneg (fun i _=>norm_nonneg _)) (fun x=>?_)
 let p (j: Fin m)(i:CurlMars n):=x j i.1 i.2
 let g (j :Fin m)(i:CurlMars n):=p j i • FingerMars i
 conv_lhs=> rw [show x=(fun j=>∑ i:CurlMars n,g j i) from funext fun j=>fullPaintMars _]
 rw[F.map_sum] -- tune names
 refine le_trans (norm_sum_le ..) ?_
 rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro i hi
 rw [show F (fun j=>g j (i j))=(∏ j,p j (i j)) • F (FingerMars ∘ i) from ?_, norm_smul,Real.norm_eq_abs,Finset.abs_prod] -- abs name tune
 · rw [mul_comm]; exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=>abs_nonneg _) (fun j _=>curve_baseMars ..)) (norm_nonneg _)
 exact F.map_smul_univ ..
lemma frameCapMars {m:ℕ}(F:Points n→ G)(h:∀ i:Fin m→ CurlMars n,CaporMars (fun x=>iteratedFDeriv ℝ m F x (FingerMars ∘ i))):CaporMars (iteratedFDeriv ℝ m F):=by
 obtain ⟨A,m',hA,H⟩:= aggDMars _ _ (fun i (_ : i∈(Finset.univ:Finset (Fin m→CurlMars n)))=>h i)
 exact ⟨A,m',hA,fun x u v s Y=> (frameDMars _).trans (H x u v s Y)⟩
end
#print axioms frameDMars
end YM.GaugeFieldConstruction.Fathom
