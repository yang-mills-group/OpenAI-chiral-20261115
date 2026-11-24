import YM.SU5.Reconstruction.Cashier.Granary
/-! Everywhere affordability of all perpendicular monitors & actual spacelike exchange. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry ConePrice Germ
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Anvil
open SelectionAnalysis
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open FirstWindows.Chambers
variable (a:Axis)(c:∀ i:Axis,Arena Y H G.history.circuit i 0 false)
variable (x:displayAlgebra Y H V G.history G.clipped a false (c a) →⋆ₐ[ℂ] ℂ)
local notation "χ₁" i:max=> displacement Y H V G.history G.clipped a false (c a) x i (c i)
local notation "R" i:max=> indoor Y H V G.history G.clipped i false (c i) (χ₁ i)
local notation "S" i:max=> fort Y H V G.history G.clipped i false (c i) (χ₁ i)
local notation "χU" i:max=> opCarries Y H V G i (c i) (χ₁ i)
local notation "L" i:max=>ride Y H V G.history G.clipped i false (c i) (χ₁ i)
open CF.Pannier.Chancel Bankroll
variable {u w q d:ℕ} (J J':ℝ)
local notation "o"=>grain (payout d q u)
local notation "Ξ"=> booty (grain (payout d q u)) d q
local notation "Ψ"=>Sen (grain (payout d q u)) (payout d q u)
local notation "Tt"=> grindscape (booty (grain (payout d q u)) d q) Ψ
local notation "Θ" s:max=>whenly (timeMesh Λ) s w
local notation "E'"=> driveAlgebra Y H V G.history G.clipped a false (c a)
variable (j:Axis)(z:SU.Slot)
local notation "ρ'" s:max=> toSkybox Y H G s
variable {Y₀: (indoor Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))).Op}
local notation "Gt"=>marks (timeMesh Λ)
local notation "Φ" i:max=> peninsula Y H V G.history G.clipped i false (c i) (χ₁ i)
-- true coverage in Common RSpace; compact cube shrink on ALL frames without analytic economy.
section ticket
variable {f:observable (tent Y H) true}{s:ℕ}
local notation "T"=>Tapestry.cabin (whenly (timeMesh Λ) s w)
lemma scintilla {S₀:Finset Cover} (v:∀ j,StampFoot Y H V s G j (c j) w S₀ f.val (1/64)) :
 (ρ' s) f∈Domain Y H G true (Tapestry.cabin (whenly (timeMesh Λ) s w)):=by
 apply ticket_mem; refine (mem_insideAt ..).2 ⟨⟨S₀,(v 0).1,(supported_iff ..).2 ?_⟩,fun _=>f.property.2 rfl⟩
 intro x p i; have ht: x∈Chambers.strip i 0 (Θ s):=(supported_iff ..).1 ((strip_seats Y H i s w).2 (v i).2.1) p
 change |x i| ≤ _; rw [abs_of_nonneg ht.1]; exact ht.2 -- rewriting order

end ticket
variable (p:Embers Y H V G a c x j z u w q d Y₀)
include p
private lemma sublimit {X: ℕ→ (R j).Op} {ψ:ℕ→ℕ} (h:Tendsto ψ atTop atTop)(v:Limited atTop X Y₀):
   Limited atTop (fun i=> (χU j) ((X∘ψ) i)) ((χU j) Y₀):= by
 obtain ⟨⟨M,g,k⟩,u⟩:=v; exact projected Y H V G j (c j) (χ₁ j) ⟨⟨M,g,h.eventually k⟩,fun x y=> (u x y).comp h⟩
lemma spark (h:0<w)(d₁:Finset Axis)(v:Gt)(c':0<(v:ℝ)) : Guarded Y H V G c a x j d₁ (fun _=>0) (fun _=>v) ((χU j) Y₀):=by
 obtain ⟨ψ,e,f,g,ζ,B,hF,hP,u',b,w'⟩:= p.price
 let k(i:ℕ):=(ρ' (ψ i)) (g i z); let A(i:ℕ):=notch (timeMesh Λ) (ψ i) w
 have hp(i):((A i):ℝ)=(Θ (ψ i):ℝ):=natural_time ..
 have ht:Tendsto (fun i=>(A i:ℝ)) atTop (𝓝 0):=by simp_rw [hp]; exact NNReal.tendsto_coe.mpr ((skinny (Λ:=Λ) w).comp hF.tendsto_atTop) -- direction?
 obtain ⟨N,u₁⟩:= eventually_atTop.mp (ht.eventually (ge_mem_nhds c')) -- Iic
 let σ(n:ℕ):= n+N; have hσ:Tendsto σ atTop atTop:=(strictMono_id.add_const N).tendsto_atTop
 refine ⟨k∘σ,A∘σ,B∘σ,⟨(fun n=> (b (σ n)).1),fun i=>?_,ht.comp hσ,sublimit Y H V G a c x j z p hσ w'⟩,fun d=>?_⟩
 · change 0< (A (σ i):ℝ); rw [hp]; exact when_pos _ _ _ h
 choose D t hz using fun i=> chooseLive Y H V G a c x (d:Axis) z (u' (σ i))
 choose M t' hf using fun i=> padding Y H V G (d:Axis) (c (d:Axis)) (χ₁ (d:Axis)) (show A (σ i) ≤ v from u₁ _ (Nat.le_add_left ..)) (t i)
 exact ⟨M,fun i=> by change Follows Y H V G (d:Axis) (c (d:Axis)) (χ₁ (d:Axis)) (FirstWindows.move (tent Y H) (eject (d:Axis) (-(0:Gt))) _) _ _; rw [neg_zero,eject_zero,move_by_zero]; exact t' i,2,fun i=> (weak_contour Y H V G (d:Axis) (c (d:Axis)) (χ₁ (d:Axis)) _).trans ((hf i).trans (harvest_price _ _ _ _ _ _ _ _ _ (hz i)))⟩
-- cp8 implies qualifiers on this test object. Entire cube `(univ\\ {j})` with true width $v>0$ in any coordinates even arbitrarily small. Show all spacelike points for them without assuming local rotation covariance.
omit p
private lemma radius (v:Gt)(p:0≤(v:ℝ))(x:Meter)(h:x∈ CubePay j (Finset.univ.erase j) (fun _=>0) (fun _=>(v:ℝ))) :‖rimPay j x‖≤ 2*(v:ℝ):=by
 have hx:0≤2*(v:ℝ):=by linarith
 apply (sq_le_sq₀ (norm_nonneg _) hx).1; rw [Anvil.rimPay_norm]
 refine (Finset.sum_le_sum (g:=fun _=>(v:ℝ)^2) ?_).trans ?_
 · intro i t; obtain ⟨h,h'⟩:=h.2 i t; apply pow_le_pow_left₀ h; simpa using h'
 rw [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ _)]; simp [Axis]; nlinarith [sq_nonneg (v:ℝ)] -- tune
variable {B:(indoor Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))).Op}
include p
lemma qualified (A: BoostBacking Y H V G c a x)(z₁:SU.Slot)(l:0<w)(h:Embers Y H V G a c x j z₁ u w q d B)(r t:Meter)(h₁:r j=0)(h₂:t j=0)(e e':ℝ)(k':|e-e'| < ‖rimPay j (t-r)‖) : Commute (sunny (Φ j) r e ((χU j) Y₀)) (sunny (Φ j) t e' ((χU j) B)) :=by
 -- buy tiny stamp; choose positive cusp within margin.
 let ψ (n:ℕ):= notch (timeMesh Λ) n w; set X:= ‖rimPay j (t-r)‖ - |e-e'|
 have hX:0<X/4:=by unfold X; linarith
 have he(n):((ψ n):ℝ)=(Θ n:ℝ):=natural_time ..
 obtain ⟨n,hn⟩:= ((NNReal.tendsto_coe.mpr (skinny (Λ:=Λ) w)).eventually (gt_mem_nhds hX)).exists -- cast zero
 let v:= ψ n; have hv:(v:ℝ)< X/4:= by unfold v; rw [he]; exact hn
 have hp:(0:ℝ)< v:= by unfold v; rw [he]; exact when_pos _ _ _ l
 let U:= Finset.univ.erase j
 refine (warrant Y H V G c a x).law A j U (Finset.notMem_erase _ _) (fun _=>0) (fun _=>v) (fun _=>0) (fun _=>v) _ _ (spark Y H V G a c x j z p l U v hp) (spark Y H V G a c x j z₁ h l U v hp) r t h₁ h₂ e e' ⟨⟨fun i _=>hp.le,fun i _=>hp.le⟩,?_⟩
 intro y d p h; set w:= d+(t-r)-y; let x:=rimPay j (t-r); have hy:x=(rimPay j w+rimPay j y)-rimPay j d:=by unfold w x; simp only [Anvil.rimPay_sub j,Anvil.rimPay_add j]; abel
 have hd:‖x‖ ≤ ‖rimPay j w‖+ 2*(v:ℝ)+2*(v:ℝ):= by
                                               conv_lhs=> rw [hy]
                                               exact (norm_sub_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add le_rfl (radius j v hp.le y p))) (radius j v hp.le d h))
 have Hz: |e-e'| < ‖rimPay j w‖:=by unfold X at hv; unfold x at hd; linarith
 rw [←sq_abs, abs_sub_comm e' e]; exact pow_lt_pow_left₀ Hz (abs_nonneg _) (by decide)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank.scintilla
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank.spark
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank.qualified
