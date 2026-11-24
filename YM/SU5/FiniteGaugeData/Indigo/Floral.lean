import YM.SU5.FiniteGaugeData.Indigo.Noyer
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Eight
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ: Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{I:ℕ→ Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E){P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)
variable (A:∀ i:Axis, Repertory Y h K R i)
open Hills Tint
variable (S T:Finset Cover)(s i k:ℕ) {g α C D ε θ C₀:ℝ}
local notation "Kₜ"=> tent Y h
local notation "N"=> side Y i s
local notation "U"=> W (tent Y h)
local notation "Ω"=> (Y.voyage i).CapeT s
local notation "E₁"=> W (tent Y h)→ₗ[ℂ]ℂ
variable {a:Axis}{d w n m:ℕ}{x f:W (tent Y h)}{vD:Axis→ℕ}(L:Master Y s i)(lP:Club Y g s)

namespace Bonbon
open Steam.Indigo
variable (Z:Finset (Face ℤ)) (C':ℝ) (p q j:ℕ) (f: W (tent Y h))
local notation "L"=> swatch Y h s Z
abbrev grainW (n:ℕ):ℝ := (↑(n+1:ℕ):ℝ)^p * Real.exp (-(n:ℝ))
abbrev tailW (n:ℕ) := ∑' i:ℕ, grainW p (i+n)
local notation "τₚ"=> tailW p
private lemma hol_p : Summable (grainW p):=by
 let f(n:ℕ):= (n:ℝ)^p* Real.exp (-(1:ℝ)*n); have he:Summable f:= Real.summable_pow_mul_exp_neg_nat_mul p (by norm_num:(0:ℝ)<1); apply ((he.comp_injective (i:=fun k:ℕ=>k+1) (fun i j h=> Nat.succ_inj.mp h)).mul_right (Real.exp 1)).congr; intro i; unfold grainW Function.comp f; rw [mul_assoc, ← Real.exp_add]; push_cast; ring_nf
private lemma warm_p(k:ℕ): 0 ≤ grainW p k:=by unfold grainW; positivity
lemma tail_C : 0≤ tailW p q:= tsum_nonneg fun _=>warm_p ..
lemma tail_B : Tendsto (tailW p) atTop (𝓝 0):= tendsto_sum_nat_add (grainW p) -- order
lemma tail_R : tailW p q= grainW p q+ tailW p (q+1):=by
 let f:=grainW p; let g(n:ℕ):= f (n+q); have he:Summable g:=(summable_nat_add_iff q).2 (hol_p p); change ∑' i,g i=_; rw [he.tsum_eq_zero_add]; unfold tailW; congr 1; · unfold g; rw [Nat.zero_add]
 apply tsum_congr; intro i; change f (i+1+q)= f (i+(q+1)); congr 1; omega
variable (u':Locator (tent Y h) f S)(v':carpet Z⊆S)
local notation "Wₗ"=> wageZ Λ h Y S g
include u' v'
lemma tail_loc : Locator Kₜ ( (L q)* f) S:= locate_join Kₜ S (turfS Y h S s Z q v') u'
lemma normLoc : Locator Kₜ (insideM Y h s Z q f) S:= locate_join Kₜ S (locW_sub Y h S 1 _ (locate_one ..) (turfS Y h S s Z q v')) u'
variable (σ:Tulle Y h s Z p C f) (g':0≤g) (Φ:ℕ→W (tent Y h)→ₗ[ℂ]ℂ)(e:Sphere Y h K R A Φ)
include σ g' e lP
lemma farAge : ‖Φ s ( (swatch Y h s Z q) * f)‖ ≤ C*(τₚ q) * wageZ Λ h Y S g:=by
 let E(r:ℕ):=Φ s ( (L r)*f); let T:=tailW p; have h₁:=σ.zeroB; have h₂:0 ≤ wageZ Λ h Y S g:=(Real.exp_pos _).le; obtain ⟨n,t,q'⟩:= ((plenty Y h s Z).and (eventually_ge_atTop q)).exists; have he:E n=0:=by unfold E; rw [swatchZ Y h s Z n t,zero_mul,map_zero]
 have hy(i j:ℕ)(t:i+j=n) : ‖E i‖ ≤ C*T i*Wₗ:= by
    induction j generalizing i with
    | zero=> rw [Nat.add_zero] at t; have z:= tail_C p n; rw [t,he,norm_zero]; exact mul_nonneg (mul_nonneg h₁ z) h₂
    | succ j ih=>
       let b:=i+1; let H:= insideM Y h s Z b f; let F' := Φ s ( (L i)*H); have hF: E i= F'+ E b := by unfold E; nth_rw 1 [faithful Y h s Z f i]; rw [map_add]
       rw [hF,show T i= _ from tail_R p i]; apply (norm_add_le ..).trans; apply (add_le_add (b:=C*grainW p i* Wₗ) (?_) (ih b (by unfold b; omega))).trans_eq; · ring
       let v₀:=costZ Y h K R A S s lP Z Φ v' i (Nat.cast_nonneg _) (show 0≤C*(b:ℝ)^p from mul_nonneg h₁ (by positivity)) g' e H (normLoc Y h S s Z b f u' v') (innerP Y h s Z p f σ b (Nat.zero_lt_succ i)); exact v₀.trans_eq (by unfold grainW; unfold b; ring)
 obtain ⟨m,h⟩:= Nat.exists_eq_add_of_le q'; exact hy q m h.symm
#print axioms tail_R
#print axioms farAge
end Bonbon
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
