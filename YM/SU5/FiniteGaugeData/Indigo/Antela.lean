import YM.SU5.FiniteGaugeData.Indigo.Taboret
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
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
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
namespace Succulent
open Strata
open CF.Indigo
namespace SpineV
open YM.SU5.FiniteGaugeData.Lapis Lumi
open LapisS LapisS.Stadium
open Chiffon.Prato
open YM.SU5.FiniteGaugeData.Indigo Taper
open Fock
namespace Licor
namespace Lychee
open Tint Eight.Bonbon
open YM.SU5.FiniteGaugeData.LapisQ WinkQ Exterior Work.F03 Cordon
open LapisS.ArenaQ
variable (H:RadioCity.Hypothesis Λ l g Y) (h:Real.exp 1 ≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "Q"=> wageL Λ
local notation "U"=>4*wageL Λ
local notation "η"=> nodeC (specialM Λ.R.L)
local notation "Πx"=> μX Λ
local notation "ν"=> zoomP Λ
local notation "ρ"=> WideLake Λ
local notation "Γ"=> cradle Λ.R
variable (t:ℝ)(q:0<t)(x:Cover)(s i k:ℕ){p b C ε c:ℝ}
local notation "W₁" => Charm.W (tent Y h)
local notation "Σ"=> AverPX Y h s x t q
local notation "Ψ"=> Snear Y h s t q
local notation "G"=> SU.group
local notation "A₁"=> ace (Λ:=Λ) s Kₜ
local notation "J"=> Jeanne (Λ:=Λ) s Kₜ
variable {I:ℕ→ Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E){P:Call Λ l}{Jk:Wicket Λ l}(R:Rolled Y h u v Jk P)(A:∀ i:Axis, Repertory Y h K R i)
local notation "B₁"=> Beacon Y h
local notation "Xλ"=> HomeX (Λ:=Λ) x
open TulleV
local notation "ρE" => estate h Y (HomeX (Λ:=Λ) x) g
local notation "RX"=> regnal Λ l Y h g x
variable (g₀:0≤g)(d₁:∀ᶠ s:ℕ in atTop, Club Y g s)
variable {S:Finset Cover} (F:W Kₜ) -- use for width_pack
local notation "β"=> wageZ Λ h Y S g
lemma trial_H : Tendsto (regnal Λ l Y h g x) (𝓝[>] 0) (𝓝 0):=by
 let f(z):= regnal Λ l Y h g x z; have hp:Continuous f:=by unfold f regnal TulleV.estate; fun_prop
 exact ( hp.tendsto' 0 0 (by unfold f regnal; simp only [TulleV.estate,zero_mul,add_zero,mul_zero])).mono_left nhdsWithin_le_nhds
include K R A g₀ d₁
lemma payday (z:WideLake Λ⊆ S)(e₁:0 ≤ C)(X:0<ε): ∀ᶠ s:ℕ in atTop,∀ (f:W (tent Y h)), Width (tent Y h) f C → Locator (tent Y h) f S →∀ (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ→ ‖Φ s ( f * ((ace (Λ:=Λ) s Kₜ) - Jeanne (Λ:=Λ) s Kₜ))‖ ≤ ε:=by
 obtain ⟨c,u,v'⟩:= Atlas Y h; let w₀:= C*(c+ (4*wageL Λ)^2); let a:=wageZ Λ h Y S g; let D₀:= a*C; let f(t:ℕ):=w₀* tailW 2 t*a; let e:= ε/2; have he:0< e:= half_pos X; have hD:0 < D₀+1:=add_pos_of_nonneg_of_pos (mul_nonneg (Real.exp_pos _).le e₁) zero_lt_one
 have hx:Tendsto f atTop (𝓝 0):=by simpa only [mul_zero,zero_mul] using! (((tail_B 2).const_mul w₀).mul_const a)
 obtain ⟨t,v,q⟩:= ((hx.eventually (ge_mem_nhds he)).and (eventually_gt_atTop 0)).exists; let p:=e/(D₀+1); have hv:0<p:= div_pos he hD; filter_upwards [ASAP Y h hv t q,d₁] with s x y f₁ j g' Φ r; let Z:=  (ace (Λ:=Λ) s Kₜ)- Jeanne (Λ:=Λ) s Kₜ; let X:= swatch Y h s (Γ) t; let F:= f₁*Z; let Y':= insideM Y h s (Γ) t Z; have hz: Locator Kₜ Z S:=locate_sub _ (locW_sub Y h _ _ _ (Aloc Y h s) (Jloc Y h s)) z; have hC:carpet (Γ) ⊆ S:= Subset.trans subset_union_right z; have he:‖Φ s (X*F)‖ ≤ e := (farAge Y h K R A S s y (Γ) 2 t F (locate_join Kₜ _ g' hz) hC (show Tulle Y h s (Γ) 2 w₀ F from (mul₁ Y h s _ (sup₁ Y h s _ e₁ j) (subtion Y h s (Γ) (v' s) (July Y h s)))) g₀ Φ r).trans v
 have hx:‖Φ s ( f₁*Y')‖ ≤ e:= (Eight.Bonbon.income Y h K R A S s y Φ (mul_nonneg e₁ hv.le) g₀ r _ (locate_join Kₜ _ g' (normLoc Y h S s _ t Z hz hC)) (show Width Kₜ (f₁*Y') (C*p) from (fun i=> RealWidth.mule (j i) (x i)))).trans (?_); swap; · refine (le_trans (le_of_eq (show C*p*(β)=D₀ * p from (by unfold D₀ a; ring))) ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hv.le).trans_eq (by unfold p; field_simp))) -- clear div.Power issue.$Tule mul.X_
 have hh: F= f₁* Y' + X*F:=by nth_rw 1 [show F=f₁*Z from rfl, dusk Y h s _ t Z]; rw [mul_add]; change f₁*Y'+f₁*(X*Z)=_; rw [←mul_assoc f₁ X, show f₁* X= X * f₁ from (Raw_comm Kₜ X f₁ (RawG.swath Y h s (Γ) _)).symm, mul_assoc X]; -- tune orientation lemma.Work.
 change ‖Φ s F‖≤_; rw [hh,map_add]; exact (norm_add_le ..).trans ((add_le_add hx he).trans_eq (add_halves ..))
lemma costδ₂ (e:0<ε): ∀ᶠ s:ℕ in atTop,∀ (Φ:ℕ→W (tent Y h)→ₗ[ℂ]ℂ),Sphere Y h K R A Φ→ ‖Beacon Y h (Φ s) (AverPX Y h s x t q) (ace (Λ:=Λ) s Kₜ) -Beacon Y h (Φ s) (AverPX Y h s x t q) (Jeanne (Λ:=Λ) s Kₜ)‖ ≤ ε:=by
 let y:= ρE 2 (wageL Λ^2); have hv:0≤y:= amountE Y h ( (Q)^2) (sq_nonneg _) Xλ 2 g; let a:= ε/(1+y); have ha:0<1+y:=add_pos_of_pos_of_nonneg zero_lt_one hv; have he:0<a:= div_pos e ha; filter_upwards [payday Y h K R A g₀ d₁ (waterD (Λ:=Λ) x) (inv_pos.mpr q).le he, payday Y h K R A g₀ d₁ (S:=ρ) (Subset.refl _) zero_le_one he,d₁] with s H V p Φ hR; let X:= AverPX Y h s x t q; let Z:=Φ s; let L:=  (ace (Λ:=Λ) s Kₜ)- Jeanne (Λ:=Λ) s Kₜ; have ht: ‖Z L‖ ≤ a:=by rw [← one_mul (L)]; exact V 1 (fun i _ =>norm_one.le) (locate_one ..) Φ hR -- locate_one
 have hp:= launchE Y h t q x s K R A g₀ p Φ hR; have hz: ‖Z (X*L)‖ ≤ a:= H X (vaultL Λ.R x t q Kₜ _) (shore Y h t q x s) Φ hR
 rw [show B₁ Z X (ace (Λ:=Λ) s Kₜ)-B₁ Z X (Jeanne (Λ:=Λ) s Kₜ)=B₁ Z X L from (by unfold Beacon L; rw [_root_.mul_sub,map_sub,map_sub]; ring)]; calc
    _ ≤ a + y*a:= (norm_sub_le ..).trans (add_le_add hz ((norm_mul ..).trans_le (mul_le_mul hp ht (norm_nonneg _) hv))) -- expose Beacon defeq?
    _ = _:= by rw [show a+y*a=a*(1+y) from (by ring)]; unfold a; field_simp
-- combine high-resolution gauge warmth.Y budget universal ∀ Φ. Costs stable later.L.P.
include H
lemma portionGl (ℓ:ℕ): ∃ c:ℝ,0<c∧ ∃ D:ℕ, ∀ᶠ t:ℝ in 𝓝[>] 0,∀ q:0<t, ∀ᶠ s:ℕ in atTop,∃ x∈ marketZ D, lapse ℓ x ∧ ∀(Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ → c≤ (Beacon Y h (Φ s) (AverPX Y h s x t q) (ace (Λ:=Λ) s Kₜ)).re:=by
 obtain ⟨c,d,cP,dP,A',C⟩:= glitter Y H h K R A ℓ; let e:= c/4; have he: 0<e:=by unfold e; positivity
 let V:= marketZ A'; refine ⟨e,he,A',?_⟩; filter_upwards [V.eventually_all.mpr (fun i _=> (trial_H (g:=g) Y h i).eventually (ge_mem_nhds he)),(nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0) (ge_mem_nhds dP)] with t w hY q; filter_upwards [C t q hY, V.eventually_all.mpr (fun i _=> costδ₂ Y h t q i K R A g₀ d₁ he),d₁] with s v χ f; obtain ⟨x,u,v,z⟩:= v; refine ⟨x,u,v,fun Φ y=>?_⟩; let B:=fun F=> B₁ (Φ s) ( AverPX Y h s x t q) F; let V':= B (Snear Y h s t q); have hv: c≤ V'.re:= z Φ y; let G':= B (Jeanne (Λ:=Λ) s Kₜ); let J':= B (ace (Λ:=Λ) s Kₜ); have hx: |(V'- G').re| ≤ e:= (Complex.abs_re_le_norm _).trans ((costδ₁ Y h t q x s K R A g₀ f Φ y).trans (w x u)); have hh: |(J'- G').re|≤ e:= (Complex.abs_re_le_norm _).trans (χ _ u Φ y); rw [Complex.sub_re] at hx hh; change e ≤ J'.re; linarith only [(abs_le.mp hx).2,(abs_le.mp hh).1,hv,(show c=4*e from (by unfold e; ring)),he]
#print axioms portionGl
end Lychee
end Licor
end SpineV
end Succulent
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
