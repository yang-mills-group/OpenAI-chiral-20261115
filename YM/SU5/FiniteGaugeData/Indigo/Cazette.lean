import YM.SU5.FiniteGaugeData.Indigo.Obreg
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
-- real transfer.Matter.
namespace Slate
variable (g₀:0≤g)(P':Titan Λ)
variable (f: Fin (n+1)→ Trigo.Chamber true)(f':Fin (n+1)→ Trigo.Chamber false)
local notation "F₀"=> footprint f ∪ footprint f'
local notation "π"=> Base f f' Kₜ
local notation "τ"=> Vst f f' Kₜ
noncomputable abbrev LoomArea (Λ:Preparation)(l:ℕ) := (footprint f∪footprint f')∪ GridStep Λ l rayW
lemma zero_in: Λ.R.L.val • nodeC (0:Cover)∈GridStep Λ l rayW:=liner_here _ _ (mem_image_of_mem _ (mem_singleton_self _))
variable (S V:Finset Cover)(R':Patch)(ℓ:ℕ)
abbrev LeadsC(ℓ:ℕ)(a:Axis)(S T:Finset Cover):Prop:=∀ x∈S,∀ y∈T,x a+(ℓ:ℤ)<y a
/-- Ordered separation all spatial/temporal Eu axes. applied only after promoting. -/
abbrev AwayP(ℓ:ℕ)(S T:Finset Cover):Prop:= ∀ a:Axis, LeadsC ℓ a S T ∨ LeadsC ℓ a T S
lemma vacant (t:AwayP ℓ S V): Disjoint S V:= Finset.disjoint_left.mpr (fun {i} p q=> by
 rcases t (0:Axis) with h|h; · have ht:= h i p i q; omega
 have ht:= h i q i p; omega)
lemma Hlace (x:Cover)(y:Cover)(p:y∈ Halo R' x):∃ u∈ Halo R' 0, y=u+x:=by
 let U:=nodeC (specialM R'.L); obtain ⟨i,_,g⟩:= Finset.mem_biUnion.mp p; obtain ⟨t,pT,rfl⟩:=mem_image.mp g; refine ⟨t+(0+U),Finset.mem_biUnion.mpr ⟨i,mem_univ _, mem_image_of_mem _ pT⟩,?_⟩; abel
noncomputable abbrev rim (S:Finset Cover)(R':Patch)(ℓ:ℕ) := ℓ+Chrono.wall S+Chrono.wall (Halo R' 0)
lemma HorizonN(y:Cover)(p:lapse (rim S R' ℓ) y): AwayP ℓ S (Halo R' y):=by
 intro a; let Q':= rim S R' ℓ; have he:= p a; rcases (show y a < -(Q':ℤ) ∨ (Q':ℤ) < y a from by unfold day at he; simp only [mem_Icc] at he; change ¬(-(Q':ℤ)≤_ ∧ _≤ _) at he; omega) with p|p
 · right; intro i u x t; obtain ⟨j,v,rfl⟩:= Hlace R' _ _ u; simp only [Pi.add_apply]; have hc:= Chrono.wall_p _ a v; have hz:= Chrono.wall_p _ a t; unfold Q' rim at p; omega
 left; intro i z x p'; obtain ⟨j,v,rfl⟩:= Hlace R' _ _ p'; simp only [Pi.add_apply]; have hc:= Chrono.wall_p _ a v; have hz:= Chrono.wall_p _ a z; unfold Q' rim at p; omega
local notation "W₀"=> LoomArea f f' Λ l
lemma startA : InTest Kₜ false (Halo Λ.R x) false (AverPX Y h s x t q).val:=shunt_narrow ..
lemma attach : ∃ X:LinksC→ℂ,∃ y:Anorak (Halo Λ.R x) X, AverPX Y h s x t q= shunt Kₜ false X y:=⟨_,_,rfl⟩
abbrev illuminated(c:ℂ)(W:W Kₜ): Prop:=(W=Base f f' Kₜ) ∨ W=Vst f f' Kₜ ∨ W= Oir Y h K R s f f' ∨ W=plateV Y h K R f f' s c
variable {W':W (tent Y h)} (ω:ℂ)
lemma litC (p:illuminated Y h s K R f f' ω W') : Locator Kₜ W' (LoomArea f f' Λ l):=by
 let F:= (F₀); have he:Locator Kₜ (π) W₀:= ((tote f f' Kₜ subset_union_left subset_union_right : InTest Kₜ false F false (Base f f' Kₜ).val).widen.mono subset_union_left); have hx:= heatMotion Y h K R s f f'; rcases p with rfl|rfl|rfl|rfl
 · exact he
 · exact (reachC Y h f f').widen.mono subset_union_left
 · exact hx
 exact locate_scale Kₜ _ _ (locW_sub Y h _ _ _ he (locate_scale Kₜ _ _ hx))
abbrev Hℓ(u:W Kₜ)(S:Finset Cover):= ∃ p:Locator Kₜ u S, Width Kₜ u (duration S * ‖reading Kₜ S u p‖)
private lemma dieP {u:W Kₜ}(v:Locator Kₜ u S): Hℓ Y h u S:=⟨v,width_read v⟩
lemma inkCare (a:Axis)(z:ℤ)(r m:ℂ)(p:illuminated Y h s K R f f' ω W') : let S' := Halo Λ.R x; let T':= LoomArea f f' Λ l; let G':= centerK' Y h (AverPX Y h (s+1) x t q) r; let F':= centerK' Y h W' m; let P':= S'∪T'; let u:=G'*F'; Hℓ Y h G' S' ∧ Hℓ Y h F' T' ∧ Hℓ Y h u P' ∧ Hℓ Y h (fire Kₜ a z u*u) ((refract a z P')∪P'):= by
 intro S' T' G' F' P' u; have hx:Locator Kₜ G' S':=fp Y h _ _ ((startA Y h t q x (s+1)).widen) _; have ht: Locator Kₜ F' T':= fp Y h _ _ (litC Y h s K R f f' ω p) _; have hp: Locator Kₜ u P':= locate_join _ _ (locate_sub _ hx subset_union_left) (locate_sub _ ht subset_union_right); exact ⟨dieP Y h _ hx,dieP Y h _ ht,dieP Y h _ hp,dieP Y h _ (locate_join _ _ (locate_sub _ (locate_cold _ _ _ _ hp) subset_union_left) (locate_sub _ hp subset_union_right))⟩
#print axioms inkCare
end Slate
end Lychee
end Licor
end SpineV
end Succulent
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
