import YM.SU5.FiniteGaugeData.Indigo.Cazette
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
/-! # WP31. ALL-budget independence violation — matter-only lens recipe vs LINK-only lens; strictly separated supports after promotion too. -/
local notation "P₀"=> Oir Y h K R s f f'
local notation "W₀"=> LoomArea f f' Λ l
noncomputable abbrev together(s:ℕ)(e:W Kₜ→ₗ[ℂ]ℂ)(v w: W Kₜ):= centerK' Y h v (e v)*centerK' Y h w (e w)
lemma orientP (v:W Kₜ→ₗ[ℂ]ℂ)(p:v 1=1)(x y:W Kₜ): v (together Y h s v x y)=Beacon Y h v x y:=by
 unfold together centerK' Beacon; simp only [_root_.mul_sub,_root_.sub_mul, Algebra.mul_smul_comm,Algebra.smul_mul_assoc, one_mul,mul_one,map_sub,map_smul,p,smul_eq_mul]; ring
lemma crosstalk (ω:ℂ)(φ:W Kₜ→ₗ[ℂ]ℂ)(G':W Kₜ)(hv: Beacon Y h φ G' (plateV Y h K R f f' s ω)≠0) : ∃ u:W Kₜ, (u=π∨u=P₀)∧ Beacon Y h φ G' u≠0:=by
 by_contra! p; let M:= levyP Λ (s+1); let d:= ω⁻¹; let B:=Beacon Y h φ G'; apply hv; rw [show plateV _ _ _ _ _ _ _ ω=((M:ℂ)) • (π - d •P₀) from rfl]; change B (((M:ℂ)) • _) = _; have hs(z:W Kₜ)(t:ℂ): B (t • z)= t*B z:=by unfold B Beacon; rw [Algebra.mul_smul_comm,map_smul,map_smul]; simp only [smul_eq_mul]; ring
 rw [hs,show B (π-d • P₀)=B π - B (d • P₀) from (by unfold B Beacon; rw [_root_.mul_sub,map_sub,map_sub]; ring), hs]; rw [show B π=0 from p (π) (Or.inl rfl),show B P₀=0 from p P₀ (Or.inr rfl)]; ring
structure Loans (ω:ℂ)(b:ℝ) (G':W (tent Y h))(s:ℕ)(φ:W (tent Y h)→ₗ[ℂ]ℂ): Prop where
 illuminatedC: φ (Base f f' Kₜ) ≠0
 farR : b≤ ‖Beacon Y h φ G' (plateV Y h K R f f' s ω)‖
 reflectsL : b ≤ ‖ φ (together Y h (s+1) φ G' (plateV Y h K R f f' s ω))‖ -- remove space at end
 grantD : ∃ u:W (tent Y h), (u=Base f f' Kₜ ∨ u= Oir Y h K R s f f') ∧ Beacon Y h φ G' u≠0 ∧ φ (together Y h (s+1) φ G' u)≠0
structure Dams (S:Finset Cover)(ω:ℕ→ℂ)(f:Fin (n+1)→ Trigo.Chamber true)(f':Fin (n+1)→ Trigo.Chamber false):Prop where
 fullU: f 0= starlit (specialM Λ.R.L)
 fullD: f' 0= reedW (specialM Λ.R.L)
 fullRank: Injective f∧ Injective f'
 credit: (TaxR Trigo.levy f f').det ≠0
 reachX:Rack true (reamW Λ.R (aliasLaw Λ)∪ S) f ∧ Rack false (reamW Λ.R (aliasLaw Λ)∪S) f'
 acquiresU: (∀ s:ℕ,ω s≠0)
 holds:∀ ℓ:ℕ,∃ (c:ℝ),0<c∧∃ D:ℕ, ∀ᶠ t:ℝ in 𝓝[>] 0,∀ q:0<t, ∀ᶠ s:ℕ in atTop,∃ x∈ marketZ D,
    lapse ℓ x∧ AwayP ℓ (LoomArea f f' Λ l) (Halo Λ.R x) ∧ Locator Kₜ (AverPX Y h (s+1) x t q) (Halo Λ.R x)∧ Width Kₜ (AverPX Y h (s+1) x t q) t⁻¹∧ Locator Kₜ (plateV Y h K R f f' s (ω s)) (LoomArea f f' Λ l)∧
    ∀ Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ, Sphere Y h K R A Φ → Loans Y h K R f f' (ω s) c (AverPX Y h (s+1) x t q) s (Φ (s+1))
include H K R A P' g₀
/-- Existence of local separated readings in an *already* terminal vacuum hierarchy. -/
theorem indigo (S:Finset Cover): ∃ (n:ℕ)(f:Fin (n+1)→ Trigo.Chamber true)(f':Fin (n+1)→ Trigo.Chamber false)(ξ:ℕ→ℂ), Dams Y h K R A S ξ f f':=by
 obtain ⟨n,f,g',p,q,a,b,hp⟩:= Laug (starlit (specialM Λ.R.L)) (reedW (specialM Λ.R.L)) (reamW Λ.R (aliasLaw Λ)∪ S); let Y':= TicketL Trigo.levy f g' hp
 obtain ⟨ξ,e,P⟩:=oxygen Y H h K R A g₀ P' f g' (fun x z=>a (show x∈_ from (mem_union_left _ z:nodeC x.1∈reamW Λ.R (aliasLaw Λ)∪ S))) (fun x z=>b (show x∈_ from (mem_union_left _ z:nodeC x.1∈reamW Λ.R (aliasLaw Λ)∪ S))) p q hp
 refine ⟨n,f,g',ξ,p,q,Y',hp,⟨a,b⟩,e,?_⟩; intro ℓ; let Z:= LoomArea f g' Λ l; let d:= rim Z Λ.R ℓ; obtain ⟨c,u,D,hT⟩:= P d; refine ⟨c,u,D,?_⟩; have hx: day ℓ ⊆ day d := Icc_subset_Icc (show -(d:ℤ) ≤ -(ℓ:ℤ) from (by unfold d rim; omega)) (show (ℓ:ℤ)≤ d from (by unfold d rim; omega)) -- retro parser.Day.
 filter_upwards [hT] with t T Ht; filter_upwards [T Ht,(tendsto_add_atTop_nat 1).eventually (motionQ Y f g' h K R A H P' hp)] with s t' x; obtain ⟨i,g,y,t₁⟩:=t'; refine ⟨i,g, fun i h=> y _ (hx h), HorizonN Z _ ℓ _ y, HaloL .., vaultL Λ.R i t Ht _ _, litC Y h s K R f g' (ξ s) (Or.inr (Or.inr (Or.inr rfl))), fun Φ hQ=>?_⟩
 let U':= Φ (s+1); let G':= AverPX Y h (s+1) i t Ht; let W':= plateV Y h K R f g' s (ξ s); obtain ⟨b,u₀,u₁⟩:= crosstalk Y h s K R f g' (ξ s) U' G' (norm_pos_iff.mp (lt_of_lt_of_le u (t₁ Φ hQ))); refine ⟨x Φ hQ, t₁ Φ hQ,(by rw [orientP _ _ _ _ (hQ.living _)]; exact t₁ Φ hQ),b,u₀,u₁,?_⟩; rw [orientP _ _ _ _ (hQ.living _)]; exact u₁
#print axioms indigo
end Slate
end Lychee
end Licor
end SpineV
end Succulent
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
