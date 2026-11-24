import YM.SU5.FiniteGaugeData.Jadot.Ergo
import YM.SU5.FiniteGaugeData.Jadot.Contract
import YM.SU5.FiniteGaugeData.CodaT.Ladders
/-! # Common Picture Universe estimate: reserve μ and linked era.
 Permission required when changing d,p (width, heights...). Instances later.
 -/
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
variable (h:Real.exp 1≤Λ.x) (s i k:ℕ) {S:Finset Cover}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ} (K:Universal Y h u v I E)
variable {P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h K R a)
local notation "Kₜ"=>tent Y h
local notation "Ψ" s:max i:max => side Y i s   -- swapped!
local notation "Φx" s:max i:max k:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable {n m d w j ℓ:ℕ}{p C Y0 r t b u' ε δ θ μ e a G σ α ξ Q γ A₀ P₀:ℝ}
variable (S':RadioCity.Hypothesis Λ l g Y)(P':Titan Λ)
local notation "€"=> Rhythm.Dolores.charge Λ
local notation "ρψ" n:max m:max=> (spar Λ.K.j m (1:Pane n))
private def glow{m':Side}{U:Op (Single m')}(vF:Fable U (tickA m'))(n d w j:ℕ)(v b c ξ G α K:ℝ): Contract m' where
 art:= Flush U n d w j v K b c ξ G α
 unit:=Flush.unit
 enlarge{S T n x} h p:= Flush.expand h p
 both{S T n m x y} h p t:=Flush.both h p t
 turn a z {S f i} h:=Flush.flipL h vF a z
abbrev Franch (P:Op (Single (side Y i s)))(n d w j:ℕ)(t b c ξ G α:ℝ)(m:ℕ)(S:Finset Cover)(f:W (tent Y h)):= Flush P n d w j t (Rhythm.Dolores.charge Λ) b c ξ G α m (region S (side Y i s)) (sold Y h s i f.val)
include S' P' K R A
lemma candlesV (e:Permit Λ w j ε δ u') (t':0<t)(s':0≤γ)(a':0< a)(hμ:0<μ)(eμ:μ ≤1)(h':μ≤u')(p':4*a+markV (MajorH Λ) μ ≤ θ)(h0:0≤ θ)(z:P₀+θ*pushH S Kₜ ≤0)(hC:0≤ C)(t0:0<b):
 ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop, let m_:=side Y (u i) s; let M:=((Φx s (u i) (v k))).J.M; let U:= ρψ m_ M; Fable U (tickA m_) ∧(∃ X Y:Op (Single m_),Cream U (tickA m_) (€) u' ε δ w j X Y) ∧
 forall (a ξ c α:ℝ),0≤c→ Burn α ξ c (€) a ε δ n w ≤ P₀→ forall(f:W Kₜ)(g:Locator (tent Y h) f S), (∀ z, ‖sold Y h s (u i) f.val z‖≤ C)→ Franch Y h s (u i) U n d w j t a c ξ γ α 1 S f → forall Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ,Sphere Y h K R A Φ→ ‖Φ s f‖≤1+b:=by
 let C₀:=Real.exp P₀; have hc:C₀*Real.exp (θ*pushH S Kₜ) ≤1:=by unfold C₀; rw [←Real.exp_add]; exact (Real.exp_monotone z).trans_eq Real.exp_zero
 filter_upwards [revenueH (l':=n) (j:=d) Y S' P' e t' s' a' hμ eμ h' p',horizon_any Y e] with s y B
 filter_upwards [cashCpp Y h K R A S s 3 (fun i=> ⟨_,spread_film i⟩) hC (Real.exp_pos P₀).le t0 h0 hc] with i g0; filter_upwards [g0,K.pick.pass Y h s (u i)] with k eP vT; intro m' M H; obtain ⟨q,P⟩:= B (u i) (v k) vT.enters M; refine ⟨q,P,?_⟩; intro a ξ c α hK O f g kT F Φ X; let N:= glow q n d w j t a c ξ γ α (€); apply eP N f g kT F _ Φ X
 intro U r x t; exact (y (u i) (v k) vT.depth vT.enters α ξ c a hK U r x t).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_monotone O) r) (Real.exp_pos _).le)
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
