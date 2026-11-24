import YM.CF.Vp929.Match.Page
import YM.CF.Vp929.Pre.Ambit
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}{a b c d C r:ℝ}[Nonempty (Haro.ΘS r)]
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial Haro
namespace MatchW
open Py.Rate Haro Cadre Wray Larch Ione
open Push.AbsoluteSums Haro Glyph Trees
open scoped Mew
local notation "Qu"=> Tenant.quota^2
variable (T S:BeatL n) {p:BudgetPoint}{v W e:ℝ}{B:ℕ}{L:Scree.Loom n}
open Technique
variable {T S} (Ω:Technique p W e d B L T S a b c r)
namespace Technique
local notation "Xp"=> Ω.note + Ω.note
local notation "Kr"=> Rinse (Seat n) (Copy n)
local notation "Er"=> ΘS r
local notation "λχ" i:max=> Ω.bond.litB Ω.H Ω.pay W Ω.floor Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize i
local notation "πχ"=> Pair (ΘS r)
local notation "I_"=> Complex.I
variable {Wk f m₁ m₂ u0 Λ ψ δ θ x g γΓ θΓ dΓ vδ r₁ s:ℝ}
local notation "Pk"=> cap1 p (BondL.øK r) W
local notation "VK"=> Vow.Cusp n
local notation "Θp"=> Py.Mood p (512*Wk) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r s m₁ m₂ u0 vδ r₁ Λ ψ θ δ γΓ θΓ dΓ
variable (Th: Py.Mood p (512*Wk) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r s m₁ m₂ u0 vδ r₁ Λ ψ θ δ γΓ θΓ dΓ)
local notation "opV" I:max k:max=> Timer (Cadre.chip (cribR (Ω.note+Ω.note)) I) (Ω.note+Ω.note) r₁ (wu p) wΨ (widthK n p.B) (spanV p.B) γΓ dΓ (spanV p.B*dΓ) dΓ k (Ω.note+Ω.note)
def Billable (p:BudgetPoint)(W:ℝ)(B:ℕ)(F:Vow.Cusp n)(u v:ℝ):Prop:=∃ I:blazeK n,(∀ X:Aura n,∀ D⊆ X.val,Fray p W (cipherK B) X D (F X D) (I X D))∧ (∀ i: Seat n,tallB (urnL I) p.B (wu p) i ≤ u) ∧ ∀ i: Seat n,tallB (Vow.hymn I) p.B (wu p) i ≤ v
abbrev Coverable(p:BudgetPoint)(W:ℝ)(B:ℕ)(F:Pair (Vow.Cusp n))(u v:ℝ):= Billable p W B (Pair.plus F) u v ∧ Billable p W B (Pair.minus F) u v
def Armed (p:BudgetPoint)(W:ℝ)(F:Vow.Cusp n)(u:ℝ):Prop:=∃ C':Vow.blazeK n,ArmsK p F C' W ∧ ∀ i:Seat n, tallB (Vow.hymn C') p.B (p.supportExponent+1+1) i ≤ u
local notation "gΨ"=> degreePrice p.B θΓ wΨ
local notation "Upp"=> uk_b (rentΦ p γΓ dΓ) vδ θΓ gΨ
local notation "αΒ"=> p.supportExponent+1+1
include Ω Th
lemma assertK (u:ℂ)(i:πχ)(F:VK)(pA:Billable p W B F m₁ m₂)(q:‖u‖=1): MonoQ p W (αΒ) (Ω.nuR i F u) Upp ∧ MonoQ p W (p.supportExponent+1+1+wΨ) (rebP (Ω.chest i F u)) θΓ ∧ Armed p W (Ω.chest i F u) (r₁⁻¹*γΓ):=by
 obtain ⟨I,t,pL,q'⟩:=pA
 let op:opV I 1:= (Ω.honor Th (fun i j v=> (t i j v).merit.wage (zero_le_one.trans Ω.floor)) pL q').1
 have hv:0 ≤ ρL p:=by unfold ρL wΨ; linarith [p.exponent_pos]
 have hu:ρL p ≤ wu p:= by unfold ρL wu wΨ; linarith
 have hp:0 < wΨ:=by norm_num [wΨ]
 let P:= Th.transit
 exact sellΦ Ω.floor (Ω.κm i u) (Xp) F I (Ω.kernel u i q).1 t op hv hp (by unfold ρL wΨ wu; linarith) wΨ m₁ vδ θΓ hp le_rfl (fun x=> (tall_m _ (fun i=> (t i _ (empty_subset _)).merit.wage (zero_le_one.trans Ω.floor)) hu x).trans (pL x)) Th.lead P.ht P.earn P.wings _ fun X V=> Ω.birth i X u V
local notation "omC"=> tintK p (rentΦ p γΓ dΓ) θΓ vδ
lemma project_K (i:πχ)(F:Pair VK)(pA:Coverable p W B F m₁ m₂):
 Both (fun f=> MonoQ p W (αΒ) f Upp) (Ω.νpoint i F) ∧ Both (fun F=>MonoQ p W (ρL p) (rebP F) θΓ ∧ Armed p W F (r₁⁻¹*γΓ)) (Pair.plus (Ω.waveW i F),Pair.minus (Ω.waveW i F)):=by
 obtain ⟨a,hf,t⟩:= Ω.assertK Th _ i _ pA.1 Complex.norm_I; obtain ⟨b,h,hF⟩:= Ω.assertK Th (-I_) i _ pA.2 (by simp)
 rw [waveW, Pair.plus_cat,Pair.minus_cat]
 exact ⟨FeeBook.MonoQ_join a b, ⟨hf,t⟩,h,hF⟩
lemma rollH (i:Er):IncX Utrue (Ω.lerW i) p W (φcape p a (Qu*b*r) (Qu*c*r) W)∧ IncX Utrue (Ω.ler i) p W (cap1 p (BondL.øK r) W):=by
 rw [mul_assoc Qu b _,mul_assoc Qu c _]; let A:= Ω.bond; let k:= Th.speed.ny; exact ⟨Ione.addT p (A.pay_r Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos k Ω.raw) (A.pay_z Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos k Ω.raw), A.starH Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.economic Ω.pos k⟩

abbrev txStar (i:Pair (ΘS r))(F:Pair (Vow.Cusp n))(U0:Pair (RegBudget n))(τ:Ids n):Pair (RegBudget n):= U0+(Ω.lerW i.1,Ω.lerW i.2)+(cast_E (Ω.νpoint i F).1 τ, cast_E (Ω.νpoint i F).2 τ)
abbrev rollT (i:Pair (ΘS r))(F:Pair (Vow.Cusp n))(U0:Pair (RegBudget n))(τ:Ids n):Pair (RegBudget n):= Ω.txStar i F U0 τ + (Ω.ler i.1,Ω.ler i.2)
abbrev tintC (g:Cusp n) (p:BudgetPoint)(θΓ r₁ γΓ W:ℝ):Prop:= MonoQ p W (ρL p) (rebP g) θΓ ∧ Armed p W g (r₁⁻¹*γΓ)
local notation "κX"=> u0+φcape p a (Qu*b*r) (Qu*c*r) W+s^2
open Py
lemma incXG (i:πχ)(F:Pair VK)(pA:Coverable p W B F m₁ m₂)(hZ:Both Cash.poise (Ω.νpoint i F))(τ:Ids n)(U0:Pair (RegBudget n))(qT:Both (fun T=>IncX Utrue T p W u0) U0): Both (fun T=>IncX Utrue T p W (κX)) (Ω.txStar i F U0 τ)∧ Both (fun T=>IncX Utrue T p W Λ) (Ω.rollT i F U0 τ):=by
 obtain ⟨x,y⟩:= (Ω.project_K Th i F pA).1
 have he(T:Pax n)(p':Cash.poise T)(u:MonoQ p W (αΒ) T Upp):IncX Utrue (cast_E T τ) p W (s^2):=by
    obtain ⟨h,m,f⟩:=u; have hx:IncX Utrue (cast_E T τ) p W omC:= worth_R p T τ p'.2 p'.1 (zero_le_one.trans Ω.floor) m f; apply Fixed.Voltage.upgradeI _ _ hx; linarith only [Th.lens,sq_nonneg s]
 obtain ⟨A,U⟩:= Ω.rollH Th i.1; obtain ⟨P,M⟩:= Ω.rollH Th i.2; let h:= Ione.addT p (Ione.addT p qT.1 A) (he _ hZ.1 x); let t:= Ione.addT p (Ione.addT p qT.2 P) (he _ hZ.2 y); exact ⟨⟨h,t⟩, Fixed.Voltage.upgradeI _ _ (Ione.addT p h U) Th.cap, Fixed.Voltage.upgradeI _ _ (Ione.addT p t M) Th.cap⟩
open Haro

local notation "Zx" A:max μ:max j:max T:max=> zeus j μ (Haro.heroP (StackL A T))
lemma latticeFieldEstimates (A:RegBudget n)(x:IncX Utrue A p W (κX))(K:Finset (Scree.Hub n))(pX:liveB K)(e:Lens Wk)(j:ℕ)(x':1 ≤ j)(M:Male)(v₀:0≤u0): Mind (Zx A M j K) ∧ ‖Zx A M j K‖ < r/256:=by
 obtain ⟨ht,w,t⟩:= Haro.axeK K p M A e x pX Ω.floor Ω.fresh j x'
 refine ⟨w,t.trans_lt (lt_of_le_of_lt ?_ Th.sky)⟩
 have he: κX ≤ 3*(u0+s^2):=by linarith only [Th.plume,v₀,sq_nonneg s]
 rw [show (512:ℝ)*Wk/512=Wk from (by ring),show Wk * _= tiltB Wk p*(κX)/W^2 from ?_]; swap; · unfold tiltB; ring
 apply div_le_div_of_nonneg_right _ (sq_nonneg W); exact mul_le_mul_of_nonneg_left he (Py.desire p (by linarith only [Th.leo])).le
end Technique
end MatchW
end YM.CF.Sour
