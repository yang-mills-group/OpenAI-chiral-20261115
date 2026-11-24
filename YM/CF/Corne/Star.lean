import YM.CF.Tarn.Sold
import YM.CF.Cloak.Coil
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Corne
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reine
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r j:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
variable(T:Tube G S)(x u v:ℝ)(P:Tab S)(q:Chi)(d:ℝ)(l:ℕ)(M:Monk G S)
local notation "a₀"=> M.key
local notation "B₀"=> M.V
local notation "p₀"=> M.park
local notation "k₁"=> M.k
section scalar
variable (β:ℝ)(J: ChartRatio G)(t b e:ℝ)(j:ℕ)
local notation "A₁"=> locals a₀ a₀ x p₀ ((j+104)*radiusB x)
abbrev flare(M:Monk G S)(i:M.zoo x):= logGuard q J t (tape (M.fuel x T q d l β) i)
abbrev jewel : ℝ := ∑ i∈ A₁,flare T x q d l β J t M i
def dua(i:Site c)(M:Monk G S):= ∑ z:M.zoo x, ansC (S:=S) i z.val.val* flare T x q d l β J t M z
lemma gala: (∑ i:Site c, dua T x q d l β J t i M)-jewel T x q d l M β J t j=∑ i∈ A₁ᶜ, flare T x q d l β J t M i:=by
 unfold dua; rw [sum_comm]; simp_rw [←sum_mul, show ∀ v:M.zoo x,(∑ i,ansC (S:=S) i v.val.val)=1 from fun v=> plant_s S (j:=0) (fun _=>v.val.val),one_mul]; rw [← sum_compl_add_sum A₁,sub_eq_iff_eq_add] -- tune
local notation "Y"=> tape (M.fuel x T q d l β)
local notation "ι"=> (∏ i∈ A₁ᶜ, broad q d (Y i))
def Qen:=ι * Reine.moist q a₀ k₁ (M.sent x T q d l β) B₀ x b e ((j+100)*radiusB x) ((j+110)*radiusB x)
lemma lore(h:0<d)(hu:d≤t): keto T x M q d l β J b e j=Qen T x q d l M β b e j * Real.exp ((∑ i,dua T x q d l β J t i M)-jewel T x q d l M β J t j):=by
 rw [gala]; unfold keto Qen capsule; by_cases p:ι=0; · dsimp only; rw [p]; ring
 let Z(z: M.zoo x):= Next.SectorChange.extended q J d (Y z); let F:= Reine.moist q a₀ k₁ (M.sent x T q d l β) B₀ x b e ((j+100)*radiusB x) ((j+110)*radiusB x)
 change (∏ i∈ A₁ᶜ,Z i)*ι*F=ι*F*_ ; rw [mul_assoc,mul_comm]; congr 1; rw [Real.exp_sum]; refine prod_congr rfl fun i v=>?_ ; unfold Z flare Next.SectorChange.extended logGuard
 have he: ‖Y i‖ ≤ 2*d:= (broad_span q h (Y i) (fun he=>p (prod_eq_zero v he))).le; rw [broad_one q (by positivity) he,broad_one q (by have hh:=h.trans_le hu; positivity) (he.trans (by linarith only [hu]))]  -- tune
end scalar
end YM.CF.Corne
