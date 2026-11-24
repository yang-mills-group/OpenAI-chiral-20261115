import YM.CF.Fief.Wheel
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{k n j d:ℕ}
open Lich.Muster
attribute [local instance] opCStarAlgebra
variable{G S x e T}
variable(A:Muster G S x e T)
open Vol YM.Push.AbsoluteSums
open ConnectedActivityE6.Raw
variable (U: Monk SU.group S)
variable{s:ℝ}{l v:ℕ}
local notation "Qz"=> Domain N B
variable {c f:Side} -- remove
section
variable {a b C c' s w W z:ℝ}{i:Site (Domain N B)}{k l x:ℕ}
def payN{c f:Side}(G:Ratio c f)(k x n:ℕ)(u v C w w':ℝ):= Footprint.payment (G.count.val^4) (Paths.originFee k x) 0 v C w u (Paths.baseFee (d:=n) G k)
def boon_s (D:PathData SU.group)(G:Ratio (Domain N B) f)(k x:ℕ)(a b C σ t:ℝ)(K n:ℕ):=payN G k x n a σ C b t
lemma adept (G:Ratio (Domain N B) f)(s':Signed)(p:Footprint.reserve (C/4) a (Paths.legFee G l x) z)(hp:0<x)(hk:0<C) (Z:ℕ→ Atom SU.group n)(hy:SumBudget (fun i=>(Z i).budget (C/2)) W)(hz:0≤b):
 (∑ i':Bit (Site (Domain N B)),tallyL i i' a x*(∑ j:Site f,crownQ G s' (l*x) Z j (C/4) b i'))≤payN G l x n a z b W C :=swift G l x s' (by rw [← oil C hk]; exact hy) p (by positivity) (by positivity) hp b hz i
lemma countU {U:ℕ→ Atom SU.group n}(p:SumBudget (fun i=>(U i).budget C) W)(v:b ≤C): SumBudget (fun i=>(U i).budget b) W:=budget_mono p (fun i=>by unfold RG.Atom.budget RG.Atom.magnitude; positivity) (fun i=> by unfold RG.Atom.budget RG.Atom.magnitude; gcongr) -- tune unused V
end
local notation "r"=> k*radiusB x
local notation "b"=> radiusB x
local notation "V"=>T.up
local notation "W"=>T.down
local notation "Y"=>S.ratio
local notation "Zc"=>atOne Qz
variable(Q D C c' t σ σ' a v' v'' pg pg' δ δ':ℝ) (s₀:ℕ)
variable (k)(o:Site (Domain N B)) -- k duplic
local notation "H0"=> p
section fare
def worthK {c f:Side} (G:Ratio c f)(l B v:ℕ)(C a q k σ u h t:ℝ):= C*(payN G l B 2 a u k (tollE σ v * Stationary.gramCost SU.group q) σ+(payN G l B 3 a u (k*t^3) (tollE σ v * q) σ + payN G l B 4 a u (k*t^4) (tollE σ v * q) σ))+payN G l B 2 a u (k*t^2) (tollE σ v*h) σ
def worthH {c f:Side}(G:Ratio c f)(l B:ℕ)(C a q k σ u h t:ℝ):= C*(payN G l B 3 a u (k*t^3) q σ+payN G l B 4 a u (k*t^4) q σ)
local notation "u₀"=>A.phaseUp.threshold
local notation "v₀"=>A.phaseLow.threshold
local notation "M"=> Stores.till x
local notation "V₁"=> M/S.patch.L.val
open Vol
variable(s:Signed)(hx:0 < radiusB x)
local notation "N'"=>(Fintype.card Signed:ℝ)
include hx
set_option maxHeartbeats 900000 in
lemma budget_f(h:T.up.Bounds T.high σ C pg)(p:Footprint.reserve (σ/4) a (Paths.legFee Y k b) δ)(hp:0 ≤ Q)(ht:0≤v'):
 (∑ i:Bit (Site (Domain N B)), tallyL o i a b*(∑ j,ringF A s r Q v' (σ/4) i j))≤ worthK Y k b M Q a C v' σ δ pg u₀ :=by
 have ht'(n:ℕ):0≤ v'*u₀^n:=mul_nonneg ht (pow_nonneg A.phaseUp.threshold_pos.le n)
 have hX(i:ℝ)(F:Bit (Site Qz)→ℝ): (∑ j,tallyL o j a b*(i*F j))=i* ∑ j,tallyL o j a b*F j :=by rw [mul_sum]; simp only [mul_left_comm i]
 simp_rw [ringF, sum_add_distrib,←mul_sum]; simp_rw [mul_add, sum_add_distrib,hX] -- tune ≤ sequence
 apply add_le_add (mul_le_mul_of_nonneg_left ?_ hp) (adept S.ratio s p hx h.width (haste M T.up.loop) (pastA _ h.width h.two _) (ht' 2) (i:=o)); simp_rw [mul_add,sum_add_distrib]; exact add_le_add (adept Y s p hx h.width (rod T.up M) (hurry h _) ht) (add_le_add (adept Y s p hx h.width _ (pastA _ h.width h.three _) (ht' 3)) (adept Y s p hx h.width _ (pastA _ h.width h.four _) (ht' 4))) -- tune
lemma budget_c(h: T.down.Bounds T.low σ C pg)(p:Footprint.reserve (σ/4) a (Paths.legFee Zc k b) δ)(hp:0≤Q)(hd:0≤D)(ht:0 ≤ v'):
 (∑ i:Bit (Site (Domain N B)), tallyL o i a b*(∑ j,ringC A s r Q D v' (σ/4) i j)) ≤ worthK Zc k b V₁ Q a C v' σ δ pg v₀ + worthH Zc k b D a C v' σ δ pg v₀ :=by
 have ht'(n:ℕ):0 ≤ v'*v₀^n:=mul_nonneg ht (pow_nonneg A.phaseLow.threshold_pos.le _)
 have hX(i:ℝ)(F:Bit (Site Qz)→ℝ): (∑ j,tallyL o j a b*(i*F j))=i* ∑ j,tallyL o j a b*F j:=by rw [mul_sum]; simp only [mul_left_comm i]
 have hv: σ/2 ≤ σ:=half_le_self h.width.le
 simp_rw [ringC,sum_add_distrib,←mul_sum]; simp_rw [mul_add,sum_add_distrib,hX]; refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left ?_ hp) (adept Zc s p hx h.width _ (pastA _ h.width h.two _) (ht' 2))) (mul_le_mul_of_nonneg_left ?_ hd)
 · simp_rw [mul_add,sum_add_distrib]; exact add_le_add (adept Zc s p hx h.width (rod T.down V₁) (hurry h _) ht) (add_le_add (adept Zc s p hx h.width _ (pastA _ h.width h.three _) (ht' 3)) (adept Zc s p hx h.width _ (pastA _ h.width h.four _) (ht' 4)))
 simp_rw [mul_add,sum_add_distrib]; exact add_le_add (adept Zc s p hx h.width _ (countU (barn h.three _) hv) (ht' 3)) (adept Zc s p hx h.width _ (countU (barn h.four _) hv) (ht' 4))
end fare
end YM.CF.Fief
