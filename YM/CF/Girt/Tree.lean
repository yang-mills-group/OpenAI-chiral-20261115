import YM.CF.Girt.Song
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Girt
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
local notation "G₀"=> SU.group
open Scroll
variable {f n :Side}{e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
open Broc
variable {M:Side}{x W:ℝ}
variable (P:Grasp Y B e) (G:Ratio (CSide M B) (mid C B))(R:GramM (mid C B))(F₁:Scree.Loom (mid M B))(F₂:Scree.Loom (mid C B))(q:Chi)(u:ℝ)
variable {P G R F₁ F₂ q u}(X:BaseL P G R F₁ F₂ q u)(T:StepData (Domain M B) (Domain C B))(p:T.ratio=ratio G)(t:T.patch.Branches T.kernel SU.group)
open Broc
open scoped Classical
open Oriented Presented RG Next.SectorChange Next.Fluctuations Next.Fluctuations.Sector SectorNext.Remainder.Affine CF.Appel Pressure.Stores CF.Forge AnalyticBridge.Annulus1AD
structure Flo (T:StepData (Domain M B) (Domain C B))(S:Tube G₀ T)(K:Teller G₀)(q:Chi)(J:ChartRatio G₀)(x W d s β:ℝ)(n l:ℕ) :Prop where
 pβ:0<β
 hd:0<d
 pW:0<W
 hf:0< fiery G₀ x T.patch.L
 cold: LocalRatio J
 year:0<s
 room:4*d < J.radius
 funds: K.Funds T S
 grantB(A:Stores T)(F:Forest T.ratio)(k:T.Choices)(V:Pane (mid M B)): A.flags=RG.flags (temp x) V → Standing (F:=F) (A:=A) (q.profiles G₀ T x W pW hf) J d k V ∧ ∃ Z:ℝ,MossX n l x A F S V k Z d (fiery G₀ x T.patch.L) q ∧ wireP G₀ (coupling β) d (Z*fiery G₀ x T.patch.L) Z ≤ s
abbrev TeamY(c:Side):= (Config G₀ (More c) × Directions G₀ (More c)) × Ids c
variable (V:Orbit (mid M B))(F: Forest T.ratio)(S:Tube SU.group T)(A: Stores T)(i:T.Choices)(q':Chi)(R':ChartRatio SU.group)(x W d' s:ℝ)(l:ℕ)
variable (P G R F₁ F₂ q u) in
def yieldB (z:TeamY (mid C B)):=let m:= youthℓ V.1 F A i z.1; if A.flags=RG.flags (temp x) V.1 then plight S x R.beta q' R' d' l W m • waveV P G R F₁ F₂ q u (p ▸ F) V (m.sent x S q' d' l R.beta,z.2) else 0
abbrev springT := ((suit T).prod (tableG G₀ (Bond (Domain C B)) s)).prod (depot (mid C B))
variable {C' :ℝ}{o:ℕ}(K:Teller G₀)(Z: Flo T S K q' R' x W d' s R.beta o l)
include X p t Z
lemma bait : Integrable (yieldB P G R F₁ F₂ q u T p V F S A i q' R' x W d' l) (springT T s)∧
 let f:=ropeG P G R F₁ F₂ q u (p ▸ F) V; let Ω:=q'.profiles G₀ T x W Z.pW Z.hf
 (∫ a, Ω.portion A F V.1 (through T F R.beta V.1 (fun _ a=>f (F.drape a))) i a ∂F.order G₀)=(prefactor T G₀ R.beta * (spare R' R.beta*point G₀ s)^Fintype.card (Active A x F)) • ∫ k, yieldB P G R F₁ F₂ q u T p V F S A i q' R' x W d' l k ∂springT T s:=by
 by_cases ht:A.flags=RG.flags (temp x) V.1; · obtain ⟨h,C,g,b⟩:= Z.grantB A F i V.1 ht; unfold yieldB; simp only [ht,↓reduceIte]; exact pock X T p t V F S A i q' R' d' s l Z.pW Z.hf Z.pβ g ht K Z.funds Z.cold Z.room Z.hd b Z.year h
 unfold yieldB; simp only [ht,↓reduceIte]; simp only [integral_zero,smul_zero]; refine ⟨MeasureTheory.integrable_zero _ _ _,?_⟩; apply integral_eq_zero_of_ae; filter_upwards with y; let U:= F.drape y; let D:=q'.profiles G₀ T x W Z.pW Z.hf; have hp:D.bill A i U V.1=0:=not_not.mp fun e=> ht ((D.actual _ _ _ _ e).exactFlags)
 change D.bill A i U V.1 • _=_; rw [hp,zero_smul]; rfl
lemma tour_B (Q:Op SU.Slot):Scree.stove P F₁ R F₂ G T q u Q V= scaleW _ Q (((Fintype.card (Forest T.ratio):ℝ)⁻¹*prefactor T G₀ R.beta) • ∑ F: Forest T.ratio,∑ A:Stores T, (spare R' R.beta * point G₀ s)^Fintype.card (Active A x F) • ∑ i: T.Choices, ∫ k, yieldB P G R F₁ F₂ q u T p V F S A i q' R' x W d' l k ∂springT T s):=by
 rw [valley X T p t V Q (q'.profiles G₀ T x W Z.pW Z.hf)]
 let c:= prefactor T G₀ R.beta; apply congrArg; rw [mul_smul]; apply congrArg; rw [Finset.smul_sum]; apply sum_congr rfl; intro F hf; rw [Finset.smul_sum]; apply sum_congr rfl; intro A h; unfold output Allocation.column tagTotal; rw [smul_smul,Finset.smul_sum]; exact sum_congr rfl fun i _=> (bait X T p t V F S A i q' R' x W d' s l K Z).2 -- arg
end YM.CF.Girt
