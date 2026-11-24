import YM.CF.BProof.Digit.Palm
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Digit
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
open Haro Ione Larch Glyph
section
variable {N:Side}
end
open Exa Tap Dial
open Push.AbsoluteSums Trees Mew Floral
open scoped YM.CF.Mew
variable {B:Cusp n}{Q:blazeK n}{W:ℝ}{δ:ℕ}{μ:Aura n→ℝ}{F:Bag n}{K:Rinse (Seat n) (Copy n)} {R:RegBudget n}
abbrev Burst (P:BudgetPoint)(K:Rinse (Seat n) (Copy n))(R:RegBudget n): Prop:=∀ X:Aura n,Stax.birthL K X ∅= orbV R X
lemma strike(p:Burst P K R)(X:Aura n)(V:Orbit n) : Fine (lamp (P:=P) B K) X V=Fine B X V+orbV R X V+Fine (rem_X (P:=P) B K) X V:=congrArg₂ (·+·) (congrArg₂ (·+·) (rfl:Fine B X V=Fine B X V) (congrFun (p X) V)) (rfl: Fine (rem_X (P:=P) B K) X V=Fine (rem_X (P:=P) B K) X V) -- tune
namespace Cash
variable {m:Cash P}(p:m.Warrant)(u:m.grapes Q B δ W)(w:1≤W) (s:Pitch P W δ K μ fun i Y=> F Y i)
abbrev mix (m:Cash P)(Q:blazeK n)(μ:Aura n→ℝ) : Aura n→ℝ:= urnL Q+urnL (Sco Q μ)+m.z • (μ+urnL (ScoL Q μ))
variable (t:m.vines Q μ 1)
local notation "X₀"=> mix m Q μ
local notation "G₀" => lamp (P:=P) B K
local notation "H₀" => rem_X (P:=P) B K
local notation "ℓ₀"=> P.supportExponent+1+1
include p u w s t
lemma logPay : Ready stern P.B X₀ (ℓ₀) m.γr wΨ m.rate ∧ (∀ X:Aura n, Medal P X.val ∅ (Fine (G₀) X) W (X₀ X)) ∧(∀ X:Aura n,Medal P X.val ∅ (Fine B X) W (X₀ X))∧ ∀ X:Aura n,Medal P X.val ∅ (Fine (G₀) X-Fine B X) W (m.z⁻¹*X₀ X):=by
 obtain ⟨x,e⟩:=heights p u w s t
 have H:=zero_le_one.trans w; have h1(i:Aura n):0≤ μ i + urnL (ScoL Q μ) i:= add_nonneg (t.mid i) ((e.fr i _ (empty_subset _)).merit.wage H)
 have h2(i):0≤ Q i ∅:= (u.fr i _ (empty_subset _)).merit.wage H; have h3(i):0≤ m.z*(μ i+urnL (ScoL Q μ) i):= mul_nonneg p.s.le (h1 i); have h4(i):0 ≤ Sco Q μ i ∅:= (x.fr i _ (empty_subset _)).merit.wage H
 have h5(i): Sco Q μ i ∅≤ (X₀ i):=le_trans (le_add_of_nonneg_left (a:=Sco Q μ i ∅) (h2 i)) (le_add_of_nonneg_right (h3 i))
 refine ⟨ready_T (P:=P) p.ht Ψk p.earn (fun i=> (h4 i).trans (h5 i)) ?_,fun i=>(x.fr _ _ (empty_subset _)).merit.big (h5 i),fun i=>(u.fr _ _ (empty_subset _)).merit.big ((le_add_of_nonneg_right (h4 i)).trans (le_add_of_nonneg_right (h3 i))),fun X=>?_⟩
 · intro i; rw [mix,tall_add,tall_add,tall_s,tall_add]; apply le_trans _ p.wings; refine add_le_add (add_le_add ((Leaf.price u (uv P) H).lien i) (x.lien i)) (mul_le_mul_of_nonneg_left (add_le_add ?_ (e.lien i)) p.s.le)
   exact (tall_m _ t.mid (show ρL P ≤ wu P-wΨ*0 by rw [mul_zero,sub_zero]; exact uv P) _).trans (by rw [parse]; exact t.birth _)
 rw [show Fine (G₀) X-Fine B X=Stax.birthL K X ∅+Fine (H₀) X from (by unfold Fine lamp; abel)]; apply ((aptL B Q u.fr _ _ s w X _ (empty_subset _)).merit.plus (e.fr _ _ (empty_subset _)).merit).big; unfold δWeight; rw [if_pos rfl,le_inv_mul_iff₀ p.s]; exact le_add_of_nonneg_left (add_nonneg (h2 X) (h4 X))
lemma reload (h:Burst P K R) : Binder P W (ℓ₀) (Nu P (Fine (G₀)) (Fine B) R) m.Nr:=by
 obtain ⟨f,x,y,z⟩:=logPay p u w s t; obtain ⟨c,e⟩:=heights p u w s t; have w(i:Aura n): Medal P i.val ∅ (Fine (H₀) i) W (urnL (ScoL Q μ) i):= (e.fr _ _ (empty_subset _)).merit
 refine beauty.mpr ⟨_, Larch.α_G _ _ p.s f ‹1≤W› x y z w (strike h),fun i=>?_⟩; exact Larch.cost_p _ _ p.s f ‹1≤W› x y z w (strike h) _ ((Leaf.price e (by unfold ρL wΨ; linarith : (ℓ₀)≤ρL P) (zero_le_one.trans ‹1≤W›)).lien i)
end Cash
end YM.CF.Sour.Digit
