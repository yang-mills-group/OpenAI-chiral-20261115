import YM.SU5.Selected.Cairn.Petit
import YM.SU5.Selected.Actress.Charm
import YM.SU5.Selected.Cairn.Season
import YM.SU5.Selected.Twirl.Celeste
import YM.SU5.Selected.Twirl.Swan
import YM.SU5.Selected.Cor.Treasure
import YM.SU5.Selected.Cor.Battery
import YM.SU5.Selected.Cor.Guild
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (C : ∀ j : Axis, Arena Y H Q.circuit j 0 false)
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false
local notation "m" χ:max => marked Y H V Q Qc (3:Axis) false (C 3) χ
open CF.Pannier.Chancel Tapestry Papal SatinVerification
open CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb CF.Pannier.Chancel.Lantern.Bulb.Mezz
open Crest.Airy (Coast Wq)
open Mileage
attribute [local instance] opCStarAlgebra
namespace Fern
local notation "B0"=> 3
local notation "O"=> (3:Axis)
local notation "R"=> Aurora Y H V Q (O) false (C 3)
local notation "U" s:max=> liftCap Y H V Q Qc O false (C 3) s
local notation "Ω"=> seat0 Y H V Q O false (C 3)
variable (Ψ:Horizon Y H V Q Qc 3 false (C 3)) (hΨ:Law Y H V Q Qc 3 false (C 3) Ψ)
local notation "L" v:max => emigrant Y H V Q Qc O false (C 3) Ψ v (C v)
local notation "T" i:max => Ψ.character i
variable {X: Rack Λ l} {Z₀:Clay Λ l} (eX: Exhibition Y H i k I E X Z₀)
  {A:Mezz} {b' v' w':ℕ} {C₁ δ ε Γ:ℝ}{G F:Coast→ Wq A.marks}
   (Δ:Delay Y H b' v' δ Γ C₁ ε A w' G F)
local notation "Δ₀" => Δ.stationed Y H
variable {F':Coast→ Wq A.marks}(V₀:Effigy Y H Γ b' v' δ C₁ ε A w' G F' F)  -- HERE clarify F is old symbol ??? printed below
variable (s:ℕ)
local notation "p"=> A.Broad
local notation "ϱ"=> screen Y H V₀.first_
local notation "r" f:max=> (Mezz.Sermon.solitude A K (V₀.first_.stationed Y H) f).val
local notation "θ" X:max=> Tower.mirror (K) O 0 X*X
open Tender (stint rapids)

open Papal.Convent (crew PriceE TipC guardFee enter pass_key stellar)
open CF.Pannier.Chancel.Attic.Cairn CF.Pannier.Chancel.Attic.Cairn.Giant
variable {M:Giant} {β:M.Notes → Crest.Rail.basisRule}{Cβ γ:ℝ}(pβ:PriceE TipC Γ (crew Y H) M β Cβ γ)(vβ:guardFee M ≤ Λ.h)(uβ:Λ.d≤Convent.enter)(sc:Scooped Λ)
local notation "rM" x:max => (SpireBook.bouquet M K x).val
local notation "ρ·"=> 3*Real.exp (1-Γ)
variable {q d w:ℕ}{C₀ T₀:ℝ} (P : Council.Choir Y H q d w C₀ T₀ Γ) (hp:10000 ≤ Γ)
open Council Survival OS.Ground
local notation "B"=> payout d q w
local notation "bM"=> Survival.camp B
local notation "S"=> Sen (Survival.camp B) B
include C P hp eX V Q Qc V₀ vβ pβ uβ sc
local notation "Y₀" v:max=> escort Y H V Q Qc O false (C 3) v (C v)
local notation "ξ" v:max=> phaseRead Y H V Q Qc v (C v)
open Season
structure SeriesC(s n n' m₀:ℕ)(F:∀ W:Window.Family,Bool→Mezz.Sermon A (tent Y H) W)(q d w:ℕ)(W₁:SU.Slot→ Family (tent Y H))(Xβ: ∀ W:Window.Family,Bool→SpireBook M (tent Y H) W)(x:Ψ.X):Prop where
    ears : TimeLine Y H V Q Qc C s n n' Ψ eX V₀ F q d w W₁ x
    realm : printedHere Λ l s M.Broad (cabin m₀)
    slopeT : addgap K ≤ M.timeGap.val
    dues (W:Window.Family): M.Equatorial (tent Y H) W (Xβ W false) (Xβ W true)
    earsE (v:Axis)(z:Window.Family × Bool): ‖E s (θ (rM (Xβ z.1 z.2)))‖ ≤ ρ· ∧ ‖E s (rM (Xβ z.1 z.2))‖ <1/2 ∧ ‖(ξ v) ((Y₀ v) (T x)) s (rM (Xβ z.1 z.2))‖ <1/2
#check @SeriesC.mk
lemma expedition (u:ℕ) : ∃ (Ψ':Horizon Y H V Q Qc 3 false (C 3))(x:Ψ'.X) (s n n' m₀:ℕ)(F:∀ W:Window.Family,Bool→Sermon A K W)(Z:SU.Slot→Family K)(Xβ:∀ W:Window.Family,Bool→SpireBook M (tent Y H) W),u≤ s∧ SeriesC Y H V Q Qc C Ψ' eX V₀ s n n' m₀ F q d w Z Xβ x:=by
 obtain ⟨Ψ',t⟩:= vision Y H V Q Qc 3 (C 3) eX
 let g(s:Axis)(x: Ψ'.X):= (Y₀ s) (Ψ'.character x); let V' (s:Axis) (i: Ψ'.X) := Classical.choice (realizeRoom Y H V Q Qc s false (C s) (g s i))
 obtain ⟨F',Z,Xβ,s,n,n',m₀,x,h,a,v,du,pr,pm,y⟩:= antilles Y H V Q Qc C Ψ' t eX V₀ pβ vβ uβ sc P hp u V'
 have t':Display Y H V Q Qc C Ψ' eX V₀ s n n' Z q d w F' x:=by
    refine ⟨fun i=>?_, du, fun i z=> ((y i).2.2.2.2.1 z).2⟩; refine ⟨t,a,v,fun W=> (((y 3).2.2.2.2.1 (W,i)).1),fun W=> ?_,fun i=> ?_⟩
    · exact Guild.alongCost Y H V Q Qc C s (Ψ'.character x) (V₀.first_.stationed Y H) (Z W i) (V₀.first_.slope.ge) v (((y 3).2.2.2.2.1 (W,i)).2.1) (fun v=> ((y v).2.2.2.2.1 (W,i)).2.2)
    exact ⟨_, seated Y H V Q Qc i C eX (g i x) (V' i x) (y i).1,axisBill Y H V Q Qc 3 C eX _ (Ψ'.character x),(y i).2.2.2.1⟩
 refine ⟨Ψ',x,s,n,n',m₀,Z,F',Xβ,h,onward Y H V Q Qc C s n n' Ψ' eX V₀ Z q d w F' x t' (fun W=> ?_),pr,(by rw [show M.timeGap=(crew Y H).timeGap from (pass_key Y H pβ).1]; exact Nat.le_add_right _ _),pm, fun i=> (y i).2.2.2.2.2⟩
 let c(w:Bool):= t'.esteem 3 (W,w); exact TimeTwist.arrives Y H V Q Qc C s (V₀.first_.stationed Y H) (Z W false) (Z W true) V₀.first_.slope.ge (t'.card false).shore (Ψ'.character x) (t'.porch W) (c false).1 (c true).1 (c false).2 (c true).2
end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Fern
#print axioms SeriesC
#print axioms expedition
#check @expedition
