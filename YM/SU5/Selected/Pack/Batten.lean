import YM.SU5.Selected.Pack.Cast
/-! # All-six Resume. Part A of checkpoint III: pay to retain each native mixed mark *all in same chosen component*. 
 `Witness`-sense. Aspiration to use this after proving dynamic nontriv.
-/
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
  (j : Axis) (C : ∀ j : Axis, Arena Y H Q.circuit j 0 false)
local notation "A" v:max => Arena Y H Q.circuit v 0 false
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false
local notation "m" χ:max => marked Y H V Q Qc j false (C j) χ
open CF.Pannier.Chancel Tapestry Papal SatinVerification
variable {q d w : ℕ} {C₀ Z : ℝ} {Ω : ℝ} (p : Council.Choir Y H q d w C₀ Z Ω)
    {X : Rack Λ l} {R₀ : Clay Λ l} (U : Exhibition Y H i k I E X R₀)
-- probability law
variable (Ψ : Horizon Y H V Q Qc j false (C j)) (hΨ : Law Y H V Q Qc j false (C j) Ψ)
local notation "L" v:max => emigrant Y H V Q Qc j false (C j) Ψ v (C v)
include V Q Qc C p U Ψ hΨ
open Council Survival OS.Ground -- likely ambiguous
local notation "B" => payout d q w
local notation "R" => Aurora Y H V Q j false (C j)
local notation "bM" => camp B
local notation "S" => Sen (camp B) B
local notation "M" s:max => liftCap Y H V Q Qc j false (C j) s
local notation "Π" => (R).orthogonalProjectionOnto
local notation "Ω₀" => seat0 Y H V Q j false (C j)
local notation "W" ℘:max => (Ψ.character ℘)

/-- This buys witnesses **within the elected physical μ**. It does not say all characters
see each footprint, nor prove convergence/distance stronger than `Witness`.
-/
def SelectedTogether (q d w:ℕ) (i':Axis) (C : ∀ a:Axis,Arena Y H Q.circuit a 0 false) (u : ℕ) : Prop :=
    let N := payout d q w
    let γ := camp N
    ∃ (Ψ' : Horizon Y H V Q Qc i' false (C i')) (p : Ψ'.X) (F : SU.Slot→Family K) (s c : ℕ),
      let χ:= Ψ'.character p
      u ≤ s ∧ Law Y H V Q Qc i' false (C i') Ψ' ∧
      extremeJoint Y H Q false (marked Y H V Q Qc i' false (C i') χ) ∧
      ∀ a : Axis, ∃ U : Birthplace Y H V Q Qc a false (C a) (escort Y H V Q Qc i' false (C i') a (C a) χ),
        LoneVac Y H V Q Qc a false (C a) U ∧
        marked Y H V Q Qc a false (C a) (escort Y H V Q Qc i' false (C i') a (C a) χ)=marked Y H V Q Qc i' false (C i') χ ∧
        ∀ z: SU.Slot, Witness Y H V Q Qc a (C a) (escort Y H V Q Qc i' false (C i') a (C a) χ) (F z) z s (Sen γ N) (booty γ d q) (cabin c) (1/2)

omit Ψ hΨ in
theorem plentiful (t:10000≤Ω)(n:ℕ) : SelectedTogether Y H V Q Qc q d w j C n := by
 obtain ⟨Z',h⟩:= vision Y H V Q Qc j (C j) U
 let g(s:Axis)(x: Z'.X):= escort Y H V Q Qc j false (C j) s (C s) (Z'.character x)
 let V' (s:Axis) (i: Z'.X) := Classical.choice (realizeRoom Y H V Q Qc s false (C s) (g s i))
 obtain ⟨F,s,c,i,hp,u,X'⟩:= assigns Y H V Q Qc j C p U Z' h n t V'
 exact ⟨Z',i,F,s,c,hp,h,u, fun a=>⟨V' a i,(X' a).1,(X' a).2.2.1,fun z=> ( (X' a).2.2.2 z ).1⟩⟩ -- DSL order

omit V Q Qc C p U Ψ hΨ
/-- `orchestrate` funds the very same Journey variant required by initial theorem and argument,
including original-to-task Cornet. No Lorentz reconstruction here. -/
theorem procured (ε η Ω : ℝ) (p : 0 < η) (t : 10000≤Ω) (s0 : Supplier) :
    ∃ (Λ : Preparation) (l : ℕ) (Z : ℝ), ε < Λ.x ∧ Λ.d ≤ η ∧ decorate s0 Λ l Z ≤ Λ.h ∧ Λ.nominated (VolumeCape.Dream.Nimbus l) ∧
    ∃ (H : Real.exp 1 ≤ Λ.x) (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (q d w : ℕ) (c : ℝ) (T : Council.Choir Y H q d w c Z Ω)
      (i k : ℕ → ℕ) (I : ℕ → Family (tent Y H) → ℕ → ℂ) (E : ℕ → Family (tent Y H) → ℂ)
      (L0 : Rack Λ l) (P0 : Clay Λ l) (T' : ℕ→ℕ→Tariff) (t : ℕ→Tariff) (V : Fashion Y H i k I E L0 P0 T' t)
      (Q' : SatinVerification.GroundExtension (i := i) (k := k) (E := E) Y H),
      SeasonCert Y H V ∧ Nonempty (∀ v : Axis,Arena Y H Q'.history.circuit v 0 false) ∧
        ∀ (C : ∀ v : Axis,Arena Y H Q'.history.circuit v 0 false) (i : Axis) (u : ℕ),
          SelectedTogether Y H V.univ_ Q'.history Q'.clipped q d w i C u := by
  obtain ⟨P, l, Z, a, b, g, o, H, Y, _, _, _, q, d, w, c, e, i, k, I, E, L', B', T, t', F, v⟩:= orchestrate ε η Ω (by linarith) p s0
  obtain ⟨X⟩:= extend_ground Y H F.univ_
  exact ⟨P,l,Z,a,b,g,o,H,Y,q,d,w,c,e,i,k,I,E,L',B',T,t',F,X,v,⟨fun i=> Classical.choice (voyage_H Y H F.univ_ X.history.circuit i 0 false)⟩,
    fun C i=> plentiful Y H F.univ_ X.history X.clipped i C e F.toExhibition t⟩
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection
#check @procured
#print axioms procured
