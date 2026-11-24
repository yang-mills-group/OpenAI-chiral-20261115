import YM.SU5.Selected.Vanguard
import YM.SU5.Selected.Time.Prom
/-! Observables CP6. Select & reconstruct continuous **physical time**, no spectator semantics. Includes concurrence test of spatial mesh motions. Test spacings as Vanguard. ( `monoAxis U` has dummy spatial even though real mesh is present; `stay` keeps only relevant time facts expressed with spectralP pushed to ℝ of THAT operator system). -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
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
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "Β" => pruner Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "uℋ" => basisRoom Y H V Q j r C
local notation "U₀" s:max => timePruner Y H V Q Qc j r C s
local notation "p₀" s:max => spacePruner Y H V Q Qc j r C s
local notation "τ" s:max => tick Y H s j 0 r
local notation "ρ" s:max => ripple Y H V s Q.circuit j 0 r C
local notation "P₀" s:max => stretches Y H V Q Qc j r C s
variable {χ : CapCharacter Y H V Q Qc j r C} (U : Birthplace Y H V Q Qc j r C χ)
local notation "λ₀" => vacuum Y H V Q Qc j r C U
local notation "η" s:max => markedActor Y H V Q Qc j r C U s
local notation "η₀" => leave Y H V Q Qc j r C U
open Companies
namespace Diary
open Spectral Spectral.Alps
-- strict here means 'all gauge-invariant marks' vs wide flag? r picks `Neutral only or not` as in II. ℰ hierarchy of E even projections applies. Name E for uncompressed. Use literal converts for consumers.
local notation "S" u:max=> walking Y H V Q Qc j r C U u
local notation "V₀" => journey Y H V Q Qc j r C U
abbrev ath(Time:ℂ):U.H.Op:= Spectral.Alps.balcony ((journey Y H V Q Qc j r C U).monoAxis j) Time
local notation "S₀" => (V₀).monoAxis j
noncomputable def jetTime := S₀
lemma jet_heat : (jetTime Y H V Q Qc j r C U).E=(V₀).track:=rfl
local notation "Πt"=> jetTime Y H V Q Qc j r C U
abbrev life := Spectral.Alps.aboveH (Πt)
abbrev porch := (Πt).edge
abbrev penthouse := (Πt).ground
abbrev priority := (spectralP Πt)
local notation "E₀"=> (V₀).track
local notation "x₀"=> (Πt).orth
local notation "β"=> bottom Y H V Q Qc j r C U
local notation "σ"=> travel_χ Y H V Q Qc j r C U
local notation "Pr"=> priority Y H V Q Qc j r C U
variable (s:ℕ)
include V Q Qc C U
/-- transfer appointment exactly on journey. -/
lemma marches (u : Trans j)(t : ℕ)(x:ℤ)(d:ℕ) : Commute (spacePruner Y H V Q Qc j r C s u x) ((U₀ t) d) := by
 let i:= max s t; have hp:s≤ i:= le_max_left ..; have ht:t≤ i:= le_max_right ..; rw [corner_finer Y H V Q Qc j r C s u i x hp,atom_refines Y H V Q Qc j r C t i d ht]; exact corner_time Y H V Q Qc j r C _ u _ _ -- syntax tune location
omit V Q Qc C U in
private lemma outlier {a:Mesh}{T:Hilbert}(F:Many a T)(P:T.Op)(h:∀ i n,Commute P (F.double i n))(t:ℝ≥0): Commute P (F.track t):=by
 let Q'(z:T): ℝ≥0→ T:= fun w=>P (F.track w z); let G(z:T):ℝ≥0→ T:= fun w=> F.track w (P z)
 change _*_=_; ext1 i; refine congrFun ((fills a).denseRange_val.equalizer (P.continuous.comp (F.trekU i).continuous) ((F.trekU (P i)).continuous) (?_ : Q' i ∘ _=G i ∘ _ )) t; funext y; obtain ⟨u,d,p⟩:=MeshClock.split a (show _ from (y.property)); change P (F.track y.val i)= F.track y.val (P i); rw [←p,F.track_even]; exact DFunLike.congr_fun (h u d) i -- syntax split
lemma travel_drive (u:Trans j)(x:ℤ)(t:ℝ≥0) : Commute (σ s u x) ((V₀).track t) := by
 refine outlier _ _ (fun i n=>?_) t; exact (marches Y H V Q Qc j r C U s u i x (2*n)).map (η₀).toAlgHom.toRingHom  -- argument order? include U pointless but done.

-- ground / station: all Mink times equivalence. temporal spectator U never tested. P projection (pTime=0) exactly strict ground for THESE translations. `travel` mesh comm with edge and project.
omit V Q Qc C U in
private lemma ground_edge {u:Axis}{T:Hilbert}(F:OS.Semigroup T u)(x:T): x∈ F.ground ↔ ∀ t:ℝ, F.edge t x=x:=by
 refine ⟨fun h i=> mink_invar F x i h,fun h=>?_⟩; apply (F.fixed x).2; intro k
 let f(v:T):= inner ℂ v (F.E k x)-inner ℂ v x; have hx(v:T):f v=0:=by
    by_contra p; have hf:= norm_pos_iff.mpr p; have hu:(F.E k-F.E 0) x=F.E k x-x:=by rw [ContinuousLinearMap.sub_apply,F.eZero]; rfl
    unfold f at hf; rw [←inner_sub_right, ←hu] at hf; obtain ⟨i,t⟩:= lips F v x _ _ _ (0:ℝ) hf; rw [ContinuousLinearMap.sub_apply,h i,h 0] at t; simp at t
 exact ext_inner_left ℂ (fun i=> sub_eq_zero.mp (hx i))
lemma staves (v:U.H): v∈ β ↔ (∀ t:ℝ,(Πt).edge t v=v) ∧ ∀ (i:ℕ)(u:Trans j)(x:ℤ), σ i u (2*x) v=v :=by
 exact (grounded Y H V Q Qc j r C U v).trans (and_congr (((Πt).fixed v).symm.trans (ground_edge (Πt) v)) Iff.rfl)
lemma intimate (x:ℝ)(z:ℤ)(u:Trans j) : Commute (σ s u z) ((Πt).edge x):=(Spectral.Alps.edge_of_commute (Πt) _ ((travel_drive Y H V Q Qc j r C U s u z 1).symm) x).symm
lemma alpine (x:ℂ)(z:ℤ)(u:Trans j) : Commute (σ s u z) (ath Y H V Q Qc j r C U x):=(intimate Y H V Q Qc j r C U s _ _ _).mul_right (travel_drive Y H V Q Qc j r C U s u z x.im.toNNReal)
lemma mink_vac(t:ℝ): (Πt).edge t λ₀ = λ₀:= ((staves Y H V Q Qc j r C U λ₀).1 (apt_floor Y H V Q Qc j r C U)).1 t
lemma fresh (x:U.H)(h:x∉ penthouse Y H V Q Qc j r C U)(t:ℝ≥0):
    (∀ z:ℝ≥0, (life Y H V Q Qc j r C U) (E₀ z x) ≠ 0) ∧
    0 < ((Pr).diagonal (E₀ t x)).real (Set.Ioi 0)∧ 0 < ((Pr).diagonal x).real (Set.Ioi 0):=by
 let F:=Πt; exact ⟨fun z w=> strict_w F x h z ((lively F (F.E z x)).2 w), (margin F (F.E t x)).1 (strict_w _ x h t), (margin F x).1 h⟩
lemma reach_arc (t:ℂ)(x: U.H)(v:(t.im)≥0) : inner ℂ x (ath Y H V Q Qc j r C U t x) = ∫ u:ℝ, Complex.exp ((u:ℂ)*t*Complex.I)∂(Pr).diagonal x:= Spectral.Alps.balcony_law (Πt) x v

end Diary
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Diary
#print axioms travel_drive
#print axioms staves
#print axioms fresh
#print axioms alpine
#print axioms reach_arc
#print axioms mink_vac
