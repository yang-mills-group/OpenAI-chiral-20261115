import YM.SU5.Selected.Undouble
import YM.SU5.Selected.Edges
/-!
# Half-tooth padding & selected representation on this grid

Stay at supports checked in each resolution. Stop using hidden sign choice
for `ρ 1`. Inherits all tick laws in all probability fibers with rank not
required. Production relation (not selected/Schwinger-only). Uses axis cap
comparison to get translations of all caps by the refined grid, without
spontaneously breaking through election. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Set MeshClock

local notation "ρ" s:max v:max=> ripple Y H V s G.history.circuit j 0 strict C v
local notation "M"=>timeMesh Λ
local notation "Q"=>advance Y H V G.history.circuit j 0 strict C
local notation "δ" s:max i:max=>(whenly M s i / 2)
local notation "J" s:max=>tick Y H s j 0 strict
local notation "S₀" =>stationC Y H V G j strict C
local notation "Qe"=>heatOp Y H V G j strict C
local notation "Be"=>boxElement Y H V G j strict C
section
variable (s i':ℕ){w:ℕ}(x:Entry Y H s j strict w)
include V C
-- padding relations by any symmetric span ; asymmetric follows for odd-odd adjustment
lemma balanced (u v W:ℕ)(y:Entry Y H s j strict W)(p: 2*w + u + v = 2*W) (h:y.val=(J s) u x.val) (e:0<w)(q:0<W) :
    B s y q= Q (δ s u) * B s x e * Q (δ s v):=by
  rw [undoubles,undoubles]; apply test_high Y H V s G.history j strict C; intro t z f
  change _=(ρ s u) ((B s x e) ((ρ s v) ((κ t) f)))
  let N:=Λ.R.L.val^(t-s)
  let X:=furnished Y H s G.history j strict w x t z; let Y₁:=furnished Y H s G.history j strict W y t z
  rw [limited_time Y H V s G.history.circuit j 0 strict C v z,snatch Y H V s G.history G.clipped j strict C w _ _ z,snatch Y H V s G.history G.clipped j strict C W _ _ z,limited_time Y H V s G.history.circuit j 0 strict C u z]
  have a: Y₁.val=(J t) (N*u) X.val:=by
    rw [show Y₁.val=Raise Y H G.history.circuit j 0 strict s t z y.val from rfl,h]; exact (tick_up Y H V s G.history.circuit j 0 strict t z x.val u).symm
  apply congrArg _; apply Subtype.ext
  change Y₁.val.val * ((J t) (2*(N*W)) f).val = chime K j (gaugeShift Λ.block ((N*u:ℕ):ℤ)) (X.val.val * ((J t) (2*(N*w)) ((J t) (N*v) f)).val)
  rw [a,chime_product]
  change _* _ = ((J t) (N*u) X.val).val * ((J t) (N*u) ((J t) (2*(N*w)) ((J t) (N*v) f))).val
  rw [tick_tock, tick_tock]
  have hx : N*u +2*(N*w)+N*v=2*(N*W) :=
    calc N*u + 2*(N*w) + N*v = N*(2*w+u+v) := by ring
         _ = 2*(N*W) := by rw [p]; ring
  rw [hx]

omit V G C
noncomputable def centering : Entry Y H s j strict (w+i') := by
  refine ⟨(J s) i' x.val,?_⟩
  obtain ⟨S,h,z⟩:=x.property
  let k:=gaugeShift Λ.block i'
  refine ⟨address j k S,flow_port K j k h,?_⟩
  intro t p; obtain ⟨a,u,rfl⟩:= mem_image.mp p; obtain ⟨b,g⟩:=z a u
  have hp:0≤k:=by unfold k Heat.gaugeShift; positivity
  have ht:4*k=ruler Λ.block*i' :=by unfold k ruler Heat.gaugeShift; ring
  rw [moves,if_pos rfl,Nat.cast_add,mul_add,← ht]; omega -- maybe
include V G C
lemma centers (e:0<w) : B s (centering Y H j strict s i' x) (by omega)= Q (δ s i') * B s x e * Q (δ s i'):=balanced Y H V G j strict C s x _ _ _ _ (by omega) rfl e _
namespace Acting
variable (T:Acting Y H V G j strict C)
local notation "Qₜ"=>clock Y H V G j strict C T
local notation "Beₜ"=>watches Y H V G j strict C T
local notation "γ" s:max=>voice Y H V G j strict C T s
lemma bal_est (e:0<w) : Beₜ s _ (centering Y H j strict s i' x) (by omega) = Qₜ (δ s i') * Beₜ s w x e * Qₜ (δ s i') :=
  show T.showL _=((_) * _) from by
    unfold watches clock; rw [← map_mul, ← map_mul] -- left assoc check
    exact congrArg T.showL (Subtype.ext (centers Y H V G j strict C s i' x e))
lemma half_voice (f:Fₛ s) : (γ s) ((J s) i' f)= Qₜ (δ s i') ((γ s) f):=by
  obtain ⟨u,h,x,rfl⟩ := ((eventually_gt_atTop (0:ℕ)).and (field_entry Y H j strict s f)).exists
  let X:=centering Y H j strict s i' x
  have v:0<u+i':=by omega
  rw [show (J s) i' x.val=X.val from rfl, T.notes Y H V G j strict C s h, T.notes Y H V G j strict C s v X]; unfold X
  rw [T.bal_est Y H V G j strict C s i']
  change _ = (Qₜ _) _ -- tune order
  exact congrArg (Qₜ _ * Beₜ s u x h) (vacuum_time ..)
lemma on_even_positive(t:ℝ≥0): (Qₜ t).IsPositive:= by
  apply ContinuousLinearMap.nonneg_iff_isPositive _|>.mp
  have h: Qₜ t=star (Qₜ (t/2))*Qₜ (t/2):= by
    rw [show star (Qₜ (t/2))=Qₜ (t/2) from T.clock_symm Y H V G j strict C _,← clock_sum,add_halves]
  rw [h]; exact star_mul_self_nonneg _
end Acting
end

end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.half_voice
