import YM.SU5.Selected.Algebra

/-! Match the local Swatch representation for this coherent course. In contrast
with coupon limits on specific Tapestry further thinnings, the statement on
limit operators here is about THIS D (all our further results will use it).
We use Tapestry precompactness only of the *actual finite* block map at the
same period and UV index. `same_step` identifies the maps. No identification
of a limiting extraction presupposed. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 250000
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
open Set
open Tapestry (Swatch render fabric render_inj texture render_eq renderLe spread sampling render_fabric)
variable (S:Finset Cover) (s:ℕ)
local notation "δx"=>wingspan Λ l S
local notation "rx"=>render S K
local notation "ry"=>render (δx) K
local notation "D"=> G.refine s

lemma texture_step (x:Swatch S): InTest K true (δx) false (D (rx x)) :=
  (G.history.circuit.supports s (texture S K x)).1

noncomputable def transfer_chart : Swatch S →ₗ[ℂ] Swatch (δx) where
  toFun x := fabric (δx) K (texture_step Y H G S s x)
  map_add' x y := by
    apply render_inj (δx) K
    rw [map_add ry]; simp only [render_fabric,map_add]
    exact G.history.circuit.plus_lift _ (aux_test (texture S K x)) (aux_test (texture S K y))
  map_smul' z x:=by
    apply render_inj (δx) K
    rw [map_smul ry]; simp only [render_fabric,map_smul]; exact G.history.circuit.amp _ (aux_test (texture S K x)) _
local notation "Bx"=>transfer_chart Y H G S s
lemma render_step (x:Swatch S): D (rx x)=ry (Bx x) := (render_fabric _ _ (texture_step Y H G S s x)).symm
lemma rendered_price (x:Swatch S): pay (rx x) (spread S * ‖x‖) := fun u => renderLe S K u x
lemma sample_price (x:Swatch S){C:ℝ}(p:pay (rx x) C): ‖x‖≤C := by
  obtain ⟨u,h⟩ := (separates K S).exists -- check namespace
  exact sampling _ _ _ ⟨h⟩ x (p u)
lemma chart_price : ∃ c:ℝ,∀ i:Swatch S,‖Bx i‖ ≤ c * ‖i‖ := by
  obtain ⟨c,pc,cv⟩:=G.history.implements s S
  obtain ⟨t,h⟩:=(cv 1 zero_lt_one).exists
  refine ⟨c*spread S,fun x=>?_⟩
  rw [mul_assoc]; apply sample_price Y H
  rw [←render_step Y H G S s x]
  exact (h _ (texture S K x) _ (rendered_price Y H S x)).1
noncomputable def transfer : Swatch S →L[ℂ] Swatch (δx) := (Bx).mkContinuousOfExistsBound (chart_price Y H G S s)
lemma transferred(x:Swatch S): D (rx x)=ry (transfer Y H G S s x) := render_step ..

lemma display_same (m:ℕ) (f:Family (tent Y H)): distribute Y H s m f=Tapestry.exhibit Y H s m f :=
  (Tapestry.present_send ..).symm
/-- `block` at this rung agrees including the shape, cost and participating period
choices (permit and hosting conditions in arguments; no change from the `Y` under study). -/
lemma same_step (m n:ℕ)(p:Tapestry.Spanned Y S s m n)
    (t:Tivoli (δx) ((tent Y H).c (momentm Y m (s+1)))) (f:Swatch S) :
    block Y H s m n S (rx f)=ry (Tapestry.coupon Y H S s m n f) := by
  have h := Tapestry.costumed Y H s m n S p.1 p.2.2 f
  let g:= Tapestry.coupon Y H S s m n
  rw [Tapestry.coupon_spanned (g:=p)]
  apply stationary_ext Y H (s+1) (wingspan Λ l S) m t.hosp (booked ..) (texture ..)
  rw [reserved Y H s S m n p.1 (texture ..) t,display_same,←Tapestry.present_exhibit]
  unfold aboveD; rw [display_same,←Tapestry.present_exhibit]
  exact h.symm

include V in
lemma transfer_limit : Tendsto (fun r=> Tapestry.coupon Y H S s (i (G.rows r)) (k (G.columns r)))
    atTop (𝓝 (transfer Y H G S s)) := by
  refine (Metric.tendsto_nhds (a:=transfer Y H G S s)).mpr ?_
  intro ε hp
  let u:=spread S; have he:0≤u:=Nat.cast_nonneg _
  obtain ⟨c,pc,p⟩ := G.history.implements s S
  let d:=ε/(u+1); have h:0<d:=by unfold d; positivity
  have h':d*u<ε:= (mul_lt_mul_of_pos_left (lt_add_one u) h).trans_eq (div_mul_cancel₀ _ (by positivity))
  have ht:Tendsto (i ∘ G.rows) atTop atTop:= (V.pick.grow_i.comp G.history.growsA).tendsto_atTop
  filter_upwards [p d h,G.history.finance (s+1), ht.eventually (Tapestry.seasons Y H S s),ht.eventually (turning Y H (s+1) (wingspan Λ l S))] with a pa q u₀ v
  let f:= Tapestry.coupon Y H S s (i (G.rows a)) (k (G.columns a))
  change dist f (transfer Y H G S s) < ε
  rw [dist_eq_norm f (transfer Y H G S s)]
  refine lt_of_le_of_lt ?_ h'; apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg h.le he)
  intro x
  change ‖f x - transfer Y H G S s x‖≤ _
  apply sample_price Y H (wingspan Λ l S)
  unfold f
  rw [map_sub,←same_step Y H S s (i (G.rows a)) (k (G.columns a)) ⟨⟨q.depth,q.enters⟩,u₀⟩ v x,←transferred, mul_assoc]
  exact (pa _ (texture S K x) _ (rendered_price Y H S x)).2.2.1
include V in
lemma compact_resolution : IsCompactOperator (transfer Y H G S s) :=
  isCompactOperator_of_tendsto (transfer_limit Y H V G S s) (Eventually.of_forall fun n=> Tapestry.compact_coupon ..)
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.compact_resolution
