import YM.SU5.Reconstruction.Brazier.Pins
import YM.SU5.Reconstruction.FirstWindows.Link
/-! Disaster test for gauge–matter factorization maintained in real normalized theory on one physical phase track. Don't claim gauge/matter decoupled terms are charged sectors in a Mink model; these are measurement counterparts to exact Poll budgets. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "Kx" t:max=> vistaFinish Y H t Z
local notation "Px" => LightBudget.prepaid Y H V G j C
namespace Encamp
open Hearth Tarmac Fortune SingleFrame Labor Fervor FirstWindows.Brazier.Path Marshal
variable {T:ℕ→Finset Tarmac}{e:ℕ→ℝ} (g:ℕ→ℝ)
variable (a : Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (U':displayAlgebra Y H V G.history G.clipped j false (c j) →⋆ₐ[ℂ] ℂ)
variable (t:ℕ→ℕ)(r:ℕ→Hearth Y H G j) (sf:Marshal.Reconstitution Y H V G Z j (c j) U' T g e t r)
variable {x y:Dome (tent Y H)}{b q:Bool}{U W:Set RSpace} (s:ℕ)
local notation "X'₀"=> Hearth Y H G j
local notation "ρ" n:max=> i (G.rows (t n))
local notation "μ" n:max=> k (G.columns (t n))
local notation "κa"=> displacement Y H V G.history G.clipped j false (c j) U' a (c a)
local notation "θ'"=> sameRead Y H V G a (c a) κa
-- before: Can assume lengths.Lower and choose occupancy reps
noncomputable abbrev thunder (x y:Dome (tent Y H))(n:ℕ):ℂ:= billing Y H G j s x y (i (G.rows (t n))) (k (G.columns (t n))) (r n)
local notation "Tp"=>thunder Y H G j t r s
structure Expose (x y:Dome (tent Y H))(U W:Set RSpace) : Prop where
 value : Tendsto (thunder Y H G j t r s x y) atTop (𝓝 (θ' s (x*y)))
 active : ∀ᶠ n:ℕ in atTop, AtSea Y H G j s x y (r n) (i (G.rows (t n))) (k (G.columns (t n))) (g n) U W
include sf
lemma pathway (p₁:x∈insideAt Λ l (tent Y H) b U s)(h:y∈insideAt Λ l (tent Y H) q W s)(hw:Disjoint U W):
 Expose Y H V G j g a c U' t r s x y U W:=by -- check g order
 obtain ⟨⟨Uₚ,o,l⟩,hb⟩:= (mem_insideAt ..).1 p₁
 obtain ⟨⟨Wp,e',w⟩,hp⟩:= (mem_insideAt ..).1 h
 let A':Tarmac:= splitShape s Uₚ Wp
 have hx : ∀ᶠ n:ℕ in atTop, AtSea Y H G j s x y (r n) (ρ n) (μ n) (g n) U W:=by
    filter_upwards [ (sf.admits A' 1 zero_lt_one), (((V.pick.grow_i.comp G.history.growsA).comp sf.deployment.late).tendsto_atTop).eventually (unwrapped Y H s (Uₚ∪Wp))] with i v eT
    exact earns_at Y H V G Z j (c j) U' s x y o e' _ _ (sf.deployment.authorize i _ le_rfl) v.1 l w hw eT -- order
 refine ⟨?_,hx⟩
 let f: FiniteGaugeDataPoly (tent Y H):= ⟨pinhole _ s (x*y),curve.mpr ⟨s,Altitude.short_pinhole s (x*y)⟩⟩
 have hw: will Y H V G Z j (c j) U' f=θ' s (x*y):=by
    rw [← will_across Y H V G Z j (c j) U' f a (c a)]
    exact (will_mark Y H V G Z a (c a) _ _ _ f.property).trans (os_ticket ..|>.symm)
 rw [←hw]; exact (sf.news f).congr' (hx.mono fun i h=> h.calculated.symm)
-- every requested interaction witness read this way; no Purchase of stage costs, just trajectory service
variable (u d: Cover)(S:Finset Cover)(slot: SU.Slot)(o: Cover)(u₀ z:ℕ)(F:Marks (tent Y H) true)(b₀:ℝ)
local notation "Fe"=>NoDecompose Y H V G a (c a) κa s u d slot u₀ z S o
local notation "Θ" f:max => FirstWindows.leg a u f
local notation "R" f:max=> reposition K d f
local notation "y'"=>fromStrict F
local notation "V₁"=>bufferedHull Λ l s (reflectedBox a 0 (streetBox K u S))
local notation "V₂"=>bufferedHull Λ l s (streetBox K d S)
local notation "Pq" x:max y:max=> Expose Y H V G j g a c U' t r s (FirstWindows.leg a u x) (reposition K d y) (V₁) (V₂)
local notation "TZ" x:max y:max=> thunder Y H G j t r s (FirstWindows.leg a u x) (reposition K d y)
-- count occ
omit sf
structure Amplified : Prop where
 report : LinkCheck Y H V G a (c a) κa s u d S slot o u₀ z F b₀
 approval : Pq y' y'
 loud : ∀ᶠ i:ℕ in atTop, 1/33 ≤ ‖(TZ y' y') i‖
 equity : ∃ x y A' B': Dome (tent Y H), NoDecompose Y H V G a (c a) κa s u d slot u₀ z S o x y A' B' ∧ Pq x y ∧ Pq A' B' ∧ Pq (A'*x) (B'*y) ∧
     ∃ δ>0,∀ᶠ i:ℕ in atTop, δ ≤ ‖ (TZ (A'*x) (B'*y)) i - ((TZ x y) i)*((TZ A' B') i)‖
include sf
lemma checkMate (v:LinkCheck Y H V G a (c a) κa s u d S slot o u₀ z F b₀): Amplified Y H V G j g a c U' t r s u d S slot o u₀ z F b₀:=by
 let h:= pathway Y H V G Z j g a c U' t r sf s v.first v.second v.apart
 obtain ⟨x,y,z₁,z₂,o₀⟩:= v.see_basis; obtain ⟨hz,hf,hx⟩:= witness_charge Y H V G a (c a) κa s u d o₀ v.apart
 let hy:=pathway Y H V G Z j g a c U' t r sf s hz.left hz.right v.apart
 let hp:=pathway Y H V G Z j g a c U' t r sf s hf.left hf.right v.apart
 let tq:=pathway Y H V G Z j g a c U' t r sf s hx.left hx.right v.apart
 refine ⟨v,h,?_,x,y,z₁,z₂,o₀,hy,hp,tq,?_⟩
 · exact h.value.norm.eventually (eventually_ge_nhds (lt_of_lt_of_le (show (1:ℝ)/33<1/32 by norm_num) v.answer)) -- tune direction
 let w:= o₀.operational; exact ⟨_,half_pos w, ((tq.value.sub (hy.value.mul hp.value)).norm.eventually (eventually_ge_nhds (half_lt_self w)))⟩
end Encamp
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
