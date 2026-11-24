import YM.SU5.Assay.Escrow
import YM.SU5.Assay.Issuing
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
local notation "σ"=>P.rawSlot j x
local notation "β"=>P.base j x
local notation "κ"=>P.coffee j x
local notation "𝔤"=>P.Grips j x
local notation "ξ"=>P.prepared
local notation "μ"=>P.singleState j
local notation "⟪" T "⟫"=>inner ℂ Ω ((T:Y) Ω)
/-! Frame-exact price on earned slice; simultaneous convergence of
 raw operators may apply more broadly than that slice.

 `u` threshold on grid height needed for actual price; `s` width index.
-/
structure Porcelain (u:ℕ→ℕ)(f:ℕ→ℕ→P.Test)(a b:ℝ)(G:ℕ→ℕ→X)(M:ℕ→Y)(A:Y) :Prop where
 earned: ∀ᶠ s in atTop, ∀t≥u s,P.Grips j x t a b (f s t) (G s t)
 stationary: ∀s,P.Rehearses j x (G s) atTop (M s)
 next: BSOT M atTop A
 together:P.Rehearses j x (fun i:ℕ×ℕ=>G i.1 i.2) atTop A
variable {P j x}{f g:ℕ→ℕ→P.Test}{a b c d:ℝ}{G G':ℕ→ℕ→(P.ColorHil j x).Op}{M M':ℕ→(P.ManyF j x).Op}{A A':(P.ManyF j x).Op}
variable {u v z:ℕ→ℕ}
namespace Porcelain
variable (h:P.Porcelain j x u f a b G M A)
include h
lemma raise (e:∀ᶠs in atTop,u s ≤ z s): P.Porcelain j x z f a b G M A:=
  {h with earned:= (h.earned.and e).mono fun _ w t p=> w.1 t (w.2.trans p)}
lemma holds : ∀ᶠi in Escrow u, 𝔤 i.2 a b (f i.1 i.2) (G i.1 i.2):=
 (((Escrow.fst u).eventually h.earned).and (Escrow.pays u)).mono fun _ z=>z.1 _ z.2
lemma combine (k:P.Porcelain j x u g b c G' M' A'): P.Porcelain j x u (fun s t=>f s t*g s t) a c
  (fun s t=>G s t*G' s t) (fun s=>M s*M' s) (A*A'):=
 ⟨(h.earned.and k.earned).mono fun s w t p=>(w.1 t p).join (w.2 t p),fun s=>(h.stationary s).mul (k.stationary s),h.next.mul k.next,h.together.mul k.together⟩
lemma compound (k:P.Porcelain j x v g b c G' M' A'): P.Porcelain j x (fun s=>max (u s) (v s)) (fun s t=>f s t*g s t) a c
  (fun s t=>G s t*G' s t) (fun s=>M s*M' s) (A*A'):=
 (h.raise (Eventually.of_forall fun _=>le_max_left ..)).combine (k.raise (Eventually.of_forall fun _=>le_max_right ..))
lemma traces : BothWays u (fun s t=> μ t x (f s t)) (fun s=>⟪M s⟫) ⟪A⟫:=by
 have r:BothWays u (fun s t=>inner ℂ (Vac) (G s t (Vac))) (fun s=>⟪M s⟫) ⟪A⟫:=
   ⟨Eventually.of_forall fun s=>(h.stationary s).price,tendsto_const_nhds.inner (h.next.showAt Ω),h.together.price.comp (Escrow.visits u)⟩
 exact r.congr' (h.earned.mono fun _ w=>⟨rfl, fun _ k=> (w _ k).price⟩)
lemma claims {i₀:Axis}(y:P.Spectrum0 i₀)(e:x=P.advocate i₀ y j):
  BothWays u (fun s t=>P.singleState i₀ t y (f s t)) (fun s=>⟪M s⟫) ⟪A⟫:=by
 subst x;exact h.traces.congr' (Eventually.of_forall fun _=>⟨rfl,fun _ _=>P.single_agrees i₀ j y ..⟩)
-- verified at the actual positive present (indices with `f s t` raw and on calendar).
lemma calendar (e:a=0):
 (∀ᶠs in atTop,∀t≥u s,∃k:P.birthF j t (f s t), P.viewF j x t k=G s t (Vac)) ∧
 Tendsto (fun i:ℕ×ℕ=>G i.1 i.2 (Vac)) atTop (𝓝 (E (A Ω))):=by
 subst a
 exact ⟨h.earned.mono fun _ w _ q=>(w _ q).present,h.together.shows Ω⟩
end Porcelain
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
