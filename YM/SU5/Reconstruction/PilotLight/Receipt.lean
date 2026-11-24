import YM.SU5.Reconstruction.PilotLight.Steady
/-! Active Stack trajectories in the receipts of this state. -/
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxRecDepth 5700
set_option maxHeartbeats 470000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel
open Fock Lat Lifted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
local notation "Gt" => marks (timeMesh Λ)
variable (j : Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false (c j) →⋆ₐ[ℂ] ℂ)
open Chambers LightBudget
local notation "J₀"=> indoor Y H V G.history G.clipped j false (c j) χ
local notation "w'₀"=> doorstep Y H V G.history G.clipped j false (c j) χ
local notation "L"=> ride Y H V G.history G.clipped j false (c j) χ
local notation "F"=> osValue Y H V G j (c j) χ
local notation "T₀"=> OSvector Y H V G j (c j) χ
local notation "Pr"=> atEstate Y H V G.history G.clipped j false (c j) χ
local notation "Lp'"=> Follows Y H V G j (c j) χ
variable {A B : (indoor Y H V G.history G.clipped j false (c j) χ).Op}
variable (s w:ℕ)
variable {x y:Dome (tent Y H)}
local notation "g₁"=> hOne Λ s w
local notation "g₂" n:max=> hAll Λ s w n
local notation "b₁"=> bOne Λ s w
open SlabMark.Bankroll PhaseChoice Tapestry.Altitude Hearthbank
variable {S:Finset Cover}{n:ℕ}{a: Fin n → Cover}{Lw:ℕ}
/-- THIS campaign. data at each step preserving full lineage & Book etc.
Transfers norm & health, not preparing labels of future refinements (same price there). -/
structure Mixer (q d u:ℕ)(s:ℕ)(x:SU.Slot → Dome (tent Y H)):Prop where
  lesson : ∃ (v v':SU.Slot→ observable (tent Y H) true) (e:ℕ)(ζ:ℝ), 0<ζ∧
       Deliver Y H V s G w c d q u v v' ζ e ∧ x=(fun z=>resolutionProbe Y H (v' z))
  room (z:SU.Slot) : Traveler Y H V G c s w z (district q d u) (tileA q d u) (x z)

variable (q d u : ℕ) {Z Z':ℝ}(P:Papal.Cellarer Y H Z Z' q d u w)
variable {P': Panel Y H V G.history G.clipped 0 false (c 0)} {χ':P'.X}
include P
lemma attainable
 (h:Papal.RealSponsor Y H V G c P' u w q d χ') (a:∀ᶠ s in atTop,∀ᶠ e:ℕ in atTop,∃ ζ>0,∃ f f':SU.Slot → observable (tent Y H) true, Deliver Y H V s G w c d q u f f' ζ e): ∀ᶠ s:ℕ in atTop, ∃ x:SU.Slot → Dome (tent Y H), Mixer Y H V G c w q d u s x:=by
 filter_upwards [a] with s h'; obtain ⟨r,ζ,z,f,f',k⟩:=h'.exists
 exact ⟨_,⟨⟨f,f',r,ζ,z,k,rfl⟩,fun i=> felt_one Y H V G c s i q d u P k (((h.wonders s r ζ f f' z k).2 i 0 1 zero_lt_one).1)⟩⟩
omit P

-- arbitrary support shrink prescribed. explicitly at all larger resolutions (can preserve earlier heights or go higher as needed)
local notation "M'"=> Mixer Y H V G c w q d u
def Mixing :Prop:= ∀ᶠ s:ℕ in atTop, ∃ x:SU.Slot→ Dome (tent Y H), Mixer Y H V G c w q d u s x
private lemma climb {p:ℕ→ℕ→Prop}(h:∀ i:ℕ,∀ᶠ n:ℕ in atTop, p i n): ∃ ψ: ℕ→ℕ, StrictMono ψ ∧ ∀ i,p i (ψ i):=by
 choose f hf using fun i=>eventually_atTop.mp (h i)
 let ψ:ℕ→ℕ:=Nat.rec (f 0) (fun i r=>max (r+1) (f (i+1))); have he(i):ψ (i+1)=max (ψ i+1) (f (i+1)):=rfl
 refine ⟨ψ, strictMono_nat_of_lt_succ (fun i=> (Nat.lt_succ_self _).trans_le ?_), ?_⟩
 · rw [he]; exact le_max_left ..
 intro i; apply hf; cases i with| zero=> exact le_rfl|succ i=> rw [he]; exact le_max_right ..
lemma resolution_fund (u:ℕ) : Tendsto (fun s=> (hAll Λ s w u:ℝ)) atTop (𝓝 0):= NNReal.tendsto_coe.mpr (skinny (Λ:=Λ) _)
structure Trail (R:ℝ)(N t:ℕ→ℕ)(x:ℕ→SU.Slot → Dome (tent Y H)):Prop where
  posts (i:ℕ): Mixer Y H V G c w q d u (t i) (x i)
  moves : StrictMono t
  blocks (i:ℕ): 0<N i
  ignition : Tendsto N atTop atTop
  aperture (i:ℕ) : (hAll Λ (t i) w (N i):ℝ) ≤ R
  shrink : Tendsto (fun i=> hAll Λ (t i) w (N i)) atTop (𝓝 0)
variable {N:ℕ→ℕ} {R:ℝ}
lemma trailhead (R:ℝ)(h:0<R)(e:Mixing Y H V G c w q d u)(p:∀i:ℕ,0<N i)(g:Tendsto N atTop atTop)(A:ℕ): ∃ (t:ℕ→ℕ)(x:ℕ→ SU.Slot → Dome (tent Y H)), Trail Y H V G c w q d u R N t x ∧ ∀ i,A ≤ t i:=by
 have hv(i:ℕ):0< min R (amber i):= lt_min h (by unfold amber; positivity)
 obtain ⟨ψ,k,y⟩:=climb (fun i:ℕ=> (Filter.eventually_ge_atTop A).and ((resolution_fund (Λ:=Λ) w (N i)|>.eventually (gt_mem_nhds (hv i))).and e))
 choose x hx using fun i=> (y i).2.2
 have he(i): (hAll Λ (ψ i) w (N i):ℝ) ≤ min R (amber i):= (y i).2.1.le -- tune coe
 refine ⟨ψ,x,⟨hx,k,p,g,(fun i=> (he i).trans (min_le_left ..)),?_⟩,fun i=>(y i).1⟩
 exact NNReal.tendsto_coe.mp (squeeze_zero (fun i=> (hAll Λ (ψ i) w (N i)).property) (fun i=> (he i).trans (min_le_right ..)) amber_limit)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.attainable
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.trailhead
