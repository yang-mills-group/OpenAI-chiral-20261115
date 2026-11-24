import YM.SU5.Reconstruction.PilotLight.Mezzanine
import YM.SU5.Reconstruction.Crease.Regional
/-! The CP11 REAL singlet-algebra definition. Connect our powering progress to it. At EVERY
$Stage.Column$ witness: true local Script at tBoard through unmetered Footprint. Note that **all** these
limits scalar; progress is unbroken buy AND interaction testimony at their $Eu+Wick ports.
THIS STAGE BY ITSELF DOESN'T EXCLUDE bare SCALAR sector on this world. See docs. -/
set_option autoImplicit false
set_option synthInstance.maxSize 32000
set_option maxRecDepth 5000
set_option maxHeartbeats 420000
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
open Chambers LightBudget Crease
open _root_.YM.BridgeClub Anvil
variable (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
  (a:Axis)
  (χ : displayAlgebra Y H V G.history G.clipped a false (c a) →⋆ₐ[ℂ] ℂ)(j:Axis)
local notation "Χ" j:max => displacement Y H V G.history G.clipped a false (c a) χ j (c j)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (c i) (Χ i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (c i) (Χ i)
local notation "L" i:max=> ride Y H V G.history G.clipped i false (c i) (Χ i)
local notation "ϴ" i:max=> (opCarries Y H V G i (c i) (Χ i))
local notation "Ln" i:max=> motor Y H V G i c (Χ i)
variable {R:ℝ} {w q d u:ℕ} {p N:ℕ→ℕ} {x:ℕ→ SU.Slot→ Dome (tent Y H)}
variable (W0:Trail Y H V G c w q d u R N p x)
variable (z:SU.Slot)
noncomputable def motorSpec (w:ℕ)(x:ℕ→ SU.Slot→ Dome (tent Y H))(p N:ℕ→ℕ)(z:SU.Slot)(i:ℕ): Sky (tent Y H):= ticket Y H G (p i) (lantern (tent Y H) (x i z) w (N i))
local notation "Xn"=> motorSpec Y H G w x p N z
local notation "kₚ"=> fun i:ℕ=> bAll Λ (p i) w (N i)
variable {h:ℕ → ℕ}(t:Tendsto h atTop atTop)
include W0 t
lemma luminousPort : Slip Y H V G c a χ j (Xn ∘ h) ((kₚ) ∘ h) (((Ln j) W0 z) ∘ h) (-1):=by -- argument order tune
 have he(i:ℕ): (bAll Λ (p i) w (N i):ℝ)=hAll Λ (p i) w (N i):= aTime ..
 refine ⟨fun i=>(ChargeFrame.fills Y H V G j c (Χ j) W0 z (h i)).funded,fun i=> ?_, ?_, ⟨?_,?_⟩⟩
 · change 0 < (bAll Λ (p (h i)) w (N (h i)):ℝ); rw [he]; exact tPositive (Λ:=Λ) _ (powered Y H V G c W0) (W0.blocks _)
 · simp only [Function.comp_apply,he]; exact (NNReal.tendsto_coe.mpr W0.shrink).comp t
 · exact ⟨2,by norm_num,Filter.Eventually.of_forall fun i=> (Hearthbank.weak_contour ..).trans (pumps Y H V G j c (Χ j) W0 z (h i))⟩
 intro x y; let Gm(i):= ((Ln j) W0 z) (h i)
 have ht:Tendsto (fun i=> (ϴ j) (Gm i) y) atTop (𝓝 (-y)):= costs_there Y H V G j c (Χ j) (fun x=> ((maintains Y H V G j c (Χ j) W0 z 0 0 x).1).comp t) y
 exact tendsto_const_nhds.inner ht
-- every designated REAL playback for this shrinking pointed detector interpretation (use even R>0 given in support planning). Requests occupancy transported without Fol.P.Stage requires support budgets.Radii. Display grants even in ambient realm. -/
omit t
variable (v: Axis → marks (timeMesh Λ))
include W0
-- Exact resort V all directions; can shrink in all components ANY sizes v, orientation Γ shelf. Early continuations at CP prescription.
lemma illuminated (vp:∀ i:Axis,i≠j → 0<(v i:ℝ)) : ∀ᶠ r:ℕ in atTop,
   let m:= fun i:ℕ=> i+r; let B:= (Ln j) W0 z; let Z:= Xn ∘ m; let h:= (kₚ) ∘ m
   Slip Y H V G c a χ j Z h (B∘m) (-1) ∧ (∀ n, Z n∈ D true (Tarp j 0 (fun i:Axis=> (v i:ℝ)) (h n:ℝ))) ∧
          ∀ i:Axis,i≠j → ∃ P:ℕ→ (J₀ i).Op, Perpendicular Y H V G i (c i) (Χ i) (v i) 0 Z P := by
    have he(i:ℕ): ((kₚ) i:ℝ)=hAll Λ (p i) w (N i):= aTime ..
    have ht:Tendsto (fun i=> ((kₚ) i:ℝ)) atTop (𝓝 0):=by simp_rw [he]; exact NNReal.tendsto_coe.mpr W0.shrink
    have hp: ∀ᶠ n:ℕ in atTop,∀ i:{i:Axis//i≠j}, (bAll Λ (p n) w (N n):ℝ) ≤ (v i.val:ℝ):= Filter.eventually_all.mpr (fun i=> ht.eventually (ge_mem_nhds (vp i i.property)))
    obtain ⟨r,hr⟩:= eventually_atTop.mp hp
    filter_upwards [eventually_ge_atTop r] with n d
    intro m B Z A; have hu(i:ℕ):r ≤ m i:= d.trans (Nat.le_add_left ..)
    refine ⟨luminousPort Y H V G c a χ j W0 z (?_), fun k=> ?_,fun i d=>?_⟩ -- order t?
    · exact (strictMono_id.add_const n).tendsto_atTop
    · have hx:=ticket_mem Y H G (ChargeFrame.fills Y H V G j c (Χ j) W0 z (m k)).age; apply domain_mono Y H G _ hx; intro y p'
      change y j∈ Set.Icc 0 ((bAll Λ (p (m k)) w (N (m k))):ℝ) ∧ _; refine ⟨?_,fun i hi=>?_⟩;
      · rw [aTime]; exact p' j
      simpa only [Pi.zero_apply, zero_add] using (show y i∈ Set.Icc 0 (v i:ℝ) from ⟨(p' i).1,(p' i).2.trans ((he (m k)) ▸ (hr _ (hu k) ⟨i,hi⟩))⟩)
    choose M t' hf using fun k:ℕ=> Hearthbank.padding Y H V G i (c i) (Χ i) (show bAll Λ (p (m k)) w (N (m k)) ≤ v i from hr _ (hu k) ⟨i,d⟩) (ChargeFrame.fills Y H V G i c (Χ i) W0 z (m k)).funded
    refine ⟨M,fun k=> by change Follows Y H V G i (c i) (Χ i) (FirstWindows.move (tent Y H) (eject i (-(0:Gt))) _) _ _; rw [neg_zero,eject_zero,move_by_zero]; exact t' k,2,fun k=>?_⟩
    exact (Hearthbank.weak_contour Y H V G i (c i) (Χ i) _).trans ((hf k).trans (pumps Y H V G i c (Χ i) W0 z _))
include z
lemma sighted (vp:∀ i:Axis,i≠j→ 0<(v i:ℝ)) : Sight Y H V G c a χ j 0 v (-1):=by
 obtain ⟨r,g,he,hw⟩:=(illuminated Y H V G c a χ j W0 z v vp).exists; exact ⟨vp,_,_,_,g,he,hw⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.illuminated
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.sighted
