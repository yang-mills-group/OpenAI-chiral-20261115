import YM.SU5.Reconstruction.PilotLight.Battery
import YM.SU5.Reconstruction.PilotLight.Indicator
/-! Battery bookkeeping. At every applicable stencil. -/
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
local notation "bP" n:max=> bAll Λ s w n
local notation "K₁"=> ticket Y H G s
local notation "Dp" n:max=> insideAt Λ l K false (alcove (hAll Λ s w n)) s
section actor
variable (n:ℕ)(p:0<w)(d:0<n)
include p d
noncomputable def appellant (p:0<w)(d:0<n)(v:Dp n): (J₀).Op := stripOp Y H V G j (c j) χ (bP n) (by rw [aTime]; exact tPositive (Λ:=Λ) s p d) (K₁ v.val) (by rw [aTime]; exact ticket_mem Y H G (insideAt_mono (alcove_in_strip ..) v.property))
local notation "Bₚ"=>appellant Y H V G j c χ s w n p d
lemma candidate (v:Dp n): Lp' (K₁ v.val) (bP n) (Bₚ v) := stripOp_follows ..
noncomputable def ledgerₚ (p:0<w)(d:0<n): insideAt Λ l (tent Y H) false (alcove (hAll Λ s w n)) s→ₗ[ℂ](J₀).Op where
 toFun:=appellant Y H V G j c χ s w n p d
 map_add' x y:= by
    apply unique_op Y H V G j (c j) χ (bP n) (candidate Y H V G j c χ s w n p d (x+y)); rw [Subalgebra.coe_add,map_add]; exact addScore Y H V G j (c j) χ (candidate Y H V G j c χ s w n p d x) (candidate Y H V G j c χ s w n p d y)
 map_smul' b v:= by
    apply unique_op Y H V G j (c j) χ (bP n) (candidate Y H V G j c χ s w n p d (b•v)); rw [Subalgebra.coe_smul,map_smul]; exact scaleScore Y H V G j (c j) χ (candidate Y H V G j c χ s w n p d v) b
-- for span evaluations extend to any Dome. Extension CASH arbitrary off submodule; NOT asserted there.
noncomputable def valuePort (p:0<w)(d:0<n): Dome (tent Y H)→ₗ[ℂ] (J₀).Op:= ((ledgerₚ Y H V G j c χ s w n p d).comp (((Dp n).toSubmodule.subtype).leftInverse))
local notation "Ψ"=> valuePort Y H V G j c χ s w n p d
lemma portent {v:Dome (tent Y H)} (q: v∈Dp n) : Lp' (ticket Y H G s v) (bP n) (Ψ v):=by
 let V':=((Dp n).toSubmodule.subtype); unfold valuePort; rw [LinearMap.comp_apply]
 rw [show ((Dp n).toSubmodule.subtype.leftInverse) v=⟨v,q⟩ from LinearMap.leftInverse_apply_of_inj (Dp n).toSubmodule.ker_subtype ⟨v,q⟩]; exact candidate Y H V G j c χ s w n p d ⟨v,q⟩
lemma exactly_here {v:Dome (tent Y H)} (q:v∈Dp n)(e : Lp' (ticket Y H G s v) (bP n) A): Ψ v=A:= unique_op Y H V G j (c j) χ (bP n) (portent Y H V G j c χ s w n p d q) e
end actor
section split
variable (S:Finset Cover)(z:SU.Slot){r:ℕ}(a:Fin r→ Cover)
variable (u n:ℕ)(p:0<w)(d:0<n)(t:0<u) (z':SU.Slot)
local notation "P"=> valuePort Y H V G j c χ s w n p d
local notation "P'"=> valuePort Y H V G j c χ s w u p t
variable (v:placement Λ)(T:ℂ)
local notation "Aq"=> pilotBeam Y H V G j (c j) χ v
/-/ factorization in this *exact* interpretation at those actual apertures -- not requiring
any continuity Sigma spectrum -- just cash after buying actor & clocks. Cot transported
for Gauge alone through same ancestry. Particular μ & Mink-edge values. N may differ.
 Width already epoch calibrated on these algebra citizens (incl separately on the unrequired gauge-inv Terms). -/
def CoolFactor (z' : SU.Slot)(p:0<w)(d:0<n)(t:0<u) : Prop :=
    ∀ (x y g m: Dome (tent Y H)), Clause (tent Y H) z S a w n true x y → Clause (tent Y H) z' S a w u true g m →
     Aq (valuePort Y H V G j c χ s w n p d (x*y)) (valuePort Y H V G j c χ s w u p t (g*m)) T=
       Aq (valuePort Y H V G j c χ s w n p d x) (valuePort Y H V G j c χ s w u p t g) T *
         Aq (valuePort Y H V G j c χ s w n p d y) (valuePort Y H V G j c χ s w u p t m) T

-- Every call permitted, even assembling actual chronological enquiries.
lemma legalSplit (p':∀ i:Axis, Between (tent Y H) i 0 (ruler Λ.block*w) S)(h:Clause K z S a w n true x y):
    ∃ R:Finset (Dome (tent Y H)), {x,y,x*y} ⊆ (R:Set (Dome (tent Y H))) ∧ ∀ v∈R,v∈Dp n ∧ Follows Y H V G j (c j) χ (K₁ v) (bP n) (P v) := by
 obtain ⟨h,g⟩:=clause_permitted Y H s w p p' h
 refine ⟨{x,y,x*y},?_,fun v e=>?_⟩; · simp
 have hp:v∈ Dp n:=by simp only [Finset.mem_insert,Finset.mem_singleton] at e; rcases e with l|l|l<;>subst v; exact h; exact g; exact (Dp n).mul_mem h g
 exact ⟨hp,portent Y H V G j c χ s w n p d hp⟩ -- tune
include t d
lemma noSplit_credit (p':∀ i:Axis, Between (tent Y H) i 0 (ruler Λ.block*w) S)(hp:Injective a)(h:x∈fieldBook z S a K w n)(g:y∈fieldBook z' S a K w u)
  (hx:CoolFactor Y H V G j c χ s w S z a u n v T z' p d t): Aq (P x) (P' y) T=0:=by
 refine Submodule.span_induction₂ (p:=fun x y _ _=> Aq (P x) (P' y) T=0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ h g
 · rintro _ _ ⟨u,x,b,rfl⟩ ⟨k,y,g,rfl⟩; rw [hx u x k y b g,(exactly_here Y H V G j c χ s w n p d (clause_permitted Y H s w p p' b).2 (every_cold Y H V G j c χ s w p' hp p b rfl)),zero_left,mul_zero]
 · intro _ _; rw [map_zero,zero_left]
 · intro _ _; rw [map_zero,zero_right]
 · intro x y z a b h v' e; rw [map_add,(allSolids Y H V G j (c j) χ v _ _ _ T).1,v',e,zero_add]
 · intro x y z a b h v' e; rw [map_add,(allSolids Y H V G j (c j) χ v _ _ _ T).2,v',e,zero_add]
 · intro k x y a b v1; rw [map_smul,(quota_scale Y H V G j (c j) χ v _ _ _ _).1,v1,mul_zero]
 intro k x y a b v1; rw [map_smul,(quota_scale Y H V G j (c j) χ v _ _ _ _).2,v1,mul_zero]
end split
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.portent
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.noSplit_credit
