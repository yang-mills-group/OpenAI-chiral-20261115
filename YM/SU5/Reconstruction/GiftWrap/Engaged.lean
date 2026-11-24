import YM.SU5.Reconstruction.GiftWrap.PrivateBall
import YM.SU5.Reconstruction.Vermont.Spirebook
/-! # Getting global true occupancy from cheaper criterion. Rank big payment not required -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "X" i:max=> OSvector Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open CrossedFrame
local notation "U"=>flank j 0∩flank z 0
local notation "Λ₁" i:max=>onceLens Y H V G C a χ i
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
local notation "Tm" i:max=> Picket.trans (S₀ i)
local notation "Ω" i:max=> Ω₀ i
local notation "Sq" => (S₀ j)
namespace Boots
local notation "lu" x:max=> (Tm j) ((x:ℝ) • basis z)
local notation "BC" => parcelUp Sq
open Quartz Quartz.Ship Quartz.Waltz Quartz.Bouy Sail Lens
local notation "M₀"=>floor Y H V G C a χ j univ
local notation "Ms"=>floor Y H V G C a χ j
local notation "Λ0" => parish M₀ (Ω j)
local notation "Vol" => owns_it M₀ (Ω j)
include F
lemma rollAnyWorld (x:E4)(A':(G₀ j).Op) (k:A'∈ M₀) : BC x A'∈ M₀ := translation_bound Y H V G C a χ F j univ univ x (subset_univ _) _ k
omit F
-- cheap version. illuminates equivalence to raw acquisition on stars for all x from weak Smith. then costs core premise
noncomputable def Accessible :Prop:= ∀ (U':Set RSpace)(d:Gt),U'⊆ Chambers.strip j 0 d→ IsCompact U'→0 < (d:ℝ) → ∀ (x:Sky (tent Y H))(A':(J₀ j).Op), x∈ Ds U' →(Q j) x d A' →∃ (W:Set E4),∃ M, Optical Y H V G C a χ j W d ((Π j) A') M
lemma becauseBooked (k:Registered Y H V G C a χ j) : Accessible Y H V G C a χ j:=fun U' d h v p x A' u e=> let t:= k U' d h v p x A' u e; ⟨_, t⟩
include F
open Schedule
lemma attracts (p:Accessible Y H V G C a χ j) : owns_it (floor Y H V G C a χ j univ) (Ω₀ j):= by
 intro x; refine closure_minimal ?_ (Submodule.isClosed_topologicalClosure _) (compass_domain_dense Y H V G j (C j) (w j) x)
 rintro _ ⟨v,rfl⟩; obtain ⟨W,c,u,e⟩:= (compact_domain Y H G).1 v.property; obtain ⟨r,r',s,h⟩:= shutters (daylight Tx) j c
 obtain ⟨t',u0⟩:= very_late (a:=max 0 (r':ℝ)) (daylight Tx); have r0:0<(t':ℝ):=(le_max_left ..).trans_lt u0; have H0: W⊆ Chambers.strip j 0 t':= fun q hq=> ⟨u hq, (h q hq).2.le.trans ((le_max_right ..).trans u0.le)⟩
 obtain ⟨A,d⟩:= fits Y H V G j (C j) (w j) t' r0 v.val (domain_loose Y H G _ (domain_mono Y H G H0 e)); have hx:(Π j) A (Ω j)=(Os j) v:= (Reflector.carries Y H V G C a χ j v.val _ d (F.present j) r0).1 -- defeq inclusion?
 obtain ⟨U',M,u'⟩:= p W t' H0 c r0 v.val A e d; obtain ⟨c',e'⟩:= u'.armour
 change (Os j) v∈ Λ0; rw [← hx]; exact thermallyPaid Sq (Ω j) M₀ (fun _=> compass_origin ..) (rollAnyWorld Y H V G C a χ F j) (sober Y H V G C a χ j U' _ (subset_univ _)) e' u'.fare
end Boots
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
