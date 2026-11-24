import YM.SU5.Reconstruction.Trap.Invoice
import YM.SU5.Reconstruction.UVPrice.Spring
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
namespace LightBudget
open SlabMark MeshClock ConePrice SelectionAnalysis
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "D" => Domain Y H G true
local notation "Gt" => timeMesh Λ
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "J₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "C₀"=> saunters Y H V G.history G.clipped j false C χ
local notation "G₀"=> fort Y H V G.history G.clipped j false C χ
local notation "Ω₀"=> mainsea Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "S"=> peninsula Y H V G.history G.clipped j false C χ
local notation "Π" x:max=> physicalKet Y H V G j C χ x
local notation "F"=> osValue Y H V G j C χ
local notation "A₀"=> flank j 0
local notation "ψ"=> marks (timeMesh Λ)
local notation "θ"=> gram j (tent Y H)
local notation "aU"=> shop j (tent Y H)
local notation "bF"=> floor j (tent Y H)
/-- supplement 3 reading BASE test in SAME phase -/
def Soft (r e δ:ℝ) : Prop:= ∀ (a:Axis)(_:a≠j)(z:ψ),0<(z:ℝ)→ (z:ℝ)<e→ let t:= Picket.byStamp j a z
                                        ∀ f:Sky (tent Y H), f∈D (flank j r)→∀ (k₁ : θ (aU t f)∈ Domain Y H G false univ) (k₂ : θ (bF t f)∈ Domain Y H G false univ)(k₃: θ f∈ Domain Y H G false univ),
                                           ( (F) ⟨θ (aU t f),k₁⟩).re ≤ ( (F) ⟨θ (bF t f),k₂⟩).re+δ*((F) ⟨θ f,k₃⟩).re
abbrev OrderSmall (r:ℝ) := ∀ δ:ℝ,0<δ→ ∃ e>0,Soft Y H V G j C χ r e δ
variable {r δ e : ℝ}
private lemma weight_premium (f:Sky (tent Y H))(z: placement Λ) (v : 0≤ coordinates Λ z j) (b : f∈ D A₀)
    (k₁ : θ (aU z f)∈ Domain Y H G false univ) (k₂ : θ (bF z f)∈ Domain Y H G false univ) (k₃: θ f∈ Domain Y H G false univ) :
    (F ⟨θ (aU z f),k₁⟩).re ≤ (F ⟨θ (bF z f),k₂⟩).re+ δ*(F ⟨θ f,k₃⟩).re ↔
      let t := (coordinates Λ z j).toNNReal
      let x := physicalKet Y H V G j C χ ⟨f,b⟩
      ‖(L).E t (transverse_play (Ω₀) z x)-(L).E t x‖^2 ≤ ‖x-(L).E t x‖^2+δ*‖x‖^2 := by
  let t := (coordinates Λ z j).toNNReal
  let h:= budget_legs Y H V G j 0 f z b v
  rw [gram_pays Y H V G j C χ _ h.1, gram_pays Y H V G j C χ _ h.2,gram_pays Y H V G j C χ f b]
  let u : 0≤ coordinates Λ (onlyTime j z) j:= by simp; exact v
  let f' := move K (onlyTime j z) f; let b₀:= budget_base Y H V G j 0 f (onlyTime j z) b u
  let p := (⟨move K z f,budget_base Y H V G j 0 f z b v⟩: D (flank j 0)); let w :=(⟨f',b₀⟩: D (flank j 0)); let y := (⟨f,b⟩: D (flank j 0))
  have hu : Π p=(L).E t (transverse_play (Ω₀) z (Π y)):= physical_move Y H V G j C χ f b z v p.property
  have hp : Π w=(L).E t (Π y) := by dsimp only [t]; rw [← plaza]; exact physical_move Y H V G j C χ f b _ u w.property -- defeq?
  change ‖physicalKet Y H V G j C χ (p-w)‖^2 ≤ ‖physicalKet Y H V G j C χ (y-w)‖^2+ _ ↔ _
  rw [map_sub,map_sub,hu,hp]
lemma soft_pay (p : 0≤r) : Soft Y H V G j C χ r e δ ↔ Roy.Cheaper (L) (Ω₀) e δ:= by
 constructor
 · intro t a z h hz x; let w:=Picket.byStamp j a z; let d:=(coordinates Λ w j).toNNReal; have hp : coordinates Λ w∈ ConePrice.CostDomain j e:= Picket.starch (Ω₀) a z h hz
   let Eq x:=(L).E d x; let S₀:= ConePrice.transverse_play (Ω₀) w
   let T:={x : J₀|‖Eq (S₀ x)-Eq x‖^2 ≤ ‖x-Eq x‖^2+δ*‖x‖^2}
   have hE: Continuous Eq:= ((L).E _).continuous
   have hT: IsClosed T:= isClosed_le (by fun_prop) (by fun_prop)
   refine closure_minimal ?_ hT (TimeMesh.dense_flanks Y H V G j C χ r x)
   rintro _ ⟨f,k,v,rfl⟩; obtain ⟨g,g'⟩:= pressure_coverage Y H V G j w f k p hp
   let h1:=domain_loose Y H G _ g; let h2:= domain_loose Y H G _ g'; let h3:=gram_covered Y H G j f v; exact (weight_premium Y H V G j C χ f w hp.1.le v h1 h2 h3).1 (t a a.property z h hz _ k h1 h2 h3)
 intro h a b z t e y f s k k' k3; let v:= (Picket.starch (Ω₀) ⟨a,b⟩ z t e); refine (weight_premium Y H V G j C χ f _ v.1.le (domain_mono Y H G (TimeMesh.flank_mono j p) s) k k' k3).2 (h ⟨a,b⟩ z t e _)
open Roy
lemma soft_ready (p:0≤r)(h: OrderSmall Y H V G j C χ r): saunters Y H V G.history G.clipped j false C χ=⊤ ∧ Wheater (S):=by
 have he: SmallCost (L) (Ω₀):= fun δ t=> (h δ t).imp fun e ⟨v,b⟩=> ⟨v,(soft_pay Y H V G j C χ p).1 b⟩
 have u:= follows_road Y H V G.history G.clipped j false C χ; exact ⟨true_room (L) (Ω₀) u he,cost_back (L) (daylight (timeMesh Λ)) (Ω₀) u he⟩
lemma budget_zero (p:0 ≤ r)(v:0<e)(g : Ivory Y H V G j C χ r e) : OrderSmall Y H V G j C χ r:=by
 intro δ t; refine ⟨e,v,fun a z h x y f b w w' w₀=>?_⟩; have he:= g a z h x y f b w w'
 rw [gram_pays Y H V G j C χ f (domain_mono Y H G (TimeMesh.flank_mono j p) b)]
 exact le_add_of_nonneg_right (show 0 ≤ δ* _ from by positivity)|>.trans' he
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
