import YM.SU5.Reconstruction.Chambers.Cost
import YM.SU5.Reconstruction.Cone.Test
import YM.SU5.Reconstruction.Seams.Hole
/-! # actual positional chart in the full continuity sector -/
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
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "D" => Domain Y H G false
local notation "Gt" => marks (timeMesh Λ)
local notation "K₀"=> tent Y H
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
set_option quotPrecheck false
local notation "P"=> (C₀).orthogonalProjectionOnto
local notation "θ"=> flipMark j K
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "κ" p:max=> move K p
-- even if saunters only a sector, can always define the interpretation. Qua preservation of ALL
-- readings, must buy full price here. Eq On all-chambers of CP2 WITHOUT such assumption.
noncomputable def coreOs : Domain Y H G false (flank j 0) →ₗ[ℂ] fort Y H V G.history G.clipped j false C χ :=
  (P).toLinearMap.comp (OSvector Y H V G j C χ)
local notation "Vo"=> coreOs Y H V G j C χ
local notation "κ₀"=> OSvector Y H V G j C χ
local notation "raw"=> atEstate Y H V G.history G.clipped j false C χ
noncomputable def opCarries (x : (J₀).Op) : (G₀).Op := (P).comp (x.comp (C₀).subtypeL)
noncomputable def bridgeEstate (p : placement Λ) : (G₀).Op :=
  Chambers.Schedule.route (S) (coordinates Λ p)
local notation "Pr"=> bridgeEstate Y H V G j C χ
section full
variable (tC : saunters Y H V G.history G.clipped j false C χ=⊤)
include tC
lemma complete_p (x : J₀) : ((P x:G₀).val:J₀) = x := by
  exact (C₀).starProjection_eq_self_iff.mpr (tC.symm ▸ Submodule.mem_top)
lemma voice_full (x : Domain Y H G false (flank j 0)) : (Vo x).val=κ₀ x := complete_p Y H V G j C χ tC _ -- simp lemma extra arg unsimp
lemma carries_full (A : (J₀).Op) (x : G₀) : ((opCarries Y H V G j C χ A x:G₀).val:J₀)= A (x.val:J₀):= complete_p Y H V G j C χ tC _
omit tC in
lemma estate_full (p:placement Λ) (x:G₀): ((Pr p x:G₀).val:J₀)=raw p (x.val:J₀) := by
  let f:=(P); unfold bridgeEstate Chambers.Schedule.route
  rw [ContinuousLinearMap.comp_apply,show (coordinates Λ p)=ConePrice.face p from rfl]
  let Hx:=glass_heat (Ω₀) (daylight (timeMesh Λ)) (L) (follows_road Y H V G.history G.clipped j false C χ) (Real.toNNReal (ConePrice.face p j)) ((S).U (diameter (ConePrice.face p)) x)
  change _ = (L).E _ ((Ω₀).track.raw (look j) _ (x.val:J₀)); refine Hx.trans (congrArg ((L).E _) (glass_move (Ω₀) (daylight (timeMesh Λ)) (L) (follows_road Y H V G.history G.clipped j false C χ) x p))
lemma voice_move (p:placement Λ) (x:Domain Y H G false A₀) (v : 0 ≤ coordinates Λ p j) (hx : move K p x.val ∈ Domain Y H G false A₀) :
    Vo ⟨move K p x.val,hx⟩= Pr p (Vo x):= by
 apply Subtype.ext; rw [estate_full,voice_full Y H V G j C χ tC,voice_full Y H V G j C χ tC]; exact transported_ket Y H V G j C χ x.val x.property p v hx
lemma voice_follows {u:Gt}{x:Sky (tent Y H)}{A:(J₀).Op} (h : Follows Y H V G j C χ x u A) (p:Domain Y H G false A₀) :
    ∃ w:Domain Y H G false (flank j 0), w.val=x*move K (eject j u) p.val ∧ Vo w=opCarries Y H V G j C χ A (Vo p):=by
 obtain ⟨w,b,v⟩:=h.graph p; refine ⟨w,b,Subtype.ext ?_⟩; rw [carries_full Y H V G j C χ tC,voice_full Y H V G j C χ tC,voice_full Y H V G j C χ tC,v]
end full

section grids
variable {v : Axis}
lemma selectRay {A : Type*} [AddMonoid A] (k : Axis) (x y : A) : (eject k x)+eject k y= eject k (x+y) := by
  ext i; by_cases v:i=k<;> simp [v]; -- orientation
lemma reverse_eject (x : Gt) : reverseOne j (eject j x)=eject j (-x):= by ext1 i; by_cases v:i=j<;>simp [reverseOne,v]
lemma eject_neg {A : Type*}[AddGroup A] (x:A) : eject j (-x)= - eject j x:= by ext i; by_cases h:i=j<;> simp [h]

@[simp] lemma bridge_time (p:Gt) : Pr (eject j p)= (S).E (ℜ (p:ℝ)) := by
  unfold bridgeEstate Chambers.Schedule.route; rw [coordinates_eject, eject_at]
  rw [show @diameter j (eject j (p:ℝ))=0 from ?_, (S).uZero]; rfl
  apply Subtype.ext; change WithLp.toLp 2 _- _ • basis j=(0:E4); ext i; by_cases v:i=j<;> simp [v]

abbrev transversal (b : Axis) (a : Axis)(u:a ≠ b) : OS.Cross b := ⟨basis a,by change basis a b=0; simp [u.symm]⟩
@[simp] lemma transversal_norm (u : v≠j): ‖transversal j v u‖=1:= by change ‖basis v‖=_; simp
lemma across_time (v:Axis) (z t:Gt) (e : v≠j) :
    Pr (eject j z + eject v t) = ( (S).U ((t:ℝ) • transversal j v e)).comp ((S).E (ℜ (z:ℝ))) := by
  unfold bridgeEstate Chambers.Schedule.route; rw [map_add, coordinates_eject, coordinates_eject,Pi.add_apply,eject_at,eject_away v (t:ℝ) j e.symm, add_zero, (S).independent]
  rw [show @diameter j (eject j (z:ℝ)+ eject v (t:ℝ))= (t:ℝ) • transversal j v e from ?_]; apply Subtype.ext
  ext i; by_cases p:i=j; · subst i; change (diameter _).val j = (t:ℝ)*(basis v j); rw [show (diameter (a:=j) _).val _=0 from (diameter (a:=j) _).property]; simp [e.symm]
  rw [diameter_at _ i p]; by_cases w:i=v <;> simp [w,p,transversal,e]
end grids

section chart
variable (tC : saunters Y H V G.history G.clipped j false C χ=⊤)
variable (a b : Sky (tent Y H)) (u v : MeshClock.marks (timeMesh Λ)) (A B : (indoor Y H V G.history G.clipped j false C χ).Op)
variable (Lt t x y:placement Λ) (p w: Domain Y H G false (flank j 0))
local notation "P₀" => Domain Y H G false (flank j 0)
-- building block optimization: external L may have negative *or* positive time displ Lt;
-- readability of θ p granted for any p positive. pays currency even when measuring in k-axis slit.
def tab (J : Calibration) (Lt x y t:placement Λ) (p a b w:Sky J): Sky J :=
  move J Lt p * (move J x a * (move J y b * move J t w))
local notation "f₁" t:max => eject j t
local notation "Ot"=> opCarries Y H V G j C χ

include tC
lemma flash (p : Domain Y H G false (flank j 0)) (h:Follows Y H V G j C χ a u A) (Hx : 0≤ ((x-Lt) j:ℝ))
    (Hv : 0≤ ((y-(x+eject j u)) j:ℝ)) :
   ∃ w: Domain Y H G false (flank j 0),w.val= move K (x-Lt) a* move K (y-Lt) p.val ∧
       Vo w=Pr (x-Lt) (Ot A (Pr (y-(x+f₁ u)) (Vo p))) := by
 let q:= y-(x+eject j u); let p' := move K q p.val; let k : p'∈ D A₀:= later_frame Y H V G j p.val q p.property Hv
 obtain ⟨w,b,v⟩ := voice_follows Y H V G j C χ tC h (⟨p',k⟩ : P₀); let Lt₁:=x-Lt; let hz := later_frame Y H V G j w.val Lt₁ w.property Hx
 refine ⟨⟨_,hz⟩,?_,?_⟩
 · change move K Lt₁ w.val=_; rw [b]; change move K Lt₁ (a * move K (eject j u) p')=_; unfold p'; rw [move_prod,move_sum,move_sum]; rw [show Lt₁+ (eject j u)+q = y-Lt from (by unfold Lt₁ q; abel)] -- association
 rw [voice_move Y H V G j C χ tC Lt₁ w Hx, v, show y-(x+eject j u)=q from rfl, ← voice_move Y H V G j C χ tC q p Hv k]

lemma purchases (h:Follows Y H V G j C χ a u A) (g:Follows Y H V G j C χ b v B) (Hx :0≤ ((x-Lt) j:ℝ)) (Hy:0≤ ((y-(x+eject j u)) j:ℝ)) (Ht:0≤ ((t-(y+eject j v)) j:ℝ)) :
    ∃ k : tab K Lt x y t (θ p.val) a b w.val ∈ Domain Y H G false Set.univ,
      osValue Y H V G j C χ ⟨tab K Lt x y t (θ p.val) a b w.val,k⟩= inner ℂ (Vo p)
        (Pr (x-Lt) (Ot A (Pr (y-(x+ eject j u)) (Ot B (Pr (t-(y+ eject j v)) (Vo w)))))) := by
  obtain ⟨z,d,e⟩ := flash Y H V G j C χ tC b v B y y t w g (by simp) Ht -- bind order
  obtain ⟨k,hk,he⟩:= flash Y H V G j C χ tC a u A Lt x y z h Hx Hy
  rw [sub_self,show Pr 0=(S).E (0:ℝ≥0) from ?_, (S).eZero,ContinuousLinearMap.id_apply] at e
  swap; · convert bridge_time Y H V G j C χ (0:Gt) using 2 <;> simp
  have hm : tab (tent Y H) Lt x y t (θ p.val) a b w.val = move K Lt (θ p.val * k.val):= by
    unfold tab; rw [hk,d]; simp only [sub_self, move_by_zero, move_prod, move_sum]; rw [show Lt+(x-Lt)=x from by abel, show Lt+(y-Lt)=y from by abel]; -- association tune
    rw [show Lt+(y-Lt+(t-y))=t from by abel]
  let w':= paired_forever Y H G j p.val k.val p.property k.property
  let h' : move K Lt (θ p.val*k.val)∈ D univ := slides_univ .. ▸ moving Y H V G Lt _ w'
  refine ⟨hm.symm ▸ h',?_⟩
  calc
    _= F ⟨move K Lt _,h'⟩ := by apply congrArg F; exact Subtype.ext hm
    _= F ⟨θ p.val*k.val,w'⟩ := moving_value ..
    _ = inner ℂ (Vo p) (Vo k) := by change _= inner ℂ ((Vo p).val:J₀) ((Vo k).val:J₀); rw [voice_full Y H V G j C χ tC,voice_full Y H V G j C χ tC]; exact (registered_pair ..).symm
    _=_ := by rw [he,e] -- bridge zero? simp did
end chart
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
