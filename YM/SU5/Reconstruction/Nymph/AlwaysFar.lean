import YM.SU5.Reconstruction.Seams.Far
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
open Sail Submodule Schedule
local notation "Pr"=> bridgeEstate Y H V G j C χ
local notation "Vo"=> coreOs Y H V G j C χ
local notation "N"=> Domain Y H G false (flank j 0)
variable (v : Axis) (hv : v≠j)
local notation "Os"=> compassKet Y H V G j C χ
-- Strengthen the CP3 Reeh result; for the projected density the assumption of full spatial continuity can be DROPPED (use via projection).
local notation "V'" => turnstile Y H V G.history G.clipped j false C χ
local notation "B₁" => (saunters Y H V G.history G.clipped j false C χ).starProjection
local notation "Xi"=> atEstate Y H V G.history G.clipped j false C χ
lemma commutes_plane (p:placement Λ): Commute (B₁) (Xi p):=by
  rw [← stack_projection]; apply Commute.symm; apply Alliance.ground
  intro i _ z; let T:= ((V').crew i).play z
  let t:= Real.toNNReal (p j :ℝ)
  have h:Commute T ((L).E t):= follows_road Y H V G.history G.clipped j false C χ i z t
  have he:Commute T ((V').raw (look j) (fun a=> p a.val)):= ((V').hard _ T (fun a _ y=>(V').cCom a i y z) _).symm
  exact (h.mul_right he).eq
lemma despite (p:placement Λ) (x:Domain Y H G false A₀) (v : 0≤ coordinates Λ p j)(y:move (tent Y H) p x.val∈ N):
    Vo ⟨move (tent Y H) p x.val,y⟩= Pr p (Vo x):=by
  apply Subtype.ext
  rw [estate_full]
  change (B₁) (OSvector Y H V G j C χ ⟨move (tent Y H) p x.val,y⟩)= _
  rw [transported_ket Y H V G j C χ x.val x.property p v]; exact congrArg (fun T:(J₀).Op=>T (OSvector Y H V G j C χ x)) (commutes_plane Y H V G j C χ p).eq
section spectral
variable (hC: ConePrice.Forward (peninsula Y H V G.history G.clipped j false C χ))
include hC hv
lemma even_closer (u:ℝ)(b:Bool) : Dense (far Y H V G j C χ v u b : Set (fort Y H V G.history G.clipped j false C χ)) := by
  let A:= far Y H V G j C χ v u b; let s:=timeMesh Λ; let w:Gt:= notch (timeMesh Λ) 0 1
  let t:= (w:ℝ).toNNReal; have hv' : 0<(w:ℝ):= by -- use natural_time
    have he : (w:ℝ)=(whenly (timeMesh Λ) 0 1:ℝ):=by unfold w; rw [show (1:ℤ)=((1:ℕ):ℤ) from rfl]; exact natural_time ..
    rw [he]; exact (show 0 < whenly (timeMesh Λ) 0 1 from when_pos _ _ _ zero_lt_one)
  let Z₁:= transversal j v hv; let Φ (i:ℂ) := Sail.sailing (fare (S) Z₁ t) (candid (S) hC Z₁ (le_of_eq (transversal_norm ..)) t (Real.toNNReal_pos.mpr hv')) i
  let Γ (x:G₀) (y:Domain Y H G true (flank j 0))(i:ℂ):= inner ℂ x (Φ i (Os y))
  -- separate weak probabilities all strip
  have χs (x:G₀) (y:Domain Y H G true A₀) : AnalyticOnNhd ℂ (Γ x y) (slit t) := fun i h=> (( (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ (G₀).space (Os y))).analyticAt _).comp (transverse_anal (S) hC Z₁ (le_of_eq (transversal_norm j hv)) t (Real.toNNReal_pos.mpr hv') i h)
  have tube (y:Domain Y H G true A₀)(i : Gt) : Φ (i:ℝ) (Os y) = Pr (eject j w+eject v i) (Os y) := by rw [across_time Y H V G j C χ v w i hv]; unfold Φ; rw [on_strip (S) hC Z₁ (le_of_eq (transversal_norm j hv)) t (Real.toNNReal_pos.mpr hv')]
  have shock (x:G₀) (hx:x∈ Aᗮ) (y:Domain Y H G true (flank j 0)) : inner ℂ x ((S).E t (Os y))=0 := by
    obtain ⟨d,he⟩:= afford_far Y H V G j v hv w hv'.le u y b
    have hp: ∀ q:Gt, (q:ℝ)∈ Ioo d (d+1) → Γ x y (q:ℝ) =0:= by
      intro q v'
      let f:= move (tent Y H) (eject j w+ eject v q) y.val
      let e:= (he q v'); let p:Domain Y H G true (flank j 0):= ⟨f,domain_mono Y H G inter_subset_left e⟩
      have hz: Pr (eject j w+ eject v q) (Os y)= Os p := (despite Y H V G j C χ (eject j w+ eject v q) (Submodule.inclusion (domain_loose Y H G _) y) (by rw [map_add,coordinates_eject,coordinates_eject]; simp [hv.symm,hv'.le]) (show f∈Domain Y H G false (flank j 0) from domain_loose Y H G _ p.property)).symm
      unfold Γ; rw [tube,hz]; exact inner_left_of_mem_orthogonal (LinearMap.mem_range.mpr ⟨(⟨f,e⟩:Domain Y H G true _),rfl⟩) hx
    have contR : Continuous (fun k:ℝ=> Γ x y k):= (χs x y).continuousOn.comp_continuous Complex.continuous_ofReal (fun x=> slit_ground _ (show 0<(t:ℝ) from Real.toNNReal_pos.mpr hv') x)
    have he:= Set.EqOn.closure (s:= Ioo d (d+1)∩ (Gt:Set ℝ)) ?_ contR (continuous_const (y:=(0:ℂ)))
    swap; · exact fun i ⟨r,v⟩=> hp ⟨i,v⟩ r
    obtain ⟨k,m,n⟩:= exists_between (show d<d+1 by linarith)
    have ht:=pioneer (slit_connected _) (slit_ground _ (show 0<(t:ℝ) from Real.toNNReal_pos.mpr hv') k) _ _ ⟨m,n⟩ (χs x y) (analyticOnNhd_const (v:=(0:ℂ))) (he.mono ((daylight s).open_subset_closure_inter isOpen_Ioo)) (show (↑(0:ℝ):ℂ)∈ slit t from slit_ground _ (show 0<(t:ℝ) from Real.toNNReal_pos.mpr hv') 0)
    change Γ x y (↑(0:ℝ))=0 at ht; unfold Γ Φ at ht; rw [on_strip (S) hC Z₁ (le_of_eq (transversal_norm j hv)) t (Real.toNNReal_pos.mpr hv'),zero_smul,OS.Semigroup.uZero] at ht; exact ht
  have hA : Aᗮ=⊥ := (Submodule.eq_bot_iff _).mpr fun x hx=> by
    have hd:= ((S).whole t).dense_image ((S).E t).continuous (compass_domain_dense Y H V G j C χ)
    apply (inner_self_eq_zero (𝕜:=ℂ)).1; refine closure_minimal ?_ (isClosed_eq (innerSL ℂ x).continuous (continuous_const (y:=(0:ℂ)))) (hd x)
    rintro _ ⟨v,⟨z,rfl⟩,rfl⟩; exact shock x hx z
  intro x; change x∈ A.topologicalClosure; rw [← Submodule.orthogonal_orthogonal_eq_closure,hA,Submodule.bot_orthogonal_eq_top]; exact Submodule.mem_top
end spectral
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
