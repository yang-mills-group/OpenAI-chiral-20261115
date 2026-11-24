import YM.SU5.Reconstruction.Seams.Far
/-! # Reeh for slitted j precursors. Extends Seams/Far proof with extra masks, one at a time. -/
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
-- tighten ANY number of the perpendicular lanes at once
abbrev mask (s:Finset Axis)(x:ℝ)(b:Bool): Set RSpace:= {i| ∀ z∈s, i∈sideLand z x b}
abbrev venueR (x:ℝ)(b:Bool)(s:Finset Axis):= flank j 0∩mask s x b
lemma purposed (x:ℝ)(b:Bool)(s:Finset Axis) : mask (insert j s) x b= sideLand j x b ∩ mask s x b:=by ext; simp_all [mask]
lemma more_lane (x:ℝ)(b:Bool)(s:Finset Axis) : venueR j x b (insert v s)= venueR j x b s∩sideLand v x b:=by rw [venueR,purposed]; unfold venueR; rw [inter_comm (sideLand v x b) (mask s x b), inter_assoc]
noncomputable def padFar (x:ℝ)(b:Bool)(s:Finset Axis) : Submodule ℂ (fort Y H V G.history G.clipped j false C χ):=LinearMap.range ((compassKet Y H V G j C χ).comp (Submodule.inclusion (domain_mono Y H G (show venueR j x b s ⊆ flank j 0 from inter_subset_left))))
local notation "Os"=> compassKet Y H V G j C χ
local notation "φ" p:max=> eject j p
local notation "μ" x:max=> move K x
include V hv
lemma prepare_padFar (t:Gt) (p : 0≤ (t:ℝ)) (u:ℝ) (b:Bool)(L' : Finset Axis)(u0:j ∉ L')(h0:v ∉ L')(f: Domain Y H G true (venueR j u b L')) :
    ∃ a:ℝ,∀ i:Gt, ((i:ℝ)∈ Ioo a (a+1)) → move K (eject j t+ eject v i) f.val∈ Domain Y H G true (venueR j u b (insert v L')) := by
  -- just Ioo. simplify output
  obtain ⟨W,c,z,e⟩:= (compact_domain Y H G).1 f.property
  obtain ⟨a,w,k,p'⟩:= Schedule.shutters (daylight (timeMesh Λ)) v c
  let g (i:Gt) := eject j t+ eject v i
  have ht (i:Gt): slides (coordinates Λ (g i)) W ⊆ venueR j u b L' := by
    apply subset_inter; · apply subset_trans (image_mono (Subset.trans z (show venueR j u b L'⊆ _ from inter_subset_left))) (even_flank j _ ?_); simp [g,hv.symm,p]
    rintro _ ⟨x,h,rfl⟩ i' l1
    have he:(x+coordinates Λ (g i)) i' = x i':= by
       unfold g; rw [map_add,coordinates_eject,coordinates_eject]; simp [ (show i'≠v from fun q=> h0 (q ▸ l1)),show i'≠j from fun q=> u0 (q ▸ l1)]
    have hz:= (z h).2 i' l1
    cases b
    · change (x+coordinates Λ (g i)) i'≤u; rw [he]; exact hz
    change u≤(x+coordinates Λ (g i)) i'; rw [he]; exact hz
  rw [more_lane j v]; cases b
  · refine ⟨u-1-w, fun i r=>?_⟩; apply domain_mono Y H G (subset_inter (ht i) _) (moving Y H V G _ _ e)
    rintro _ ⟨x,z,rfl⟩; change x v + coordinates Λ _ _ ≤ u
    simp only [g,map_add,Pi.add_apply,coordinates_eject,eject_at,eject_away j _ v hv,zero_add]; linarith [(p' x z).2, (show (i:ℝ) ∈ Ioo _ _ from r).2]
  refine ⟨u-a,fun i r=>?_⟩; apply domain_mono Y H G (subset_inter (ht i) _) (moving Y H V G _ _ e)
  rintro _ ⟨x,z,rfl⟩; change u≤x v+coordinates Λ _ _
  simp only [g,map_add,Pi.add_apply,coordinates_eject,eject_at,eject_away j _ v hv,zero_add]; linarith [(p' x z).1, (show (i:ℝ)∈ Ioo _ _ from r).1]

section spectral
variable (tC : saunters Y H V G.history G.clipped j false C χ=⊤) (hC: ConePrice.Forward (peninsula Y H V G.history G.clipped j false C χ))
include tC hC hv
lemma lands_denseStep (u:ℝ)(b:Bool)(Z : Finset Axis)(pχ:j∉Z)(tv:v∉Z)(h:Dense (padFar Y H V G j C χ u b Z : Set G₀)) : Dense (padFar Y H V G j C χ u b (insert v Z) : Set (fort Y H V G.history G.clipped j false C χ)) := by
  let A:= padFar Y H V G j C χ u b (insert v Z); let s:=timeMesh Λ; let w:Gt:= notch (timeMesh Λ) 0 1
  let t:= (w:ℝ).toNNReal; have hv' : 0<(w:ℝ):= by -- use natural_time
    have he : (w:ℝ)=(whenly (timeMesh Λ) 0 1:ℝ):=by unfold w; rw [show (1:ℤ)=((1:ℕ):ℤ) from rfl]; exact natural_time ..
    rw [he]; exact (show 0 < whenly (timeMesh Λ) 0 1 from when_pos _ _ _ zero_lt_one)
  let Z₁:= transversal j v hv; let Φ (i:ℂ) := Sail.sailing (fare (S) Z₁ t) (candid (S) hC Z₁ (le_of_eq (transversal_norm ..)) t (Real.toNNReal_pos.mpr hv')) i
  let Γ (x:G₀) (y:Domain Y H G true (flank j 0))(i:ℂ):= inner ℂ x (Φ i (Os y))
  -- separate weak probabilities all strip
  have χs (x:G₀) (y:Domain Y H G true A₀) : AnalyticOnNhd ℂ (Γ x y) (slit t) := fun i h=> (( (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ (G₀).space (Os y))).analyticAt _).comp (transverse_anal (S) hC Z₁ (le_of_eq (transversal_norm j hv)) t (Real.toNNReal_pos.mpr hv') i h)
  have tube (y:Domain Y H G true A₀)(i : Gt) : Φ (i:ℝ) (Os y) = Pr (eject j w+eject v i) (Os y) := by rw [across_time Y H V G j C χ v w i hv]; unfold Φ; rw [on_strip (S) hC Z₁ (le_of_eq (transversal_norm j hv)) t (Real.toNNReal_pos.mpr hv')]
  have shock (x:G₀) (hx:x∈ Aᗮ) (y:Domain Y H G true (venueR j u b Z)) : inner ℂ x ((S).E t (Os ⟨y.val,domain_mono Y H G (show venueR j u b Z ⊆ _ from inter_subset_left) y.property⟩))=0 := by
    let f₀ : Domain Y H G true (flank j 0) := ⟨y.val,domain_mono Y H G inter_subset_left y.property⟩
    obtain ⟨d,he⟩:= prepare_padFar Y H V G j v hv w hv'.le u b Z pχ tv y
    have hp: ∀ q:Gt, (q:ℝ)∈ Ioo d (d+1) → Γ x f₀ (q:ℝ) =0:= by
      intro q v'
      let F₁:= move (tent Y H) (eject j w+ eject v q) y.val
      let e:= (he q v'); let p:Domain Y H G true (flank j 0):= ⟨F₁,domain_mono Y H G inter_subset_left e⟩
      have hz: Pr (eject j w+ eject v q) (Os f₀)= Os p := (voice_move Y H V G j C χ tC (eject j w+ eject v q) (Submodule.inclusion (domain_loose Y H G _) f₀) (by rw [map_add,coordinates_eject,coordinates_eject]; simp [hv.symm,hv'.le]) (show F₁∈Domain Y H G false (flank j 0) from domain_loose Y H G _ p.property)).symm
      unfold Γ; rw [tube,hz]; exact inner_left_of_mem_orthogonal (LinearMap.mem_range.mpr ⟨(⟨F₁,e⟩:Domain Y H G true _),rfl⟩) hx
    have contR : Continuous (fun k:ℝ=> Γ x f₀ k):= (χs x f₀).continuousOn.comp_continuous Complex.continuous_ofReal (fun x=> slit_ground _ (show 0<(t:ℝ) from Real.toNNReal_pos.mpr hv') x)
    have he:= Set.EqOn.closure (s:= Ioo d (d+1)∩ (Gt:Set ℝ)) ?_ contR (continuous_const (y:=(0:ℂ)))
    swap; · exact fun i ⟨r,v⟩=> hp ⟨i,v⟩ r
    obtain ⟨k,m,n⟩:= exists_between (show d<d+1 by linarith)
    have ht:=pioneer (slit_connected _) (slit_ground _ (show 0<(t:ℝ) from Real.toNNReal_pos.mpr hv') k) _ _ ⟨m,n⟩ (χs x f₀) (analyticOnNhd_const (v:=(0:ℂ))) (he.mono ((daylight s).open_subset_closure_inter isOpen_Ioo)) (show (↑(0:ℝ):ℂ)∈ slit t from slit_ground _ (show 0<(t:ℝ) from Real.toNNReal_pos.mpr hv') 0)
    change Γ x f₀ (↑(0:ℝ))=0 at ht; unfold Γ Φ at ht; rw [on_strip (S) hC Z₁ (le_of_eq (transversal_norm j hv)) t (Real.toNNReal_pos.mpr hv'),zero_smul,OS.Semigroup.uZero] at ht; exact ht
  have hA : Aᗮ=⊥ := (Submodule.eq_bot_iff _).mpr fun x hx=> by
    have hd:= ((S).whole t).dense_image ((S).E t).continuous h
    apply (inner_self_eq_zero (𝕜:=ℂ)).1; refine closure_minimal ?_ (isClosed_eq (innerSL ℂ x).continuous (continuous_const (y:=(0:ℂ)))) (hd x)
    rintro _ ⟨v,w,rfl⟩; obtain ⟨z,rfl⟩:= LinearMap.mem_range.mp w; exact shock x hx z
  intro x; change x∈ A.topologicalClosure; rw [← Submodule.orthogonal_orthogonal_eq_closure,hA,Submodule.bot_orthogonal_eq_top]; exact Submodule.mem_top

omit hv
lemma lands_dense (u:ℝ)(b:Bool)(Z : Finset Axis)(p:j∉Z) : Dense (padFar Y H V G j C χ u b Z:Set G₀):= by
 induction Z using Finset.induction_on with
 | empty =>
   apply Dense.mono _ (compass_domain_dense Y H V G j C χ); rintro v ⟨x,rfl⟩; let h:= x.property; have hz:venueR j u b ∅=flank j 0:=by ext; simp [venueR,mask]
   exact LinearMap.mem_range.mpr ⟨⟨x.val, hz.symm ▸ x.property⟩,rfl⟩
 | @insert i s e ih =>
   apply lands_denseStep Y H V G j C χ i (fun q=>p (q ▸ Finset.mem_insert_self ..)) tC hC u b s (fun x=>p (Finset.mem_insert_of_mem x)) e (ih (fun x=>p (Finset.mem_insert_of_mem x)))
end spectral
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
