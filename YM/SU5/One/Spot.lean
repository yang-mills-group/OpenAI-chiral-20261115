import YM.SU5.One.Overlay

/-!
# The dense positive-time test-polynomial domain of the selected functionals

Use ONE algebra, with its locality system, axes from ONE character.
Do **not** claim a common set which is simultaneously in all four wings is
dense in each. Here a common physical test-field algebra of inputs whose
future parts reconstruct the entire selected Hilbert in each choice. And a
genuine joint ingredient of the reconstruction: the continued pair of the
cell test has data IN the projected compass, with continuity in all
four (Euclidean) shifts and the same lower bound. No claim of full relativistic
covariance/locality, or even that the unprojected generally extends (though
individual time is real on the whole selected H).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Branch
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry PhaseChoice Altitude
open Selected CF.Pannier.Chancel Set

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K"=> tent Y H
variable {i k:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ} {E:ℕ→Family (tent Y H)→ℂ} (V: Universal Y H i k I E)
    (G: GroundExtension (i:=i) (k:=k) (E:=E) Y H) {L:Tapestry.Rack Λ l}{B:Tapestry.Clay Λ l}
    (D: Exhibition Y H i k I E L B)
variable (d : Axis) (S : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
local notation "𝔄" j:max=> displayAlgebra Y H V G.history G.clipped j false (S j)
variable (c : displayAlgebra Y H V G.history G.clipped d false (S d) →⋆ₐ[ℂ] ℂ)
local notation "C"=> SameCharacter.resident Y H V G d false (S d) c
local notation "Θ"=> onDrawing Y H V G D d S C
local notation "Mx"=> evaluate Y H V G d S C
local notation "r" j:max=> displacement Y H V G.history G.clipped d false (S d) c j (S j)
local notation "R" j:max t:max=> Selected.response Y H V t G.history G.clipped j false (S j) (r j)

abbrev watch (U : Set RSpace) := circum Λ l (tent Y H) true U Set.univ

theorem next {U V' : Set RSpace} (p:U⊆V') : watch Y H U ≤ watch Y H V':=wellGrows Λ K l true (handstamp U) (handstamp V') _ _ Set.Subset.rfl (Set.preimage_mono p)
lemma sky {wide : Bool}{V' : Set RSpace}{s:ℕ}: observatory Y H wide s V' ≤ watch Y H V':=
  le_trans (observing_more Y H (show s≤ s from Nat.le_refl _)) (wellGrows Λ K l true (handstamp V') _ _ _ (Set.inter_subset_left) Set.Subset.rfl)

/-- Exhaustion in physical units and bounded height. This *same domain* can
be evaluated using budget of Imprint and Tailored, with no prechosen common
support for all of it required. -/
lemma microscope {U : Set RSpace}{x:Altitude.Cloud (Dome (tent Y H))} (v:x∈ watch Y H U) :
    ∃ s : ℕ, ∃ n:ℕ,x∈ observatory Y H true s (U∩ cabin n):=by
  obtain ⟨s,h⟩:= declaredGate Λ (tent Y H) l true (handstamp U) _ v
  obtain ⟨n,t⟩:=(wellExhaustion Λ K l true (handstamp U) (Set.univ∩ Set.Iic s) x h).exists
  refine ⟨s,n,wellGrows Λ K l true (handstamp U∩ cabin n) (handstamp (U∩ cabin n)) _ _ Set.Subset.rfl ?_ t⟩
  intro i g; have he : ∀ j,|i j|≤ (n:ℝ):=g.2
  refine ⟨g.1,fun j=>?_⟩; change |i j/2|≤ (n:ℝ); rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith [he j,abs_nonneg (i j)]

variable (j:Axis)
local notation "Δ"=> engaged Y H V G j false (S j) d (S d) C
local notation "γ" s:max=> Acting.voice Y H V G j false (S j) Δ s
local notation "κ" s:max=> bud Y H V s G.history G.clipped j false (S j) (r j)
local notation "℥" => indoor Y H V G.history G.clipped j false (S j) (r j)
local notation "Y₀"=> PhaseChoice.atZero Λ
local notation "U"=> flank j 0
local notation "W"=> watch Y H U
local notation "P" s:max=> Sunlight.cloister Λ l j (PhaseChoice.atZero Λ) (tent Y H) s
local notation "Z"=> sameSpace Y H V G d S c j
local notation "F" s:max=> Tower.Field Y H s j 0 false
local notation "ε"=>declaim Y H V G j D d S C

lemma underAxis (x : W): ∃ s:ℕ,x.val∈ P s:= by
  obtain ⟨s,n,g⟩:=microscope Y H x.property
  exact ⟨s,stamped Y H j g Set.inter_subset_left⟩
private lemma sketch (x y:W) : ∃ s:ℕ,x.val∈ P s ∧ y.val∈ P s:=by
  obtain ⟨s,h⟩:= underAxis Y H j x; obtain ⟨t,g⟩:= underAxis Y H j y
  refine ⟨max s t, spacing_stamp Y H j (le_max_left ..) h,spacing_stamp Y H j (le_max_right ..) g⟩ -- tune

noncomputable def role (x : W): ℥ := Z (ε (underAxis Y H j x).choose_spec)
local notation "A"=> role Y H V G D d S c j
lemma role_at (x: W) (s: ℕ) (p : x.val∈P s) : A x= Z (ε p):=by
  unfold role; apply congrArg Z
  let v:=underAxis Y H j x; let q:= v.choose; change ε v.choose_spec= ε p
  rcases le_total q s with h|h
  · exact (declaim_all Y H V G j D d S C h v.choose_spec p).symm
  exact declaim_all Y H V G j D d S C h p v.choose_spec

lemma role_built (x:W) (s:ℕ) (p:x.val∈P s) :
    A x=(κ s) (⟨(Exhibition.vistaFinish Y H s D x.val).val,practiced Y H V j D p⟩ : F s):=by rw [role_at Y H V G D d S c j x s p, declaim,sameSpace_points]

noncomputable def denote : W→ₗ[ℂ](℥) where
  toFun := A
  map_add' x y:=by
    obtain ⟨s,a,b⟩:= sketch Y H j x y
    rw [role_at Y H V G D d S c j _ s (show (x+y: W).val∈P s from Subalgebra.add_mem (P s) a b),role_at Y H V G D d S c j x s a,role_at Y H V G D d S c j y s b,←map_add]; unfold declaim; rw [←map_add]
    apply congrArg Z; apply congrArg; apply Subtype.ext; let ee:= congrArg Subtype.val (map_add (Exhibition.vistaFinish Y H s D) x.val y.val)
    exact ee
  map_smul' a x:=by
    obtain ⟨s,v⟩:= underAxis Y H j x
    rw [role_at Y H V G D d S c j _ s (show (a • x:W).val∈P s from Subalgebra.smul_mem _ v _), role_at Y H V G D d S c j x s v]; change Z _=a • Z _; rw [←map_smul]; unfold declaim; rw [←map_smul]
    apply congrArg Z; apply congrArg; apply Subtype.ext; let ee:= congrArg Subtype.val (map_smul (Exhibition.vistaFinish Y H s D) a x.val)
    exact ee
local notation "Σ₀"=> denote Y H V G D d S c j
lemma form_cost (x y:W) : inner ℂ (Σ₀ x) (Σ₀ y)= Θ ((Y₀).oppose Λ j K x.val*y.val):= by
  obtain ⟨s,a,b⟩:=sketch Y H j x y; change inner ℂ (A x) (A y)=_
  rw [role_at Y H V G D d S c j x s a,role_at Y H V G D d S c j y s b, LinearIsometryEquiv.inner_map_map]
  exact cabin_form Y H V G j D d S C a b
lemma printed_full : DenseRange (denote Y H V G D d S c j) := by
  let P₀:= PhaseChoice.showcase Y H V G j D d S C
  refine ((Z).surjective.denseRange.dense_image (Z).continuous (showcased Y H V G j D d S C)).mono ?_
  rintro _ ⟨v,h,rfl⟩
  obtain ⟨s,a,f,hp,t,hv,e⟩:=(show v∈ P₀ from h)
  have hx : f∈W:= next Y H (Set.inter_subset_left (s:=U) (t:=cabin a)) (sky Y H (show f∈ observatory Y H true s (U∩ cabin a) from ?_)); swap; · unfold observatory; rw [Set.univ_inter]; exact t
  refine ⟨⟨f,hx⟩, (role_at Y H V G D d S c j _ s hv).trans ?_⟩
  rw [e]
lemma first_frame : Σ₀ 1 = doorstep Y H V G.history G.clipped j false (S j) (r j):= by
  change A (1:W)=_
  have h : (1:Altitude.Cloud (Dome (tent Y H)))∈ P 0:= (P 0).one_mem
  rw [role_built Y H V G D d S c j 1 0 (show (1:W).val∈P 0 from h), ← root Y H V 0 G.history G.clipped j false (S j) (r j)]
  apply congrArg (κ 0); apply Subtype.ext
  change ((Exhibition.vistaFinish Y H 0 D) 1).val=(1: Dome K).val
  have h₁: (Exhibition.vistaFinish Y H 0 D) 1=1:= by unfold Exhibition.vistaFinish; rw [Decking.crown1]
  rw [h₁]

open YM.SelectionAnalysis MeshClock
local notation "q₁"=> (saunters Y H V G.history G.clipped j false (S j) (r j)).orthogonalProjectionOnto
local notation "L₁"=> fort Y H V G.history G.clipped j false (S j) (r j)
local notation "π"=> peninsula Y H V G.history G.clipped j false (S j) (r j)

@[simp]
lemma reflect_shot (f: Marks (tent Y H) true) (s:ℕ): (Y₀).oppose Λ j K (photograph Y H s f) = photograph Y H s (mirrorInMarks Y H j true f) := by
  unfold Sunlight.oppose photograph; rw [pinhole_apply,pinhole_apply,Altitude.pluage,Altitude.plank]
  rw [show plumeTail (fun i=>aureole K j ((Y₀).marks i)) (fun _=> (1:Dome K))=fun _ :ℕ=>(1:Dome K) from funext fun i=> aureoleUnit .., atZ]; rfl

private lemma draw_future {s:ℕ}(x:F s)(f:Marks (tent Y H) true)(h:f.val=x.val): ∃ a:W, a.val=photograph Y H s f ∧ Σ₀ a = (κ s) x:= by
  obtain ⟨Xx,hf,hp⟩:= (show x.val ∈ wing K j _ from ((purpose_ok ..).1 x.property).1)
  rw [←h] at hf; rw [area0] at hp
  let u:= photograph Y H s f; have e : u∈ observatory Y H true s (flank j 0):= by
     refine wellGrows Λ K l true (handstamp (cells Λ l s Xx)) _ _ _ Set.Subset.rfl ?_ (negative_source Y H f hf)
     refine Set.preimage_mono ?_
     refine supported_iff_cells.mp ?_
     change printedHere Λ l s Xx (handstamp (flank j 0)); rw [stamp_flank]
     simpa [flank,Tapestry.markZ] using brought Λ l s j 0 Xx hp
  let a:W:=⟨u,sky Y H e⟩; refine ⟨a,rfl,?_⟩
  change A a=_; rw [role_built Y H V G D d S c j a s (stamped Y H j e Set.Subset.rfl)]
  apply congrArg; apply Subtype.ext; change (Exhibition.vistaFinish Y H s D (pinhole _ s (resolutionProbe Y H f))).val=x.val; unfold Exhibition.vistaFinish; rw [Decking.outcrop]; exact h

/-- A representation (including continued matrix elements) agrees on the
selected overlapping cell test stated. At `real offsets not exactly on the
mesh` `scene` rather than a fictitious exact identity of estimator inputs. Do
not claim the full unprojected state continues in spatial offsets. -/
lemma in_glass {s:ℕ}(p q:Cover) (w:Marks K true){δ:ℝ}{o:Cover}{u k₀:ℕ}{z:SU.Slot}{X':Finset Cover}
    (g: Lantern Y H V G D d S c s X' j p q w δ o u k₀ z) :
    let i := relocateWorld Y H true p w; let k:= relocateWorld Y H true q w
    ∃ (f f':W) (x y:Tower.Field Y H s j 0 false), f.val=photograph Y H s i ∧ f'.val=photograph Y H s k ∧
      x.val=i.val ∧ y.val=k.val ∧ Σ₀ f=(κ s) x ∧ Σ₀ f'=(κ s) y ∧
      inner ℂ (q₁ (Σ₀ f): L₁) (q₁ (Σ₀ f'))=Θ ((Y₀).oppose Λ j K f.val*f'.val) ∧
      1/32≤ ‖inner ℂ (Σ₀ f) (Σ₀ f')‖ ∧
      ∀ᶠ v: (Axis→ℝ) in 𝓝 0,
        1/33 ≤ ‖inner ℂ (q₁ (Σ₀ f):L₁) ((π).E (v j).toNNReal ((π).«U» (diameter v) (q₁ (Σ₀ f'):L₁)))‖ := by
  intro i k
  obtain ⟨x,y,h,t,hc,hn,he,hx⟩:=g.through.extendsTo
  obtain ⟨f,a,v⟩:= draw_future Y H V G D d S c j x i h.symm
  obtain ⟨f',z',m⟩:= draw_future Y H V G D d S c j y k t.symm
  let Λ₀(v'):ℂ:= scene Y H V s G.history G.clipped j false (S j) (r j) x y v'
  let f₀:L₁:= q₁ (Σ₀ f); let F₀:L₁:=q₁ (Σ₀ f')
  have ht : f₀=land Y H V s G.history G.clipped j false (S j) (r j) x:= congrArg q₁ v
  have hV : F₀=land Y H V s G.history G.clipped j false (S j) (r j) y:= congrArg q₁ m
  have hh(ω:Axis→ℝ): inner ℂ f₀ ((π).E (ω j).toNNReal ((π).«U» (diameter ω) F₀))=Λ₀ ω:=by rw [ht,hV]; exact (peninsula_window ..).symm
  refine ⟨f,f',x,y,a,z',h,t,v,m,?_, ?_,hn.mono fun v h=> ?_⟩
  · specialize hh 0; rw [Pi.zero_apply,Real.toNNReal_zero,(π).eZero,show diameter (a:=j) (0:Axis→ℝ)=0 from ?_,(π).uZero] at hh
    swap; · apply Subtype.ext; change WithLp.toLp _ (0:Axis→ℝ) - _ = _; simp
    change inner ℂ f₀ F₀=_; change inner ℂ f₀ F₀= scene _ _ _ _ _ _ _ _ _ _ _ _ _ at hh
    rw [hh,a,z',reflect_shot,←photos_multiply,photo_response Y H V G D d S c _ _ j]; exact he
  · rw [form_cost, a,z',reflect_shot]; exact (g.estimate 0).1
  have h0 : 1/33 ≤ ‖Λ₀ v‖ := h
  rw [←hh v] at h0; exact h0
end YM.CF.Buffered.Afterglow.Tower.One
