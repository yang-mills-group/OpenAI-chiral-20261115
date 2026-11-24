import YM.SU5.Selected.Balance
import YM.SU5.Selected.CheckpointTemporal
/-!
# Attending select-vacuum RP at every reckoned plane

Same sector fixed across planes starts (Tapestry `Sunlight`). The odd-ratio
subdivision doesn't turn all hinges into grid points of the *translation*
system (the latter manufactured from pair of reflections). Instead gain a
little room through actual-height `Flood` stencil refinement, then translate
slightly to the right and assess through inherited odd-root positivity. This
doesn't leave the hierarchy to prove e.g. continuous restoration.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Set Theory MeshClock
local notation "M"=>timeMesh Λ
local notation "τ" s:max v:max=>(whenly M s v /2)
local notation "Q"=>advance Y H V G.history.circuit j 0 strict C
local notation "δ" z:max => gaugeShift Λ.block z
local notation "μ" v:max=> chime K j (δ v)

lemma translate_root_nat {f g:observable (tent Y H) strict}(w:ℕ)(s:ℕ)(p:f.val=(μ (w:ℤ)) g.val) : (P s) f= (P s) g:=by
  obtain ⟨x⟩:= anyporch Y H s j strict g
  let y:= centering Y H j strict s w x.fwd
  have ht:y.val.val=relocate K j x.rise f.val:=by
    change (μ (w:ℤ)) _= _; rw [p,x.yes]; unfold relocate; rw [Tower.bumps K j _ _ g.property.1.paid.choose_spec,Tower.bumps K j _ _ g.property.1.paid.choose_spec,add_comm]
  rw [cap_moved_entry Y H V G j strict C s (x.span+w) y f (by have h:=x.pos; omega) x.rise ht,onAny Y H V s G.history G.clipped j strict C x]
  have h:= centers Y H V G j strict C s w x.fwd x.pos; unfold y; rw [h]
  change (π).comp ((((Q (τ s w)).comp (B s x.fwd x.pos)).comp (Q (τ s w))).comp ι₀) = _
  rw [ContinuousLinearMap.comp_assoc,behind',← ContinuousLinearMap.comp_assoc (π),← ContinuousLinearMap.comp_assoc (π),behind]; rfl
lemma translate_root {f g:observable (tent Y H) strict}(w:ℤ)(s:ℕ)(p:f.val=(μ w) g.val) : (P s) f=(P s) g:=by
  wlog q: 0≤w generalizing f g w
  · have hr:g.val=(μ (-w)) f.val:=by rw [p,Tower.bumps K j _ _ g.property.1.paid.choose_spec,show (δ (-w))+(δ w)=0 by unfold Heat.gaugeShift; ring,wake K j g.property.1.paid.choose_spec]
    exact (this _ hr (by omega)).symm
  apply translate_root_nat Y H V G j strict C w.toNat s
  simp only [Int.toNat_of_nonneg q]; exact p

variable (d:Axis)(R:Arena Y H G.history.circuit d 0 strict)
include C in
lemma seal_shift {f g:observable (tent Y H) strict}(w:ℤ)(s:ℕ)(p:f.val=(μ w) g.val): seal₀ Y H V G d strict R s f=seal₀ Y H V G d strict R s g:=by
  apply (bank Y H V G j strict C d R).mono_; rw [corner,corner]; exact translate_root Y H V G j strict C w s p
section charged
variable (T:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
local notation "R₀"=> catalog Y H V G d false (T d)
local notation "St"=> bank Y H V G j false (T j) d (T d)
local notation "L"=> Λ.R.L.val
variable (x:Resident (catalog Y H V G d false (T d)))
local notation "X" => engaged Y H V G j false (T j) d (T d) x
local notation "Kx"=> evaluate Y H V G d T x
local notation "Aχ" => X.space
local notation "Fₓ" i:max=> Tower.Field Y H i j 0 false
local notation "γ" s:max=> Acting.voice Y H V G j false (T j) X s
local notation "W"=> Acting.clock Y H V G j false (T j) X
local notation "R₂" i:max=> wing K j (δ i)

lemma elect_slide {F:Family K}(p:TestFamily K true F)(w:ℤ)(s:ℕ): Kx s ((μ w) F)=Kx s F:=by
  have he:=aux_test (flow_port K j (δ w) p.paid.choose_spec)
  unfold evaluate; rw [dif_pos he,dif_pos p]; apply congrArg (fun a:R₀=>eye x a) -- order
  exact seal_shift Y H V G j false (T j) d (T d) w s (f:=observe he) (g:= observe p) rfl
lemma elect_mirror {F:Family K}(p:TestFamily K true F)(w:ℤ)(s:ℕ): Kx s (mirror K j (δ w) F)=star (Kx s F):=by
  rw [slidesPlane j p.paid.choose_spec (δ w),elect_slide Y H V G j d T x (reflect_ok K j 0 p) w s]
  unfold evaluate; rw [dif_pos (reflect_ok K j 0 p),dif_pos p]
  exact at_mirror Y H V G false d (T d) x s (T j) (observe p)
lemma elect_refine {F:Family K} (p:TestFamily K true F)(s q:ℕ):Kx (s+q) (stream Y H G.refine s q F)= Kx s F:=by
  unfold evaluate; rw [dif_pos (streams_test Y H G.history.circuit s q p),dif_pos p]; exact at_refine Y H V G false d (T d) x s (observe p) q
lemma voice_at {s:ℕ}(f g:Fₓ s):Kx s (mirror K j 0 f.val*g.val)= inner ℂ ((γ s) f) ((γ s) g):=by
  unfold evaluate; let z:= (reflect_ok K j 0 (field_test Y H s j 0 false f)).mul (field_test Y H s j 0 false g); rw [dif_pos z]; exact (engaged_form Y H V G j false (T j) d (T d) x s f g (observe z) rfl).symm

lemma future_climb {S:Finset Cover}(w:ℤ)(p: Tower.region j (δ w) (K).ℓ S) (r:ℕ) : Tower.region j (δ ((L:ℤ)^r*w)) ((K).ℓ+r) (volumeAround Λ l r S):=by
  induction r with
  | zero =>simpa [volumeAround] using p
  | succ r ih=>
    rw [volumeAround,←Nat.add_assoc _ r,show (δ ((L:ℤ)^(r+1)*w))=L*(δ ((L:ℤ)^r*w)) by unfold Heat.gaugeShift; rw [pow_succ']; ring]
    exact strict_one Y H j ih

local notation "σ" s:max v:max=> Acting.clock Y H V G j false (T j) X (τ s v)
private lemma into_wing (w:ℤ)(z:ℕ)(e:(δ w)= -(δ (z:ℤ))) (s:ℕ)(f:Family K)(p:f∈wing K j 0):
   0 ≤ Kx s (mirror K j (δ w) f * f):=by
  let X₀ : Fₓ s:= ⟨f,(purpose_ok ..).2 ⟨(by rw [area0]; exact p),by simp⟩⟩
  let y:= tick Y H s j 0 false z X₀
  have hf:TestFamily K true f:=field_test Y H s j 0 false X₀
  have h : mirror K j (δ w) f=mirror K j 0 y.val:=by
    rw [slidesPlane j hf.paid.choose_spec (δ w),chime_diag K j (δ w) 0 hf.paid.choose_spec,e,neg_neg]; rfl
  rw [h]; change 0 ≤ Kx s (mirror K j 0 y.val*X₀.val)
  rw [voice_at]; unfold y; rw [Acting.half_voice]
  exact (Acting.on_even_positive Y H V G j false (T j) X _).inner_nonneg_left _

/-- Full OS positivity at the aligned planes in the selected hierarchy. -/
lemma elect_plane {w:ℤ}{S:Finset Cover}{F:Family K} (h:InTest K true S false F) (p: Tower.region j (δ w) (K).ℓ S) (s:ℕ) : 0 ≤ Kx s (mirror K j (δ w) F * F):=by
  let n:=8*Λ.block.val; let u:=(L:ℤ)^n*w; let r:=u /2 + 1; let v:=2*r-u
  have h₁:1≤v:=by unfold v r; omega
  have h₂:v≤2:=by unfold v r; omega
  let D:=G.history.circuit; let S':=volumeAround Λ l n S
  let f:=stream Y H G.refine s n F
  have hx:InTest K true S' false f := (proceeds Y H D s n h).1
  have ht:(δ u)=(L:ℤ)^n*δ w:=by unfold u Heat.gaugeShift; ring
  let J₀:=gaugeShift Λ.block 1
  have hh:0<J₀:=by unfold J₀ Heat.gaugeShift; positivity
  have he: -(δ (v.toNat:ℤ))=δ (-v):=by rw [Int.toNat_of_nonneg (by omega)]; unfold Heat.gaugeShift; ring
  have ha: (δ u) + 2*(δ (-r))=(δ (-v)):=by unfold v Heat.gaugeShift; ring
  have hp: Tower.region j 0 (K).ℓ (address j (δ (-r)) S'):=by
    intro i b; obtain ⟨t,a,rfl⟩:= mem_image.mp b
    have z:= future_climb Y H j w p n t a
    rw [moves,if_pos rfl]; change (δ u)+↑((K).ℓ+n)≤ _ at z; push_cast at z
    have he: (n:ℤ)=2*J₀:=by unfold n J₀ gaugeShift; push_cast; ring
    have ht:(δ (-v))= -v * J₀:=by unfold J₀ Heat.gaugeShift; ring
    nlinarith only [z,ha,he,ht,h₁,h₂,hh]
  let v' := ((reflect_ok K j (δ w) (aux_test h)).mul (aux_test h))
  rw [← elect_refine Y H V G d T x v' s n, woven_product Y H D s n (axial K j _ h) h (mirror_detached Λ l (a:=j) (z:=δ w) p p),stream_flipped Y H D s n j (δ w) (aux_test h),←ht,
    ← elect_slide Y H V G j d T x ((reflect_ok K j (δ u) (aux_test hx)).mul (aux_test hx)) (-r) (s+n),chime_product,chimePlane j (δ u) (δ (-r)) hx,ha]
  exact into_wing Y H V G j d T x (-v) v.toNat he.symm (s+n) _ (show (μ (-r)) f∈wing K j 0 from ⟨_,flow_port K j _ hx,hp⟩)
end charged
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.elect_plane
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.elect_mirror
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.translate_root
