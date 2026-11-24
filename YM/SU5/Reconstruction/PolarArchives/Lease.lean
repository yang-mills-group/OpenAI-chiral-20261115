import YM.SU5.Reconstruction.PolarArchives.Census
import YM.SU5.Reconstruction.Brazier.Steps
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "Mirror" i:max=> flipMark i (tent Y H)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "au"=>move K
variable (P:Ramp)
local notation "H₀"=> Ark.Ht Y H G.history.circuit P.a 0 false (C P.a)
local notation "A"=>Aurora Y H V G.history P.a false (C P.a)
local notation "Pc"=>album Y H V G C P.a
local notation "pay"=> LightBudget.prepaid Y H V G P.a (C P.a)
local notation "vc"=>seat0 Y H V G.history P.a false (C P.a)
local notation "px"=> (A).orthogonalProjectionOnto
local notation "Nₐ"=> Domain Y H G false (flank P.a 0)
local notation "τ" => gust P (tent Y H)
open Chambers
local notation "μₜ" t:max=>move (tent Y H) (eject P.a t)
variable {q:Bool}{U:Set RSpace}
noncomputable def rotateQ (P:Ramp) (J:Calibration): Sky J→ₗ[ℂ] Sky J:= (flipMark P.a J).comp (gust P J)
local notation "Re"=> rotateQ P K
include V in
lemma panels {x:Sky (tent Y H)}(p:x∈Domain Y H G q U): rotateQ P (tent Y H) x ∈ Domain Y H G q (mirrorE P.a 0 '' (P.s.act '' U)) :=
 mirror_support Y H G P.a _ (shelters Y H V G P p)
lemma comp_square (x:Sky (tent Y H)): rotateQ P K (rotateQ P K x)= flipMark P.a K (flipMark P.b K x):=by
 change flipMark P.a K (τ (flipMark P.a K (τ x)))=_
 rw [gust_mirror, show P.s.perm P.a=P.b from Equiv.swap_apply_left ..,gust_square]
lemma comp_amount {x:Sky (tent Y H)}(h:x∈µ)(p:Re (Re x)∈µ): Pc ⟨Re (Re x),p⟩=Pc ⟨x,h⟩:=by
 let v:= flipMark P.b K x; have hx:v∈µ:=domain_mono Y H G (subset_univ _) (mirror_support Y H G P.b x h); rw [show (⟨Re (Re x),p⟩:µ)=⟨_,domain_mono Y H G (subset_univ _) (mirror_support Y H G P.a v hx)⟩ from Subtype.ext (comp_square Y H P x), mirror_tone Y H V G C P.a _ hx]
 rw [show Pc ⟨v,hx⟩=_ from mirror_tone Y H V G C P.a P.b h hx,star_star]

noncomputable def embarking (P:Ramp)(p:placement Λ): placement Λ:= reverseOne P.a (P.s.act p)
@[simp] lemma embark_a (p:placement Λ): embarking P p P.a=p P.b:=by unfold embarking reverseOne; rw [if_pos rfl,P.move_a,neg_neg]
@[simp] lemma embark_b(p:placement Λ): embarking P p P.b= -p P.a:=by unfold embarking reverseOne; rw [if_neg P.cross,P.move_b]
lemma embark_c (p:placement Λ)(u:j≠P.a)(v:j≠P.b): embarking P p j=p j:=by unfold embarking reverseOne; rw [if_neg u,P.move_h _ u v]
lemma rotate_moves(p:placement Λ)(x:Sky (tent Y H)): rotateQ P K (au p x)=au (embarking P p) (rotateQ P K x):=by
 change flipMark P.a K (τ (au p x))= _; rw [zone_gust,flipped_moves]; rfl

section
variable (m:marks (timeMesh Λ))
def carton (P:Ramp)(r:ℝ):Set RSpace := flank P.a r ∩ flank P.b r
local notation "C₀"=> carton P (m:ℝ)
local notation "bx" q:max=>Domain Y H G q (carton P (m:ℝ))
include V in
lemma loadsQ {x:Sky (tent Y H)}(h:x∈ Domain Y H G q (carton P (m:ℝ))): rotateQ P K x∈ Domain Y H G q (flank P.a (m:ℝ)):=by
 apply domain_mono Y H G _ (panels Y H V G P h)
 rintro _ ⟨u,⟨z,x,rfl⟩,rfl⟩; change (m:ℝ) ≤ mirrorE P.a 0 _ P.a; simpa [mirrorE, P.move_a] using (show (m:ℝ)≤z P.b from x.2)
include V in
lemma unshelter {x:Sky (tent Y H)}(h:x∈ Domain Y H G false (flank P.a (m:ℝ))): move K (eject P.a (-m)) x∈ Domain Y H G false (flank P.a 0):= by
 simpa only [AddSubgroup.coe_neg,add_neg_cancel] using (Brazier.pub_area Y H V G P.a (t:= -m) x h)
lemma relax {u:Set RSpace}{x:Sky (tent Y H)}(h:x∈Domain Y H G q u):x∈D false u:=by cases q with | false=>exact h|true=>exact domain_loose Y H G u h
include V in
lemma direct {x:Sky (tent Y H)}(h:x∈ Domain Y H G q (carton P (m:ℝ))): move K (eject P.a (-m)) x∈ Domain Y H G false (flank P.a 0):=
 unshelter Y H V G P m (domain_mono Y H G inter_subset_left (relax Y H G h))
variable (q₀:Bool)
/-- registers BOTH lifts on the desired positive pane. -/
noncomputable def carrier : (bx q₀) →ₗ[ℂ] H₀:= (pay).comp (((move K (eject P.a (-m))).comp (bx q₀).subtype).codRestrict (Nₐ) (fun z=> direct Y H V G P m z.property)) -- notation comp tune
noncomputable def rotated_c : (bx q₀) →ₗ[ℂ] H₀:= (pay).comp (((move K (eject P.a (-m))).comp ((Re).comp (bx q₀).subtype)).codRestrict (Nₐ) (fun z=> unshelter Y H V G P m (relax Y H G (loadsQ Y H V G P m z.property))))
include V in
lemma march {t:placement Λ}(u:0≤t P.a)(v:0≤t P.b){x:Sky (tent Y H)}(h:x∈Domain Y H G q C₀):move K t x∈Domain Y H G q C₀:=by
 apply domain_mono Y H G _ (moving Y H V G t x h)
 rintro _ ⟨p,z,rfl⟩; exact ⟨le_trans z.1 (le_add_of_nonneg_right (show 0≤ (t P.a).val from u)), le_trans z.2 (le_add_of_nonneg_right (show 0≤(t P.b).val from v))⟩ -- ejections
include V in
lemma marched {x:Sky (tent Y H)}(p:x∈ Domain Y H G q univ):∃ z:placement Λ,move K z x∈ Domain Y H G q C₀:=by
 obtain ⟨u,c,_,h⟩:=(compact_domain ..).1 p; obtain ⟨a0,h₁⟩:=(c.image (continuous_apply P.a)).bddBelow; obtain ⟨B,h₂⟩:=(c.image (continuous_apply P.b)).bddBelow -- a0 shadows notation
 obtain ⟨r,hv⟩:= anywhere Λ ((m:ℝ)-min a0 B)
 refine ⟨fun _=>r,domain_mono Y H G ?_ (moving Y H V G _ _ h)⟩; rintro _ ⟨y,t,rfl⟩; have ha:a0≤y P.a:=h₁ ⟨y,t,rfl⟩; have hb:B≤y P.b:=h₂ ⟨y,t,rfl⟩
 refine ⟨?_,?_⟩
 · change (m:ℝ) ≤ y P.a+r.val; linarith [min_le_left a0 B]
 change (m:ℝ) ≤ y P.b+r.val; linarith [min_le_right a0 B]

end
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
