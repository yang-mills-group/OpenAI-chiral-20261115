import YM.SU5.Reconstruction.PolarArchives.Lease
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
local notation "K₀"=>displayAlgebra Y H V G.history G.clipped P.a false (C P.a)
local notation "Ωχ"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped P.a false (C P.a)
local notation "Rs"=> reduceToDisplay Y H V G.history G.clipped P.a false (C P.a)
open Chambers Brazier
local notation "V₀"=> Nₐ
local notation "Rt" t:max=> Pub Y H P.a t
variable (m:MeshClock.marks (timeMesh Λ))(p:0< m)
local notation "xq" q:max=>Domain Y H G q (carton P (m:ℝ))
local notation "Cm"=> strip P.a (-(m:ℝ)) (m:ℝ)
section
private lemma issue (d:marks (timeMesh Λ)){f:Sky (tent Y H)}(h:f∈ Domain Y H G false (strip P.a 0 (d:ℝ)))(p:0<d): ∃ B:Kw, (∀ u:f∈µ, Rs B=Pc ⟨f,u⟩)∧ ∀ x:V₀,∃ y:V₀,y.val=f* (Rt d) x.val∧ pay y=B.val (pay x):=by
 obtain ⟨s,⟨f,kf,rfl⟩,w,t,e⟩ := (((domain_eventually Y H G).1 h).and (notch_nat_event d p)).exists
 let d':= lantern Λ s w
 have he : (d:ℝ)=(whenly (timeMesh Λ) s w:ℝ) := by rw [←e]; exact natural_time ..
 rw [he] at kf; let x:= startOp Y H P.a s w f kf
 refine ⟨entrance Y H V s G.history G.clipped P.a false (C P.a) x t, fun u=>?_,fun z=>?_⟩
 · rw [atStamp]; exact Subtype.ext (compress_entry Y H V s G.history G.clipped P.a false (C P.a) x t)
 rw [←e]; exact Brazier.rootGraph Y H V G P.a (C P.a) s w x t z

private lemma pub_cost (d e:Gt)(f:Sky (tent Y H)) : (Rt d) ((Rt e) f)= (Rt (d+e)) f := pub_sum Y H P.a d e f
@[simp] private lemma pub_zero (f:Sky (tent Y H)): (Rt 0) f=f:= by unfold Pub; rw [eject_zero,move_by_zero]
structure DotPrice (w:µ)(B:Kw):Prop where
 views : Rs B= Pc w
 has (q r: Bool)(x:xq q)(z:xq r): τ x.val * w.val * z.val∈ Domain Y H G false Set.univ
 knows(q r: Bool)(x:xq q)(z:xq r)(u:τ x.val*w.val*z.val∈µ):
    Ωχ ⟨τ x.val * w.val * z.val,u⟩= inner ℂ (rotated_c Y H V G C P m q x) (B.val (carrier Y H V G C P m r z))
include p in
lemma atDot (w: Domain Y H G false Set.univ) (h:w.val∈ Domain Y H G false (strip P.a (-(m:ℝ)) (m:ℝ))): ∃ B:driveAlgebra Y H V G.history G.clipped P.a false (C P.a), DotPrice Y H V G C P m w B:=by
 let d:Gt:=m+m; let F:=(Rt m) w.val
 have hx:F∈ D false (strip P.a 0 (d:ℝ)):= by
    apply domain_mono Y H G _ (moving Y H V G _ _ h)
    rintro _ ⟨z,t,rfl⟩; unfold d; replace t:(-(m:ℝ)≤ z P.a ∧ z P.a ≤ (m:ℝ)):=t; rw [AddSubgroup.coe_add,coordinates_eject]; change 0≤ z P.a + eject _ (m:ℝ) _ ∧ z P.a+eject _ (m:ℝ) _≤_
    rw [eject_at]; constructor<;>linarith [t.1,t.2]
 obtain ⟨B,B0,HB⟩:= issue Y H V G C P d hx (add_pos p p); refine ⟨B,(B0 (domain_le_lawDomain Y H G _ hx)).trans (moving_chime Y H V G C P.a _ w.property _),?_,?_⟩
 all_goals intro q r x z
 all_goals
    let f:V₀:= ⟨_,direct Y H V G P m z.property⟩; let g:V₀:= ⟨_,unshelter Y H V G P m (relax Y H G (loadsQ Y H V G P m x.property))⟩
    obtain ⟨y,hy,ht⟩:= HB f
    have hword : move K (eject P.a m) (τ x.val*w.val*z.val)= flipMark P.a K g.val * y.val:=by
       have h₁ :(Rt d) f.val= (Rt m) z.val:=by change (Rt d) ((Rt (-m)) z.val)=_; rw [pub_cost,show d+ -m=m from (by unfold d; abel)]
       have h₂ : flipMark P.a K g.val= (Rt m) (τ x.val):=by
          change flipMark P.a K ((Rt (-m)) (flipMark P.a K (τ x.val)))=_; rw [pub_negflip,mirror_twice,neg_neg]
       rw [hy, h₁,h₂,move_prod,move_prod,mul_assoc]
    have hv := paired_forever Y H G P.a _ _ g.property y.property
 · apply domain_mono Y H G (subset_univ (slides (coordinates Λ (eject P.a (-m))) Set.univ))
   suffices q: move K (eject P.a (-m)) (move K (eject P.a m) (τ x.val*w.val*z.val)) ∈ D false (slides (coordinates Λ (eject P.a (-m))) Set.univ) by
       change (Rt (-m)) ((Rt m) _)∈_ at q; rwa [pub_cost,neg_add_cancel,pub_zero] at q
   exact moving Y H V G _ _ (hword.symm ▸ hv)
 intro u; rw [←root_shift Y H V G P.a (C P.a) (eject P.a m) u (hword.symm ▸ hv)]; change _=inner ℂ (pay g) (B.val (pay f)); rw [←ht]
 -- ←ht after carrier rewrite tune
 exact (congrArg Ωχ (Subtype.ext hword)).trans (LightBudget.initial_pair Y H V G P.a (C P.a) g y).symm
end
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
