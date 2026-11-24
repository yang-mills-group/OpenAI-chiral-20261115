import YM.SU5.Reconstruction.PolarArchives.Tractor
import YM.SU5.Reconstruction.PolarArchives.FloorCharge
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
local notation "R"=> LightBudget.ruler Y H V G P.a (C P.a)
local notation "Zr" i:max=> R (embarking P i)
variable (m:MeshClock.marks (timeMesh Λ))(q₀:Bool)
local notation "Xq"=> Domain Y H G q₀ (carton P (m:ℝ))
local notation "XL" =>carrier Y H V G C P m q₀
local notation "XR"=>rotated_c Y H V G C P m q₀
local notation "RX"=>rotateQ P (tent Y H)
open MotorPool
private lemma tractor_pay (p:Sky (tent Y H))(t:placement Λ)(x: (μₜ (-m)) p∈ Nₐ)(v:0≤ t P.a)(u: (μₜ (-m)) (au t p)∈ Nₐ):
  R t (pay ⟨(μₜ (-m)) p,x⟩)= pay ⟨(μₜ (-m)) (au t p),u⟩:=by
 have hx: (μₜ (-m)) (au t p) = au t ((μₜ (-m)) p) := by rw [move_sum,move_sum,add_comm];
 rw [LightBudget.initial_moves Y H V G P.a (C P.a) _ x t v (hx ▸ u)]
 exact congrArg pay (Subtype.ext hx.symm)
local notation "π"=> (A).starProjection
set_option maxHeartbeats 760000 in
lemma flight: Driver (H:=Ark.Ht Y H G.history.circuit P.a 0 false (C P.a)) XL XR ((A).starProjection) (fun v:Tractor Λ P=> R v.val) (fun v:Tractor Λ P=>Zr v.val) := by
 constructor
 · intro v p
   let x: Xq:= ⟨au v.val p.val,march Y H V G P m v.2.1 v.2.2 p.property⟩; have hv:0≤embarking P v.val P.a:= by rw [embark_a]; exact v.2.2
   refine ⟨x,tractor_pay Y H V G C P m p.val _ _ v.2.1 _,?_⟩
   let h:= unshelter Y H V G P m (relax Y H G (loadsQ Y H V G P m p.property)); let ht:= unshelter Y H V G P m (relax Y H G (loadsQ Y H V G P m x.property)); let x0:= embarking P v.val; have he: RX x.val= au x0 (RX p.val):= rotate_moves Y H P v.val p.val
   change (Zr v.val) (pay ⟨(μₜ (-m)) (RX p.val),h⟩)= pay ⟨(μₜ (-m)) (RX x.val), ht⟩
   have k : move K (eject P.a (-m)) (au x0 (RX p.val))∈Domain Y H G false (flank P.a 0):= by rw [← he]; exact ht
   exact (tractor_pay Y H V G C P m (RX p.val) (embarking P v.val) h hv k).trans (congrArg pay (Subtype.ext (congrArg (μₜ (-m)) he.symm)))
 exact fun i x=> ⟨(tractor_chip Y H V G C P _ _).2,(tractor_chip Y H V G C P _ _).2⟩ -- tune parser bullets
 intro i x; exact ⟨congrArg Subtype.val (tractor_chip Y H V G C P i.val x).1,congrArg Subtype.val (tractor_chip Y H V G C P (embarking P i.val) x).1⟩
 intro p u; exact Submodule.starProjection_eq_self_iff.mpr (tractor_first Y H V G C P p u)
 intro p u; exact Submodule.starProjection_eq_self_iff.mpr (tractor_second Y H V G C P p u)
lemma costsP(p:Xq)(h:p.val∈Domain Y H G false univ)(v:RX p.val∈Domain Y H G false univ) :
    π (XL p) = ((Pc ⟨p.val,h⟩).val vc).val ∧ π (XR p) = ((Pc ⟨RX p.val,v⟩).val vc).val:= by
 have Hc (x:Sky (tent Y H))(p0:x∈µ)(q:(μₜ (-m)) x∈ Nₐ): px (pay ⟨(μₜ (-m)) x,q⟩)=(Pc ⟨x,p0⟩).val vc:=by rw [at_origin _ _ _ _ C P.a q (domain_le_lawDomain Y H G _ q),moving_chime Y H V G C P.a _ p0]
 exact ⟨congrArg Subtype.val (Hc p.val h _),congrArg Subtype.val (Hc (RX p.val) v _)⟩ -- goals placeholders tune
structure Gatemark (p: Domain Y H G false univ)(u: ℕ→ (Domain Y H G q₀ (carton P (m:ℝ)))): Prop where
 left : Tendsto (fun i=> XL (u i)) atTop (𝓝 (((Pc p).val vc).val:H₀))
 right(h:RX p.val∈ Domain Y H G false univ): Tendsto (fun i=> XR (u i)) atTop (𝓝 ((((Pc ⟨RX p.val,h⟩).val vc):↥(Aurora Y H V G.history P.a false (C P.a))).val:H₀))
lemma fullMark (p: Domain Y H G false univ)(z:p.val∈ Domain Y H G q₀ univ): ∃ u,Gatemark Y H V G C P m q₀ p u:=by
 obtain ⟨t,h⟩:= marched Y H V G P m z; let x: Xq:=⟨_,h⟩
 have q:= domain_le_lawDomain Y H G univ z -- tune p capture
 have Q:x.val∈ Domain Y H G false univ:=domain_le_lawDomain _ _ _ _ x.property; have e: RX x.val∈ Domain Y H G false univ:= domain_le_lawDomain _ _ _ _ (panels Y H V G P x.property)
 obtain ⟨u,h₁,h₂⟩:= Driver.ledger _ _ (flight Y H V G C P m q₀) x; obtain ⟨a,b⟩:=costsP Y H V G C P m q₀ x Q e
 rw [a,show Pc ⟨x.val,Q⟩=_ from moving_chime Y H V G C P.a t p.property Q] at h₁; refine ⟨u,h₁,fun hq=>?_⟩
 rw [b] at h₂; have ht:= rotate_moves Y H P t p.val; change RX x.val=_ at ht; rw [show Pc ⟨RX x.val,e⟩ =_ from (congrArg Pc (Subtype.ext ht)).trans (moving_chime Y H V G C P.a _ hq (ht ▸ e))] at h₂; exact h₂
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
