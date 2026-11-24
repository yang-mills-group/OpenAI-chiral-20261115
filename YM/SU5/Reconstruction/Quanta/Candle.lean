import YM.SU5.Reconstruction.PolarArchives.Terrain
import YM.SU5.Reconstruction.Quanta.Curves
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
local notation "H₀"=> Ark.Ht Y H G.history.circuit j 0 false (C j)
local notation "A"=>Aurora Y H V G.history j false (C j)
local notation "Pc"=>album Y H V G C j
local notation "pay"=> LightBudget.prepaid Y H V G j (C j)
local notation "vc"=>seat0 Y H V G.history j false (C j)
local notation "px"=> (A).orthogonalProjectionOnto
local notation "Nₐ"=> Domain Y H G false (flank j 0)
local notation "τ" => gust P (tent Y H)
open Chambers
local notation "μₜ" t:max=>move (tent Y H) (eject j t)
variable {q:Bool}{U:Set RSpace}
local notation "K₀"=>displayAlgebra Y H V G.history G.clipped j false (C j)
local notation "Ωχ"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped j false (C j)
local notation "Rs"=> reduceToDisplay Y H V G.history G.clipped j false (C j)
open Chambers Brazier
local notation "V₀"=> Nₐ
local notation "Rt" t:max=> Pub Y H j t
variable (m:MeshClock.marks (timeMesh Λ))(p:0< m)
local notation "xq" q:max=>Domain Y H G q (carton P (m:ℝ))
local notation "Cm"=> strip j (-(m:ℝ)) (m:ℝ)
section
private lemma issueC (d:marks (timeMesh Λ)){f:Sky (tent Y H)}(h:f∈ Domain Y H G false (strip j 0 (d:ℝ)))(p:0<d): ∃ B:Kw, (∀ u:f∈µ, Rs B=Pc ⟨f,u⟩)∧ ∀ x:V₀,∃ y:V₀,y.val=f* (Rt d) x.val∧ pay y=B.val (pay x):=by
 obtain ⟨s,⟨f,kf,rfl⟩,w,t,e⟩ := (((domain_eventually Y H G).1 h).and (notch_nat_event d p)).exists
 let d':= lantern Λ s w
 have he : (d:ℝ)=(whenly (timeMesh Λ) s w:ℝ) := by rw [←e]; exact natural_time ..
 rw [he] at kf; let x:= startOp Y H j s w f kf
 refine ⟨entrance Y H V s G.history G.clipped j false (C j) x t, fun u=>?_,fun z=>?_⟩
 · rw [atStamp]; exact Subtype.ext (compress_entry Y H V s G.history G.clipped j false (C j) x t)
 rw [←e]; exact Brazier.rootGraph Y H V G j (C j) s w x t z

private lemma pub_costC (d e:Gt)(f:Sky (tent Y H)) : (Rt d) ((Rt e) f)= (Rt (d+e)) f := pub_sum Y H j d e f
@[simp] private lemma pub_zeroC (f:Sky (tent Y H)): (Rt 0) f=f:= by unfold Pub; rw [eject_zero,move_by_zero]

-- core existence: in Symmetric Root, every prepared pair sensing this Board.
structure Candle (w:µ)(B:Kw):Prop where
 learns : Rs B= Pc w -- include C default
 makes(x:Nₐ): ((Mirror j) ((Rt m) x.val))*w.val*((Rt m) x.val)∈ Domain Y H G false Set.univ
 goes(x:Nₐ)(u: ((Mirror j) ((Rt m) x.val))*w.val*((Rt m) x.val) ∈µ):
    Ωχ ⟨((Mirror j) ((Rt m) x.val))*w.val*((Rt m) x.val),u⟩= inner ℂ (pay x) (B.val (pay x))
include p in
lemma squareCandle (w: Domain Y H G false Set.univ) (h:w.val∈ Domain Y H G false (strip j (-(m:ℝ)) (m:ℝ))): ∃ B:Kw, Candle Y H V G C j m w B:=by
 let d:Gt:=m+m; let F:=(Rt m) w.val
 have hx:F∈ D false (strip j 0 (d:ℝ)):= by
    apply domain_mono Y H G _ (moving Y H V G _ _ h)
    rintro _ ⟨z,t,rfl⟩; unfold d; replace t:(-(m:ℝ)≤ z j ∧ z j ≤ (m:ℝ)):=t; rw [AddSubgroup.coe_add,coordinates_eject]; change 0≤ z j + eject _ (m:ℝ) _ ∧ z j+eject _ (m:ℝ) _≤_
    rw [eject_at]; constructor<;>linarith [t.1,t.2]
 obtain ⟨B,B0,HB⟩:= issueC Y H V G C j d hx (add_pos p p); refine ⟨B,(B0 (domain_le_lawDomain Y H G _ hx)).trans (moving_chime Y H V G C j _ w.property _),?_,?_⟩
 all_goals
    intro x
    obtain ⟨y,hy,ht⟩:= HB x
    have hword : move K (eject j m) (((Mirror j) ((Rt m) x.val))*w.val*((Rt m) x.val))= flipMark j K x.val * y.val:=by
       have h₁ : (Rt m) ((Mirror j) ((Rt m) x.val))= flipMark j K x.val:=by rw [pub_negflip,pub_costC,add_neg_cancel,pub_zeroC]
       have h₂ : (Rt m) ((Rt m) x.val)=(Rt d) x.val:= pub_costC Y H j m m _
       rw [hy,move_prod,move_prod,h₁,h₂,mul_assoc]
    have hv := paired_forever Y H G j _ _ x.property y.property
 · let f:= ((Mirror j) ((Rt m) x.val))*w.val*((Rt m) x.val)
   apply domain_mono Y H G (subset_univ (slides (coordinates Λ (eject j (-m))) Set.univ))
   suffices q: move K (eject j (-m)) (move K (eject j m) f)∈ D false (slides (coordinates Λ (eject j (-m))) Set.univ) by
       change (Rt (-m)) ((Rt m) f)∈_ at q; rwa [pub_costC,neg_add_cancel,pub_zeroC] at q
   exact moving Y H V G _ _ (hword.symm ▸ hv)
 intro u; rw [←root_shift Y H V G j (C j) (eject j m) u (hword.symm ▸ hv),←ht]; exact (congrArg Ωχ (Subtype.ext hword)).trans (LightBudget.initial_pair Y H V G j (C j) x y).symm
end
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives.squareCandle
