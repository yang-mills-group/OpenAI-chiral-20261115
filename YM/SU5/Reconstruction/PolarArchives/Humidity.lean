import YM.SU5.Reconstruction.PolarArchives.Diligence
import YM.SU5.Reconstruction.PolarArchives.Script
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
local notation "Hₛ"=> groundRoom Y H V G.history P.a false (C P.a)
local notation "Ωχ"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped P.a false (C P.a)
local notation "Rs"=> reduceToDisplay Y H V G.history G.clipped P.a false (C P.a)
local notation "RX"=>rotateQ P K
-- using ANY clock's resident. P.a fixed reader analysis already.Need Boo receipt here
local notation "Z"=> displayAlgebra Y H V G.history G.clipped j false (C j)
local notation "B₀"=> album Y H V G C j
local notation "φ"=> whiff Y H V G C j χ
local notation "Pt"=>Pave Y H V G C j χ
local notation "P₀"=> adjustment Y H V G.history G.clipped P.a false (C P.a) j (C j)
local notation "VR"=> Veer Y H V G P
local notation "TT"=> Tango Y H V G P
local notation "OR"=> orbit Y H V G C P
lemma adjust_album (f:Domain Y H G false Set.univ): P₀ (Pc f)= album Y H V G C j f:=by
 obtain ⟨s,b,rfl⟩:=(eventually_enclosed Y H G f).exists; change P₀ (Pc (⟨ticket Y H G s b.val,ticket_loose ..⟩))= album Y H V G C j ⟨ticket Y H G s b.val,ticket_loose ..⟩
 rw [atStamp,atStamp,adjust_adj]
noncomputable def smile: displayAlgebra Y H V G.history G.clipped j false (C j) ≃⋆ₐ[ℂ] displayAlgebra Y H V G.history G.clipped j false (C j) := (P₀).symm.trans ((OR).trans P₀)
local notation "Bu"=> smile Y H V G C j P -- order h19E? C before j etc
lemma smile_on (w:µ): smile Y H V G C j P (album Y H V G C j w)=album Y H V G C j (VR w):=by change P₀ (OR ((P₀).symm _))= _; have h: (P₀).symm (album Y H V G C j w)=album Y H V G C P.a w:= (congrArg ((P₀).symm) (adjust_album Y H V G C j P w).symm).trans ((P₀).symm_apply_apply _); exact (congrArg (fun x=> P₀ (OR x)) h).trans ((congrArg P₀ (orbit_lift Y H V G C P w)).trans (adjust_album Y H V G C j P (VR w)))
lemma rolling(u:Z): Bu (Bu u)=u := by
 change P₀ (OR ((P₀).symm (P₀ (OR ((P₀).symm u)))))=_; rw [StarAlgEquiv.symm_apply_apply,orbit_square,StarAlgEquiv.apply_symm_apply]
noncomputable def chargeTilt : displayAlgebra Y H V G.history G.clipped j false (C j)→⋆ₐ[ℂ] ℂ:= χ.comp (smile Y H V G C j P).toStarAlgHom
local notation "χ'"=> chargeTilt Y H V G C j χ P
lemma at_map (x:Domain Y H G false univ): album Y H V G C j (TT x) = star (album Y H V G C j (VR x)):=by rw [←adjust_album Y H V G C j P,← adjust_album Y H V G C j P (VR x),(newsTags Y H V G C P x).1]; exact (P₀).map_star' _
lemma character_rotation (x:Domain Y H G false univ): whiff Y H V G C j χ (gust P (tent Y H) x.val)=star (whiff Y H V G C j (chargeTilt Y H V G C j χ P) x.val):=by
 rw [← tier Y H V G C j χ _ (show gust P K x.val∈µ from (TT x).property),← tier Y H V G C j χ' _ x.property]; change χ (B₀ (TT x))= star (χ (Bu (B₀ x))); rw [smile_on,at_map,map_star]
lemma epoch_mark(s:ℕ)(x:Dome (tent Y H)):
    oneAt Y H V G j (C j) (chargeTilt Y H V G C j χ P) s x=oneAt Y H V G j (C j) χ s (epoch (tent Y H) P x):=by
 let f:Dome K:= aureole K P.a 0 x; let W: µ:= ⟨ticket Y H G s x,ticket_loose ..⟩; let Xq: µ:= ⟨_,domain_le_lawDomain _ _ _ _ (mirror_support Y H G P.a W.val W.property)⟩; let Q:= chargeTilt Y H V G C j χ P; let Zt:= gust P K Xq.val
 have hz: Zt = ticket Y H G s (epoch K P x):=keeps_epoch Y H V G P s x -- order 
 have hb:whiff Y H V G C j Q Xq.val=star (whiff Y H V G C j Q W.val):= (plain Y H V G C j Q P.a).fuel W.val W.property
 have ht:= character_rotation Y H V G C j χ P Xq; unfold Zt at hz; unfold Q at hb; rw [hz,hb,star_star, funds_stamp Y H V G C j χ (ticket_loose ..),funds_stamp Y H V G C j χ' W.property, os_ticket_val] at ht; exact ((os_ticket Y H V G j (C j) Q s x).symm.trans ht.symm) -- orient HT

variable (gap:ℝ≥0)(h:Rectitude Y H V G P gap)
include h
lemma restored_rotation : chargeTilt Y H V G C j χ P= χ:= DFunLike.ext _ _ fun v=>by change χ (P₀ (OR ((P₀).symm v)))=χ v; rw [state_root _ _ _ _ _ _ _ h,StarAlgEquiv.apply_symm_apply]
noncomputable def approval: Blush Y H V G C j χ P.s:=
 ⟨gust P K, gust_square P,fun _ _ _ p=> shelters Y H V G P p,P.swing,gust_unit ..,gust_mul P,zone_gust Y H P,gust_mirror P,fun x hx=> (character_rotation Y H V G C j χ P ⟨x,hx⟩).trans (by rw [restored_rotation _ _ _ _ _ _ _ _ _ h])⟩
noncomputable def tableau: Pt (P.s*Signed.mirror P.a):= Blush.properMem Y H V G C j χ (plain Y H V G C j χ P.a) (approval Y H V G C j χ P gap h)
lemma tableau_is (x:Sky (tent Y H)): (tableau Y H V G C j χ P gap h).shift x=gust P K (flipMark P.a K x):=rfl
lemma beyond_χ : RPos_remote Y H V G P C j χ gap:=by
 intro x u; let w: D true (Acres P gap):=⟨x,u⟩; let Zp:= TerrainOf Y H V G P gap w; rw [←tier Y H V G C j χ _ (show τ x*x∈µ from Zp.property),show (album Y H V G C j) ⟨τ x*x,_⟩= (P₀) (Pc Zp) from (adjust_album Y H V G C j P Zp).symm]
 exact _root_.map_nonneg χ (_root_.map_nonneg (P₀).toStarAlgHom (voting _ _ _ _ _ _ _ h w)) -- order circ tune
noncomputable def raybooks : Chat_remote Y H V G P C j χ gap := Classical.choice (available_phase_Kermit_remote Y H V G P C j χ gap (beyond_χ Y H V G C j χ P gap h))
omit h
open LightBudget
lemma core (p:∀P:Ramp,∃ gap:ℝ≥0,Rectitude Y H V G P gap):BoostBacking Y H V G C j χ:= by
 apply Consult.funded Y H V G C j χ (r:=0) le_rfl; intro x y z u v; let p':Ramp:= ⟨x,y,z⟩; obtain ⟨delta,he⟩:= p p'; exact outgoBook_remote Y H V G p' C j χ delta (raybooks Y H V G C j χ p' delta he) v
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
