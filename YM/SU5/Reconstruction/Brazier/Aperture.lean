import YM.SU5.Reconstruction.Brazier.Beacon
import YM.SU5.Selected.Flights
/-! Funding compactness on the FULL ARK at each oriented polynomial query, not just station-wise. Transfers to estimates for approximating the communication χ norm costs. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "X" => Cloud (Dome (tent Y H))
local notation "Kx" t:max=> vistaFinish Y H t Z
local notation "Px" => LightBudget.prepaid Y H V G j C
local notation "σ"=> driveAlgebra Y H V G.history G.clipped j false C
local notation "Z₀"=> reduceToDisplay Y H V G.history G.clipped j false C
open PhaseChoice
namespace Wallet
local notation "Zx"=>allBox Y H V G j
lemma compact_cap (S:Finset Cover)(s w:ℕ)(p:Between K j 0 (ruler Λ.block*w) S)(hw:0<w):
  IsCompactOperator (allBox Y H V G j S s C w p hw):=by
 obtain ⟨p',hw'⟩:= escalatesPlace Y H j S s w p hw
 let t := wingspan Λ l S; let w' := Λ.R.L.val^(s+1-s)*w; let U:= Zx S s C w p hw; let V':= Zx t (s+1) C w' p' hw'; let L:=PhaseChoice.transfer Y H G S s
 have he : U=V'.comp L:=by
   ext1 x; let y:= toEntry Y H j false S s w p (allHues Y H S x); let y':= furnished Y H s G.history j false w y (s+1) (by omega)
   have hd:y'.val.val=render t K (L x):=by change stream Y H G.refine s (s+1-s) (render S K x)=_; rw [show s+1-s=1 from by omega]; exact transferred ..
   exact (refined_box Y H V s G.history G.clipped j false C w y hw (s+1) (by omega)).trans (box_chart Y H V G j t (s+1) C w' p' hw' _ hd)
 change IsCompactOperator U; rw [he]; exact (compact_resolution Y H V G S s).clm_comp V' 
end Wallet
open Tarmac Chambers
namespace Tarmac
variable {a:Tarmac}{w:ℕ} (p:Tarmac.Stage Λ l j a w)
local notation "s"=> a.roof
local notation "S"=>frameBudget a.book Λ l a.roof
variable {x:Cloud (Dome (tent Y H))}{r:ℝ}
-- full mark-tape
local notation "T"=> (w+w)
local notation "y" x:max=> center Y H j w ((Kx (a.roof)) x)
local notation "N"=> notch (timeMesh Λ)
lemma Stage.hwords (p: Stage Λ l j a w) : 0<w+w:= add_pos p.pos p.pos
local notation "Ψ"=> a.balcony Y H j w
local notation "λ₀" x:max t:max=> entrance Y H V (a.roof) G.history G.clipped j false C x t
local notation "Ω"=> groundRoom Y H V G.history j false C
local notation "bZ" => allBox Y H V G j (Ψ) (s) C (w+w) (a.between Y H j w p) p.hwords
variable (hx:Pocket (tent Y H) a.book a.roof r x)
noncomputable def representationOf (p:Stage Λ l j a w)(hx:Pocket (tent Y H) a.book a.roof r x) : Entry Y H (a.roof) j false (w+w) :=
 startOp Y H j (a.roof) (w+w) (center Y H j w (vistaFinish Y H (a.roof) Z x)) ((mem_insideAt ..).2 ⟨⟨_,a.center_shift Y H j w _ (shaping Y H Z _ _ _ hx), (strip_seats ..).2 (a.between Y H j w p)⟩,nofun⟩)
lemma markPreparation : (representationOf Y H Z j p hx).val.val=(y x).val:=rfl
noncomputable def credit (p:Stage Λ l j a w) (hx:Pocket (tent Y H) a.book a.roof r x): driveAlgebra Y H V G.history G.clipped j false C :=
 λ₀ (representationOf Y H Z j p hx) p.hwords
local notation "Pt"=> credit Y H V G Z j C
lemma paycheck : (Z₀ (Pt p hx)) = located Y H V (a.roof) G.history G.clipped j false C (asLoose K (y x)):=
 Subtype.ext (compress_entry Y H V (a.roof) G.history G.clipped j false C (representationOf Y H Z j p hx) p.hwords)
lemma pays_character : χ (Z₀ (Pt p hx))= oneAt Y H V G j C χ a.roof (vistaFinish Y H a.roof Z x) := by
 rw [paycheck]; change oneAt Y H V G j C χ a.roof (y x)=_
 let f:= (Kx (a.roof)) x; let z:= eject j (w:ℤ)
 have h' : move K (stamps Λ a.roof z) (ticket Y H G a.roof f) = ticket Y H G a.roof (y x):=move_at Y H V G _ a.roof f z rfl
 have hm := moving_value Y H V G j C χ (stamps Λ a.roof z) (ticket_loose Y H G a.roof f) (h'.symm ▸ ticket_loose ..)
 rwa [show (⟨_,_⟩ : D false Set.univ)= _ from (Subtype.ext h': (⟨_,h'.symm ▸ ticket_loose ..⟩ : D false Set.univ)= ⟨ticket Y H G a.roof (y x), ticket_loose ..⟩), os_ticket_val,os_ticket_val] at hm

noncomputable def upliftBox (p:Stage Λ l j a w) : Swatch (a.balcony Y H j w) →L[ℂ] (driveAlgebra Y H V G.history G.clipped j false C) :=
 ContinuousLinearMap.codRestrict (allBox Y H V G j (Ψ) (a.roof) C (w+w) (a.between Y H j w p) p.hwords) (σ).toSubalgebra.toSubmodule (fun x=>object_in_drive Y H V (a.roof) G.history G.clipped j false C (toEntry Y H j false Ψ s T (a.between Y H j w p) (allHues Y H _ x)) p.hwords)
lemma receipt_funded : ∃ b:Swatch (a.balcony Y H j w), upliftBox Y H V G j C p b = Pt p hx ∧
 ‖b‖ ≤ (spread (frameBudget a.book Λ l a.roof):ℝ) * (Hank Y H a.book a.roof B * r):=by
 obtain ⟨b,hc,he⟩:= a.translatedWallet Y H Z j w hx
 exact ⟨b,Subtype.ext (box_chart Y H V G j (Ψ) (s) C (w+w) (a.between Y H j w p) p.hwords (x:=representationOf Y H Z j p hx) b (hc.symm : (representationOf Y H Z j p hx).val.val=_)).symm,he⟩
lemma budget_compact : IsCompactOperator (upliftBox Y H V G j C p) :=
 (Wallet.compact_cap Y H V G j C (Ψ) (a.roof) (w+w) (a.between Y H j w p) p.hwords).codRestrict (V:=(σ).toSubalgebra.toSubmodule) (fun x=> (upliftBox Y H V G j C p x).property) (drive_closed Y H V G.history G.clipped j false C)
lemma stage_hold (r:ℝ) (p:Stage Λ l j a w): ∃ U:Set (driveAlgebra Y H V G.history G.clipped j false C), IsCompact U ∧ ∀ x:Cloud (Dome (tent Y H)),∀ hx:Pocket (tent Y H) a.book a.roof r x, Pt p hx ∈ U:=by
 refine ⟨closure ((upliftBox Y H V G j C p) '' Metric.closedBall 0 ((spread (S):ℝ)*(Hank Y H a.book s B * r))), (show IsCompactOperator (upliftBox Y H V G j C p).toLinearMap from budget_compact Y H V G j C p).isCompact_closure_image_closedBall _,fun x hx=>?_⟩
 obtain ⟨b,f,c⟩:= receipt_funded Y H V G Z j C p hx; exact subset_closure ⟨b,mem_closedBall_zero_iff.mpr c,f⟩
end Tarmac
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
