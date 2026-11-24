import YM.SU5.Reconstruction.PolarArchives.Census
import YM.SU5.Reconstruction.Based.Enclosure
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
set_option quotPrecheck false
set_option maxHeartbeats 430000
namespace LineCharge
open SlabMark MeshClock PolarArchives
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)(χ: displayAlgebra Y H V G.history G.clipped j false (C j)→⋆ₐ[ℂ]ℂ)
local notation "W"=>displayAlgebra Y H V G.history G.clipped j false (C j)
local notation "µ"=> Domain Y H G false Set.univ
local notation "ℳ"=> Domain Y H G false (flank j 0)
local notation "P" => PolarArchives.album Y H V G C j
local notation "Ψ" s:max=>located Y H V s G.history G.clipped j false (C j)
variable (s:ℕ)
local notation "Ξ" => sameRead Y H V G j (C j) χ s
local notation "π" =>LightBudget.prepaid Y H V G j (C j)
-- Retain EXACT real query and budget positions for authentication on sharp device,
-- obtain ROOT positivity of a supplemental REAL Πw+ folded-back posed Mark. Use on any query.
noncomputable def matchWith(z:Cover) (f:Dome (tent Y H)) : Dome (tent Y H):= reposition K (-z) (aureole K j 0 (reposition K z f))
lemma match_as(z:Cover)(f:Dome (tent Y H)): matchWith Y H j z f*f=reposition K (-z) (aureole K j 0 (reposition K z f)*reposition K z f):= by rw [reposition_prod]; simp [matchWith]
lemma root_same_stamp (z:Cover)(f:Dome (tent Y H)): located Y H V s G.history G.clipped j false (C j) (asLoose K (reposition K z f))= (Ψ s) (asLoose K f):=by
 let T:=move K (stamps Λ s z); let Q(t:Dome (tent Y H)):=ticket Y H G s t
 have e:T (Q f)=Q (reposition K z f):= move_at Y H V G _ s f z rfl
 have hz(f:Dome (tent Y H)): Q f∈ µ:= ticket_loose ..
 rw [←PolarArchives.atStamp Y H V G C j s _ (hz _),←PolarArchives.atStamp Y H V G C j s f (hz _),show (⟨_,hz _⟩:Domain Y H G false univ) = ⟨T (Q f),e.symm ▸ hz _⟩ from Subtype.ext e.symm];
 exact moving_chime Y H V G C j _ _ _ -- implicit
include V C j in
lemma financing (z:Cover)(f:Dome (tent Y H)): E s (reposition K z f).val=E s f.val:=by
 let Ω:= seat0 Y H V G.history j false (C j)
 calc
    _ = inner ℂ Ω (((Ψ s) (asLoose K (reposition K z f))).val Ω) := (inspected Y H V s G.history G.clipped j false (C j) (F:=asLoose K (reposition K z f))).symm
    _ = inner ℂ Ω (((Ψ s) (asLoose K f)).val Ω) := by rw [root_same_stamp Y H V G C]
    _ = _ := inspected Y H V s G.history G.clipped j false (C j) (F:=asLoose K f)
lemma future_book (f:Dome (tent Y H)): ∃ z:Cover,reposition (tent Y H) z f∈ insideAt Λ l K false (flank j 0) s:=by
 obtain ⟨S,t⟩:= ((marque ..).1 f.property).paid
 obtain ⟨z,i,x,_⟩:= placementVoy Y H j S 0; refine ⟨z,(positive_today Y H j s _).2 ((purpose_ok ..).2 ?_)⟩; rw [area0]; exact ⟨⟨_,cad_test z _ t,x⟩, nofun⟩ -- nofun property
lemma positive_root (z:Cover) (f:Dome (tent Y H))(p: Ξ f≠0)(kz:reposition (tent Y H) z f ∈ insideAt Λ l K false (flank j 0) s): 0< (E s (matchWith Y H j z f*f).val).re:= by
 let a : insideAt Λ l K false (flank j 0) s:=⟨_,kz⟩; let x:=enclose Y H G (flank j 0) false s a; let Ω:=seat0 Y H V G.history j false (C j)
 have h: (Ψ s) (asLoose K f)≠0:=fun e=> p (by unfold sameRead; rw [os_ticket_val]; change χ ((Ψ s) (asLoose K f))=_; rw [e,map_zero])
 have hz: LightBudget.prepaid Y H V G j (C j) x≠0:=by
    intro y; apply h; rw [←root_same_stamp Y H V G C _ s z f]; apply display_faithful Y H V G.history G.clipped j false (C j); change ((Ψ s) (asLoose K a.val)).val Ω = _; rw [← atStamp Y H V G C j s _ (ticket_loose ..)];
    rw [←show (Aurora Y H V G.history j false (C j)).orthogonalProjectionOnto (π x) = (P (⟨_,ticket_loose ..⟩:Domain Y H G false Set.univ)).val Ω from PolarArchives.at_origin Y H V G C j x.property (ticket_loose ..), y,map_zero]; symm; exact ContinuousLinearMap.zero_apply ..
 rw [match_as, financing Y H V G C j]
 let Q:= aureole K j 0 a.val*a.val; have hp: inner ℂ (π x) (π x) = E s Q.val := by
    rw [LightBudget.initial_pair Y H V G j]
    let e:flipMark j K x.val*x.val=ticket Y H G s Q:=(paired_today Y H G j s a a).symm; rw [show (⟨_,_⟩:Domain Y H G false Set.univ) = ⟨_,ticket_loose Y H G s Q⟩ from Subtype.ext e,course_ticket_val]
 rw [←hp]; exact (re_inner_self_pos (𝕜:=ℂ)).2 hz
lemma turnup (f:Dome (tent Y H))(p: Ξ f≠0): ∃ z:Cover, 0 < (E s (matchWith Y H j z f*f).val).re ∧ ∀ᶠ r in atTop,0 < (sharp Y H s (i (G.rows r)) (k (G.columns r)) (matchWith Y H j z f*f).val).re:=by
 obtain ⟨z,t⟩ := future_book Y H j s f; have h:= positive_root Y H V G C j χ s z f p t; refine ⟨z,h,?_⟩
 let g:Dome (tent Y H):= matchWith Y H j z f*f; exact (Complex.continuous_re.continuousAt.tendsto.comp (PhaseChoice.final_limit Y H G s g.val ((marque ..).mp g.property))).eventually (lt_mem_nhds h)
end LineCharge
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LineCharge.turnup
