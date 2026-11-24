import YM.CF.BProof.Prime.Clock
import YM.CF.BProof.Prime.Estate
/-! Uniform non-Unsafe zone. gauge phase lift vs reference z.-/
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Cliff
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye Seam
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}(Y:S.Setup L a (More N) d y)(P:Entice S L a d y)(T:PathData G)(θ:ℝ)(x:Pod Y)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "g₀"=> Y.g
local notation "wB"=>House.Season mH Y.c'
local notation "gE"=>Trek.tag mH
local notation "πX"=> Cabinet.roadB Y
local notation "rawK"=> rawG Y P T θ
local notation "K_"=> Y.hall
open Hero Mark
open Spin Dream Fock Dial -- fix
set_option maxHeartbeats 260000
local notation "Ζ_"=>framesL Y P T θ
local notation "CC"=>Y.yard.long
open Rhythm Tape Hearth Lat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N₁ N₂:ℕ} {m m':Side}{j:ℕ} {a₁ b l r:ℝ}{D:Spin.Ready j a₁ b l r}{u:ℝ} (E:Essence D u)
variable {rₜ:ℕ} (Δ:Rhythm.Note E (Gates.gap L a) rₜ)(U: Orbit N → Pane N) (ν δ:ℝ)
variable {rB:ℕ}
variable {Y E T θ Δ U ν δ} (Z : School Y T θ E Δ U ν δ rB)
open Scope Moment Push.AbsoluteSums
local notation "μz"=> Z.μwage
variable (k ξ:ℕ) -- near depth, and size cutoff in F support
open Branch Tenant Air Veil Prime
variable {α C:ℝ}{I:Type}[Fintype I](K:Core j a₁ b l r N)
variable (Q:Primer N I α C)
local notation "Ψ"=> Pouch Y P T θ
local notation "ψx"=>Z.world1 P K
local notation "ψ0"=>Z.world0 P K
open Prime
variable (h:Clock Z k ξ)(w0:House.Block Y.yard Y.c')(xw:Pouch Y P T θ)
local notation "FΘ"=>Z.easyMoney P xw
local notation "κW"=> rawG Y P T θ xw.val
local notation "HF_"=> Seam.wear Y P T θ Z.f xw.val
local notation "HFΘ"=> Estate.road Z
local notation "δC"=> Rhythm.Lease.wearC S y
local notation "C_"=> Δ.clock
local notation "ΨN"=> Pouch Y P T θ
local notation "ΖQ"=> central Y xw.val w0
local notation "timeK"=> TimePlus k ξ μz
variable (Pw:w0∉ nearL Y xw.val){i:Y.yard.Index}{b':Seat N}
abbrev Blaze (b:Y.Block) (i:Seat N): Prop:= Cabinet.roadB Y i ∈ray mH b 1
structure Calm (b:House.Block Y.yard Y.c')(x:Seat N): Prop where
 tag: Blaze (Y:=Y) b x
 up : Y.yard.Vic (gE x) (TimePlus k ξ Z.μwage) (time x)
include h
lemma after_clock {μ:Support (More N)}(v:Air.atFall Y k μ)(t:Micro.Loc μ)(k':μ.card≤ξ)(x:Seat N)(p:x∈μ)(g:b'∈μ): Calm Z k ξ (πX x) b':=by
 obtain ⟨⟨i,v⟩,p⟩:= h.paysL Z k ξ t p v k' (Lattice.halo_subset _ _ g); exact ⟨p, (show gE b'=i from Posts.vic mH i _ (h.commuter Z k ξ _ le_rfl) v) ▸ v⟩
namespace Calm
variable (vT: Calm Z k ξ w0 b')
include vT
omit h in
lemma breezy : πX b' ∈ ray mH w0 1:= vT.tag
include Pw
omit h in
lemma dune : Trek.distant mH g₀ (Cabinet.sick Y xw.val) b' 6:=by
 by_contra g; exact halo_far Y hNear 6 1 (by decide : 1+6 ≤ hNear) vT.tag Pw ((Seam.nearhood Y).1 g)
lemma piece_true : let w:=HF_; let u:=HH_ Y P T θ xw.val Z.f Δ.clock Z.p U b'; let v:=XX_ Y P T θ xw.val Z.f Δ.clock Z.p U b'; b'∈ ChillF mH g₀ (Cabinet.sick Y xw.val) Δ.clock.blockY ∧ v=w.over b'∧ u=w.port C_ b' := (Z.lic_ P _ xw.property).expand_true Z.stageU.podium (Instructions E P Y Δ Z.buyS).2.1 Z.pt Z.p0 (Z.lamp_ P _ xw.property) b' (.inr (clear_weaker mH g₀ _ _ _ (dune P Z k ξ w0 xw Pw vT) (by decide : 3 ≤ 6))) -- tune args
omit vT in
lemma soft_W (i:Bond (More N))(e:Calm Z k ξ w0 i.1)(p: Calm Z k ξ w0 (i.1+step i.2)): cd G ((U (F_' Y P T θ xw.val)) i) 1≤δC:=by
 have g:= (Z.lamp_ P xw.val xw.property).outside i (e.piece_true P Z k ξ h w0 xw Pw).1 (p.piece_true P Z k ξ h w0 xw Pw).1; change κW i=(U (F_' Y P T θ xw.val)) i at g; rw [←g,cd_symm,cd_one]; refine Rhythm.Lease.nearT P Y T θ (Cabinet.tool Y xw.val) Z.lineT.raw Z.lineT.ok xw.property (TimePlus k ξ μz) (by have ht:= h.tall; have :=Deep.D_le mH; omega) Z.buyS.look i (gE i.1) e.up (clear_weaker mH g₀ _ _ _ (dune P Z k ξ w0 xw Pw e) (by decide : 1≤6)) -- issue includes vT
lemma stamp_p : (HF_).code b' = ΖQ:=by
 let f:=Trek.planeN mH (Cabinet.tool Y xw.val).mood; let z:= (gE b',BProof.space b'); have ht:Cabinet.stampY Y xw.val z=ΖQ:= good_stamp P Y T θ xw.val w0 Z.lineT.raw Z.lineT.ok xw.property Pw z vT.tag (by decide : 1+1≤hNear); apply Eq.trans _ ht; rw [column_stamp]; unfold Script.code; change Trek.planeN ..=_; unfold Trek.planeN nX nB Pods.Manual.nIndex Pods.Manual.nSide -- names tune
 split <;> rfl
-- change by an actual near rotation A (varies with point). Supplies hom_ticket comparisons including all t !
omit h Pw vT
include Z
lemma port_morph {A:Trek.Script Y.yard}(b:Cabinet.Pod Y) {V:Pane N} (V': Trek.Permit A Δ.clock V Y.g (Cabinet.sick Y b) (Rhythm.Lease.wearC S y)) (x:Seat N)(v: Trek.distant mH g₀ (Cabinet.sick Y b) x 2)(hT:∀ i:Y.yard.Index,x∈Y.yard.band i→ chip (Y.yard.u i) CC x*10≤CC) (z:Fin 5)(g:A.code x=z): let B':= homeScript mH z; ∃ a:SU.E, cd G a 1≤δC∧ A.over x=scaledV a (B'.over x)∧ A.port C_ x= motion a ∘ B'.port C_ x:=by
 intro B'; let i:=hr mH x; have he:= Z.stageU.podium; let G':= Bias.homerP E Y Δ z
 have h0 (v:A.over x=B'.over x)(w:A.port C_ x=B'.port C_ x): ∃ a:SU.E, cd G a 1≤δC ∧ A.over x=scaledV a (B'.over x)∧ A.port C_ x= motion a ∘ B'.port C_ x:=by use 1; rw [motion_one,scaled_one]; exact ⟨(cd_self ..).trans_le (Rhythm.Lease.wear_p S).le,v,w⟩ -- id comp
 by_cases hl: Trek.dark mH x; swap; · apply h0; unfold Script.over; rw [if_neg hl,if_neg hl,g]; rfl; unfold Script.port; rw [if_neg hl,if_neg hl,g]; rfl
 have hx:x∈Y.yard.band i:= Trek.band_pick mH x hl; by_cases d:Y.yard.D i; · obtain ⟨v,g⟩:=V'.levelD C_ he hx d; exact h0 (v.trans (G'.levelD C_ he hx d).1.symm) (g.trans (G'.levelD C_ he hx d).2.symm)
 obtain ⟨p,u,t⟩:= V'.Ticket C_ he v hx d (hT i hx); obtain ⟨P0,K0,W0⟩:= G'.Ticket C_ he (Trek.emptyB mH g₀ (gE x) (BProof.space x) 2) hx d (hT i hx); let R:=A.frame i x; let l:=locus z; let c:=Mag.center z; change B'.port C_ x=motion (l*c) ∘ amend z (Trek.Script.ramp C_ i x) at P0; change B'.over x=scaledV l apex at K0; have hz:l*c=1:= inv_mul_cancel c; have hv:c*l=1:= mul_inv_cancel c
 rw [g] at p t; refine ⟨R*c, (Trek.Permit.booster z R).trans_le t,?_ ,?_⟩
 · rw [u,K0,←scaled_seq (R*c),mul_assoc,hv,mul_one]
 rw [p,P0,hz,motion_one]; rfl -- tune

include vT h Pw
lemma morph : ∃ A:SU.E, cd G A 1 ≤ δC ∧ Z.stun P xw.val b'=scaledV A (Z.homX ΖQ b') ∧ FΘ b'=motion A ∘ Estate.road Z ΖQ b' :=by
 obtain ⟨_,q,g⟩:= vT.piece_true P Z k ξ h w0 xw Pw; have hp:Estate.road Z ΖQ b'=(homeScript mH ΖQ).port C_ b':= spectra ..; have hx:Z.homX ΖQ b'=(homeScript mH ΖQ).over b':= starRise mH g₀ ΖQ C_ Z.p Z.stageU.podium Z.pt Z.p0 b'; change FΘ b'= (HF_).port C_ b' at g; change Z.stun P xw.val b'=(HF_).over b' at q
 rw [g,q,hx,hp]; apply port_morph Z xw.val (Z.lic_ P _ xw.property) b' (clear_weaker mH g₀ _ _ _ (vT.dune P Z k ξ w0 xw Pw) (by decide : 2≤6)) _ ΖQ (vT.stamp_p P Z k ξ h w0 xw Pw); intro i u; have hx:= vic_chip mH u (show 2*(TimePlus k ξ μz)<CC from by have := h.commuter Z k ξ (TimePlus k ξ μz) le_rfl; omega) vT.up; have := h.tall; have :=Deep.D_le mH; omega

end Calm
end YM.CF.BProof.Cliff
