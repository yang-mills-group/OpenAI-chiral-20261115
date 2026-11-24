import YM.CF.BProof.Rise.Gulf
import YM.CF.BProof.Rise.Trunk
/-! Local tests for transplant even on broken across neighborhoods. -/
set_option quotPrecheck false
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
open Economy Jet
variable (μ:Support (More N))(gμ: ∀ i∈μ, Calm Z k ξ w0 i){γ':ℝ}
-- Postponed after δ & Chart availability. cq and marketing.
structure Inside (S:Gates.Stage c w R v)(E:Essence D u) (δ γ:ℝ)(y:ℝ): Prop where
 shape: Economy.Pressure S.K (Rhythm.Lease.wearC S y) γ
 pays : xm*(Κξ (Rhythm.Lease.wearC S y) S.K.C*4) ≤ δ
 tarp : E.H.yC+3*xm*Κξ (Rhythm.Lease.wearC S y) S.K.C < u
section
end
structure Range (δ γ K ε:ℝ)(μ:Support (More N))(V: Pane N)(x x₀: Stun N) where
 U : ℝ→ Pane N
 X : ℝ→ Stun N
 plot(t:ℝ): TransK 1 U t K ∧ Jet.seek X 1 t K
 fuel(t): Lat.Slow (U t) (hook (X t)) γ
 safe(t): Guard (U t) δ
 done: (gG N).agree μ (U ε,X ε) (V,x)
 start : (U 0,X 0)=(1,x₀)
-- trans point on all over μ, incl Frame. wallet_agreement.
variable (Γ:Inside S E δ γ' y)
local notation "V_"=> Tape.carried (Z.pose P K xw).val.1
local notation "X_"=> Z.stun P xw.val
local notation "M_"=> Z.homX ΖQ
include Γ P
lemma sway(z:Fin 5): PaceX Set.univ 1 (Z.homX z) E.H.yC:= (Bias.homerP E Y Δ z).liftF _ _ _ _ _ _ Z.stageU.podium Z.pt Z.p0 (Bias.homerL E Y Δ δ Z.lineT.safe Z.lineT.height) (Instructions E P Y Δ Z.buyS).2.1 -- includes P in proof
include Pw gμ h
lemma spend_ (q:ℝ)(v:u≤q): Nonempty (Range δ q γ' δC μ V_ X_ M_) :=by
 let δ':= δC; let H:= (Rhythm.Lease.wear_p (y:=y) S).le; let W:= HF_; let X:= M_; let V(i:Bond (More N)):=if i.1∈μ∧i.1+step i.2∈μ then U (F_' Y P T θ xw.val) i else 1
 choose A t e using fun i:Seat N=> (show ∃ A:SU.E, cd G A 1≤δC ∧ (i∈μ→ X_ i=scaledV A (M_ i)) from by by_cases p:i∈μ; obtain ⟨a,h,q,v⟩:= Calm.morph P Z k ξ h w0 xw Pw (gμ i p); exact ⟨a,h,fun _=>q⟩; exact ⟨1,(cd_self ..).trans_le H,fun t=>(p t).elim⟩)
 have hp(i:Bond (More N)): cd G (V i) 1≤δ':=by unfold V; split; rename_i h; exact Calm.soft_W P Z k ξ ‹_› w0 xw Pw i (gμ _ h.1) (gμ _ h.2); exact (cd_self ..).trans_le H -- tune `‹_›`
 have he:= Γ.shape; let Z':= Economy.paths V δ'; let X':= Economy.fillX δ' X A; have ht:= Economy.guarding S.K V δ' hp X A he t δ Γ.pays E.H.yC q (sway P Z Γ _) (Γ.tarp.trans_le v); have hz: (gG N).agree μ (V,feast A X) (V_,X_):= (Veil.paired ..).2 ⟨(pine_eq μ).2 (fun i a b=> if_pos ⟨a,b⟩),(tent_eq μ).2 fun i p=> (e i p).symm⟩
 refine ⟨Z',X',fun z=>⟨path_pay S.K V δ' hp he z,fill_pay S.K _ X A he t z⟩, fun z=> (ht z).2,fun z=> (ht z).1,?_ ,?_⟩; rw [show Z' δC=V from path_end S.K _ δ' hp he, show X' δC=feast A X from fill_end S.K δ' X A he t]; exact hz; exact Prod.ext (path_zero ..) (fill_zero ..)
end YM.CF.BProof.Cliff
