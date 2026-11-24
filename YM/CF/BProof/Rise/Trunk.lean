import YM.CF.BProof.Rise.Shelf

set_option autoImplicit false
/- 4 ξ x voltage for three trace terms. -/
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
open Stint TraceD
-- Stamp.L tests run before or after closure price. Cov term birth.
abbrev Fst(L: Honor D K δ):= Tape.kiln L.1 Δ.stage.c rateH Δ.stage.η
local notation "Hz"=>Z.age P K
variable {yv:Pay}(H: TraceD (Z.age P K) Δ.stage.c rateH Δ.stage.η yv)
local notation "θA"=> Z.pose P K xw
local notation "θB"=> Z.hom P K ΖQ
section Toll
abbrev voltage:= wealthX D.hT (Rhythm.Lease.wearC S y) ξ -- tune binder Lean
variable (μ:ℕ)
def money_θ (E:Spin.Ready j a₁ b l r)(S:Gates.Stage c w R v)(y:ℝ)(ξ:ℕ) := wealthX E.hT (Rhythm.Lease.wearC S y) ξ
lemma voteV :0≤ money_θ D S y ξ:=by unfold money_θ wealthX; have hh:= (Rhythm.Lease.wear_p (y:=y) S); have he:=xm_p; unfold baseΦ; have hk:=rate_p; positivity
lemma vote_up {μ:ℕ}(p:μ≤ξ): wealthX D.hT (Rhythm.Lease.wearC S y) μ≤ money_θ D S y ξ:=by unfold money_θ wealthX baseΦ; have ht:= Rhythm.Lease.wear_p S (y:=y); have he:=xm_p; have hk:= rate_p; gcongr
variable {d':ℕ}{ν0 C0:ℝ}
lemma household (u:Desk N)(h': (zDesk u).card ≤ ξ)(g:∀ i∈ zDesk u, Calm Z k ξ w0 i)(h:Clock Z k ξ)(p:w0∉ nearL Y xw.val) : ‖H.items u θA-H.items u θB‖≤ money_θ D S y ξ * H.charge u :=by
 let A:=θA; let B':=θB; let V:=money_θ D S y ξ; let κ:=Tape.kiln (Z.age P K).1 Δ.stage.c rateH Δ.stage.η; let S:=(TraceD.proj u).2; have he:κ.st.eval S θA θB≤V:= (κ.st.includeV (show S⊆zDesk u from subset_insert ..) _ _).trans ((coverH P Z k ξ K h w0 xw p g).trans (vote_up (D:=D) ξ h')); rw [mul_comm]
 rcases u with i|(i|i)
 · let y(x):= H.realT.line i x; change ‖πReal _-πReal _‖≤ H.realT.pay i * V; apply le_trans (b:=‖y A.val.1-y B'.val.1‖); · unfold πReal; rw [← Complex.ofReal_sub,Complex.norm_real, ←Complex.sub_re]; exact Complex.abs_re_le_norm (_:ℂ)
   refine ((H.realT.taxes i).varies ..).trans (mul_le_mul_of_nonneg_left (le_trans ?_ he) (H.realPrice.nonneg i)); -- state proof primary
   exact le_add_of_nonneg_right (sum_nonneg (fun i _=> Tape.Skein.toll_pos ..)) -- tune exact statement κ.st eval path
 · let y(x):= H.biasT.line i x; change ‖πReal _-πReal _‖≤ H.biasT.pay i * V; apply le_trans (b:=‖y A-y B'‖); · unfold πReal; rw [← Complex.ofReal_sub,Complex.norm_real, ←Complex.sub_re]; exact Complex.abs_re_le_norm (_:ℂ)
   exact ((H.biasT.taxes i).varies ..).trans (mul_le_mul_of_nonneg_left he (H.biasPrice.nonneg i))
 let y(x):= H.imagT.line i x; change ‖Spire.zen _-Spire.zen _‖≤ H.imagT.pay i * V; apply le_trans (b:=‖y A-y B'‖); · unfold Spire.zen; rw [←mul_sub,norm_mul,Complex.norm_I,one_mul,←Complex.ofReal_sub,Complex.norm_real, ←Complex.sub_im]; exact Complex.abs_im_le_norm (_:ℂ)
 exact ((H.imagT.taxes i).varies ..).trans (mul_le_mul_of_nonneg_left he (H.imagPrice.nonneg i))
end Toll
end YM.CF.BProof.Cliff
