import YM.CF.BProof.Rise.Plate
import YM.CF.BProof.Prime.Levy
/-! Lease.Bl traces variation including path derivatives on all arguments. -/
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
variable (vT: Calm Z k ξ w0 b')
abbrev baseΦ(s:ℝ):= 2*xm*s*rateH -- name?
lemma budgetP (X Y:ℝ→Stamp)(p:Money X)(q:Money Y)(u:ℝ)(v:0≤u) (g:SU.E)(d:cd G g 1≤u)(h:X=motion g ∘ Y)(i:Tape.Key): Tape.wage (Tape.drawQ X p) (Tape.drawQ Y q) i ≤ baseΦ u:=by
 let θ:=baseΦ u; have hp:0≤θ:= mul_nonneg (mul_nonneg (mul_nonneg zero_le_two xm_p.le) v) rate_p.le; have he(F:Stamp)(k:‖F‖≤rateH): ‖motion g F - F‖≤θ:=by
    have hv:= seat_rate g 1 F k; rw [motion_one,id_eq] at hv; refine hv.trans ?_; unfold θ baseΦ; have hx:=Hero.xm_p; have ht:= Hero.rate_p; gcongr -- tune
 unfold Tape.wage; apply (ContinuousMap.norm_le _ hp).2; intro i'; change ‖Tape.payT X i.1 i.2 (Tape.visit i'.val).val -Tape.payT Y i.1 i.2 (Tape.visit i'.val).val‖≤_; rw [Tape.walk_visit]; rcases i with ⟨i,b|b⟩; change ‖X _ -_‖≤_; rw [h]; exact he _ ((q.weight _).trans_le expenses.one)
 change ‖deriv X _ - deriv Y _‖ ≤ _; rw [h,Hero.motionDer _ q.2.1]; exact he _ (q.2.2 _ (Tape.T_b i _ i'.property))
include vT h Pw
local notation "Ω"=>baseΦ δC
local notation "θA"=> Z.pose P K xw
local notation "θB"=> Z.hom P K ΖQ
local notation "HΘ"=>Z.age P K
lemma wageF(i:Tape.Key): Tape.wage ((θA).val.2.val b') ((θB).val.2.val b') i≤ Ω:=by -- notation (θA).val issue parse
 obtain ⟨a,p,e,g⟩:= vT.morph P Z k ξ h w0 xw Pw; exact budgetP (Z.easyMoney P xw b') (Estate.road Z ΖQ b') (Z.capital P xw b') (Estate.road_cost P Z ΖQ b') δC (Rhythm.Lease.wear_p S).le a p g i
lemma tollF : Tape.Skein.toll b' (θA).val.2 (θB).val.2 ≤4*Ω:=by
 unfold Skein.toll; apply le_trans (sum_le_sum (fun i _=> wageF P Z k ξ K h w0 xw Pw vT i)); simp [Key]
lemma cleaner : b'∈spot ((θA).val.1.val.2) ↔ b'∈ spot ((θB).val.1.val.2):=by
 by_cases e:∃ x:Site N,b'=node x; swap; · apply iff_of_false (fun v=>e ?_) (fun v=>e ?_) <;> obtain ⟨j,h,p⟩:= spotsNN _ v<;> exact ⟨_,p.symm⟩
 obtain ⟨x,rfl⟩:=e; rw [spot_spec,spot_spec]; change x∈Pins mH g₀ (sick Y xw.val) ↔ x∈Pins mH g₀ ∅; rw [pins,pins]; apply and_congr_right; intro e; exact iff_of_true (vT.dune P Z k ξ w0 xw Pw) (Trek.emptyB ..) -- tune applies auto elaboration
omit vT
variable {μ:Support (More N)}(g:∀ i∈μ, Calm Z k ξ w0 i)
include g
abbrev wealthX(a b:ℝ)(k:ℕ):= (k:ℝ)*4*(xm*b) / |a| +(k:ℝ)*(4*baseΦ b)
lemma coverH : let L:= (Z.age P K).1; (Tape.kiln L Δ.stage.c rateH Δ.stage.η).st.eval μ θA θB ≤ wealthX D.hT δC μ.card:=by
 intro L; have hp:0≤δC:= (Rhythm.Lease.wear_p S).le; change ((fa (Tape.carried (θA).val.1) (Tape.carried (θB).val.1) μ / |D.hT|)+ ∑ i∈μ,dots i ((θA).val.1.val.2) ((θB).val.1.val.2))+∑ i∈μ,Tape.Skein.toll i _ _≤_; unfold dots; rw [sum_eq_zero (fun i t=>if_pos (cleaner P Z k ξ K h w0 xw Pw (g i t))),add_zero]
 apply add_le_add
 · apply div_le_div_of_nonneg_right _ (abs_nonneg D.hT); apply fa_bound (mul_nonneg xm_p.le hp); intro i v; apply (optic ..).trans; exact mul_le_mul_of_nonneg_left (Calm.soft_W P Z k ξ h w0 xw Pw i (g _ (mem_filter.mp v).2.1) (g _ (mem_filter.mp v).2.2)) xm_p.le
 exact ((sum_le_sum (fun i p=> tollF P Z k ξ K h w0 xw Pw (g i p))).trans_eq (by rw [sum_const,nsmul_eq_mul]))
namespace Variation
end Variation
end YM.CF.BProof.Cliff
