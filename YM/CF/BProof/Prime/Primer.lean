import YM.CF.BProof.Prime.Clock
/-! primer rooted trace log. Truncation price. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Prime
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
open Branch Tenant Air Veil
variable {α C:ℝ}{I:Type}[Fintype I](K:Core j a₁ b l r N)
structure Primer (N:Side)(I:Type)[Fintype I] (α C:ℝ) where
 rent: I→ Support (More N)
 tax: I→ℝ
 root: I→ Seat N
 ch(i):root i∈rent i
 Wt(i):Veil.Part (world N) (rent i) (tax i)
 toll:Moment.Toll rent tax (4*α) C
 breadth i: tax i≠0 → Micro.Loc (rent i)
-- Lean tune broad property.
variable (Q:Primer N I α C)
namespace Primer
abbrev func(i:I):= (Q.Wt i).val
def selected (Y:S.Setup L a (More N) d y) (k ξ:ℕ)(μ: Support (More N)) := Air.atFall Y k μ∧ μ.card≤ξ
def omitted (Y:S.Setup L a (More N) d y) (k ξ:ℕ)(μ: Support (More N)) := Air.atFall Y k μ∧ ξ<μ.card
def short := univ.filter fun i=> selected Y k ξ (Q.rent i)
abbrev term (x:Veil.World N)(i:I):=if omitted Y k ξ (Q.rent i) then Q.func i x else 0
abbrev brief (x:World N)(i:I):= if selected Y k ξ (Q.rent i) then Q.func i x else 0
def totalV (x:World N):= ∑ i, (if atFall Y k (Q.rent i) then Q.func i x else 0)
lemma total_p (x:World N): Q.totalV (Y:=Y) k x=(∑ i,Q.brief (Y:=Y) k ξ x i) +∑ i,Q.term (Y:=Y) k ξ x i:=by unfold term totalV brief selected omitted; rw [←sum_add_distrib]; refine sum_congr rfl fun i _=>?_ ; by_cases h: atFall Y k (Q.rent i); by_cases l:(Q.rent i).card≤ξ; simp only [h,l, not_lt.mpr l, true_and,ite_false,ite_true,add_zero]; simp [h,l,lt_of_not_ge l]; simp [h]
abbrev tail(i:I) := Air.Atmos (omitted Y k ξ) Q.rent Q.tax i
abbrev LongFee (x:Pouch Y P T θ)(i:I) := Q.term (Y:=Y) k ξ (Z.world1 P K x) i
@[fun_prop] lemma long_m(i:I): Measurable fun x:Pouch Y P T θ =>Q.LongFee P Z k ξ K x i:=by unfold LongFee term; split; exact (Q.Wt i).meas.comp (Z.tracks_W P K); exact measurable_const
abbrev expL(α:ℝ)(s:ℕ):=Real.exp (-(α*s))
variable (qα:0≤α)
include qα
lemma cargo : Moment.Toll Q.rent (Q.tail (Y:=Y) k ξ) (3*α) (expL α ξ*C):=by
 let θ:=expL α ξ; let E:= (Q.rent); let g:=Q.tax; let w:=Q.tail (Y:=Y) k ξ; have v(i):0≤w i:=(lim_toll _ E g Q.toll).nonneg i; refine ⟨v,fun i=>budget_mono (budget_scale (Real.exp_pos _).le (Q.toll.pays i)) (fun x=> ?_) ?_⟩
 · unfold Moment.hit; split; exact mul_nonneg (Real.exp_pos _).le (v _); exact le_rfl
 intro p; unfold Moment.hit; split; swap; · simp only [mul_zero]; exact le_rfl
 unfold tail Air.Atmos; split; rename_i H; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Q.toll.nonneg ..); unfold expL; rw [←Real.exp_add]; apply Real.exp_monotone; have he: (ξ:ℝ)≤(Q.rent p).card:=Nat.cast_le.mpr H.2.le; nlinarith
 rw [mul_zero]; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (Q.toll.nonneg ..))
variable (Lk: Clock Z k ξ)
include Lk
lemma chain : Scope.Chain Y P T θ rB k Z.μwage Q.rent (tail (Y:=Y) k ξ Q) (fun i t=> Q.LongFee P Z k ξ K t i) (expL α ξ*C) α:=by
 refine ⟨Q.cargo k ξ qα, fun i h=>?_, fun i x=>?_,long_m P Z k ξ K Q,fun i _ Λ p x y v=> ?_⟩
 · unfold tail Air.Atmos at h; split at h; rename_i v; refine ⟨Air.atFall_on k Lk.pos ⟨_, Q.ch i⟩ v.1 (Q.breadth i h), Q.breadth i h,Lk.height Z k ξ⟩; contradiction
 · unfold LongFee term tail Air.Atmos; split; exact (Q.Wt i).tag.pays _; rw [norm_zero]
 unfold LongFee term; split; exact (Q.Wt i).include_b (Z.recordW P K x y (Q.rent i) p v); exact rfl
end Primer
end YM.CF.BProof.Prime
