import YM.CF.BProof.Prime.Flash
/- Accounting near gain parameter φ. -/
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
variable (Q:Primer N I α C)
local notation "Ψ"=> Pouch Y P T θ
local notation "ψx"=>Z.world1 P K
local notation "ψ0"=>Z.world0 P K
variable (x' : Pod Y)
open Account
variable (Y) {q:ℕ}
lemma funds_ray (m k:ℕ){b:House.Block Y.yard Y.c'} (X:Cores Y rB) (v:b∈ Cabinet.halo Y X.val m)(h:k+m≤rB) : ray mH b k ⊆ plate Y rB X:=by
 intro i p; obtain ⟨j,v,b⟩:= (Cabinet.halo_m ..).1 v; exact Seam.ray_plate Y ((Cabinet.halo_m ..).2 ⟨j,v,ray_net Y _ _ b p⟩) (by omega)
lemma close_near {Λ:Finset (House.Block Y.yard Y.c')}(x x':Pod Y){b:House.Block Y.yard Y.c'}(v:Spiced Y Λ x x')(p: ray mH b k⊆Λ) : b∈Cabinet.halo Y (Cabinet.sick Y x) k ↔ b∈Cabinet.halo Y (Cabinet.sick Y x') k:=by
 rw [Cabinet.halo_spec,Cabinet.halo_spec]; refine exists_congr fun a=> and_congr_left fun k=> ?_; exact Brick.Act.sick_id mH g₀ y v _ (p k)
lemma priceRay {v:ℝ}(h:0≤v): Moment.Toll (fun b:Y.Block=> House.ray mH b k) (fun _=>v) 4 (fourBill k*Real.exp (4* fourBill k)*v):=by
 let X(b:Y.Block):=House.ray mH b k; let J:= fun _ : Y.Block=>v; let P(y):=Moment.hit X J 4 y; have hu(y:House.Block Y.yard Y.c')(i:Y.Block):0 ≤ P y i:=by unfold P Moment.hit J; split; positivity; exact le_rfl
 refine ⟨fun _=>h,fun i=>budget_finite (hu i) ?_⟩; let V:= X i; let L:= Real.exp (4*fourBill k)*v; change ∑ b, P i b≤_; rw [mul_assoc]; rw [←Finset.sum_subset (f:=P i) (subset_univ V)]; swap; · intro b _ v; unfold P Moment.hit; exact if_neg (fun l=> v ((ray_flip Y k).1 l))
 apply (sum_le_sum (g:=fun _=>L) (fun b h=> ?_)).trans; rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ (show 0≤L by unfold L; positivity); exact Nat.cast_le.mpr (House.ray_pay ..); unfold P Moment.hit; rw [if_pos ((ray_flip ..).1 (show b∈ V from h))]; unfold L; change _*v ≤ _*v; gcongr; exact House.ray_pay .. -- h shadow
lemma center_m (o:Y.Block): Measurable fun x=> central Y x o:=by
 unfold Cabinet.central; -- label tag
 change Measurable (fun x:Pod Y=>stampY Y x (cartL Y o)); unfold stampY Brick.Act.tag; fun_prop -- tune
lemma halo_lic{k:ℕ}{o:Y.Block}:MeasurableSet {x:Pod Y| o∈ Cabinet.halo Y (Cabinet.sick Y x) k}:= (sick_m Y) (Set.Countable.measurableSet (Set.to_countable {t:Finset Y.Block|o∈ Cabinet.halo Y t k}))
namespace Primer
variable {Y} {ρ σ:ℝ}(Lk:Clock Z k ξ)(t:Q.Guard P Z k ξ K ρ σ)
variable (o:House.Block Y.yard Y.c')
def liveC(x:Pouch Y P T θ) := Q.atBook k ξ (ψ0 (central Y x.val o)) o-Q.atBook k ξ (ψ0 0) o
def pastC(x:Pouch Y P T θ):= Q.atBook k ξ (ψx x) o-Q.atBook k ξ (ψ0 0) o
local notation "Kξ" => price_short Y.yard.short k ξ Y.g.count.val C
local notation "CΨ"=> Q.correctedF P Z k ξ K
@[fun_prop] lemma term_m : Measurable fun x:Pouch Y P T θ=> Q.atBook k ξ (ψx x) o:= (Q.book_m k ξ o).comp (Z.tracks_W P K)
@[fun_prop] lemma Term_m : Measurable fun x:Pouch Y P T θ=> Q.atBook k ξ (ψ0 (central Y x.val o)) o:= (measurable_of_countable (f:=fun z=> Q.atBook k ξ (ψ0 z) o)).comp ((center_m ..).comp measurable_subtype_coe)
@[fun_prop] lemma live_m : Measurable (Q.liveC P Z k ξ K o):= (Q.Term_m P Z k ξ K o).sub measurable_const
@[fun_prop] lemma past_m : Measurable (Q.pastC P Z k ξ K o):= (Q.term_m P Z k ξ K o).sub measurable_const
@[fun_prop] lemma corrected_m : Measurable fun x=> Q.correctedF P Z k ξ K x o :=Measurable.ite (measurable_subtype_coe (halo_lic ..)) measurable_const ((Q.term_m P Z k ξ K o).sub (Q.Term_m P Z k ξ K o)) -- tune _ instance k nearL defin
variable (uw:Pouch Y P T θ)
include Lk t
lemma past_cap : (Q.pastC P Z k ξ K o uw).re≤ 2*Kξ:= by
 apply (Complex.re_le_norm _).trans; apply (norm_sub_le ..).trans; simpa only [two_mul] using (add_le_add (Q.amount Z k ξ o t.ok Lk (ψx uw)) (Q.amount Z k ξ o t.ok Lk (ψ0 0))) -- syntax
lemma live_cap (p: central Y uw.val o ≠ 0): (Q.liveC P Z k ξ K o uw).re≤-σ:= t.bill _ p _
lemma corrected_pay :‖CΨ uw o‖≤ ρ*Kξ := by unfold correctedF; split; rw [norm_zero]; exact mul_nonneg t.pos (mul_nonneg (Nat.cast_nonneg _) Q.C_pos); rename_i v; exact Q.book_bill P Z k ξ K o uw t Lk v -- tune order
omit t
lemma corrected_eq (u u':Pouch Y P T θ)(Φ:Esp Y rB (ray mH o 32) u.val u'.val): CΨ u o=CΨ u' o:=by
 have ht:=esp_here Y u.val u'.val rB Φ; unfold correctedF; by_cases h:o∈ nearL Y u.val; all_goals have hp:o∈ nearL Y u.val ↔ o∈nearL Y u'.val:= close_near Y hNear _ _ ht (House.ray_in mH 32 (by decide : hNear≤32)) -- tune order
 · rw [if_pos h,if_pos (hp.mp h)];
 rw [if_neg h,if_neg (fun t=> h (hp.mpr t))]; unfold relB; rw [Q.book_pose P Z k ξ K o u u' Lk Φ,cent_eq Y u.val u'.val o (House.ray_home ..) ht]
def adjusted (x:Pouch Y P T θ) := ∑ i:Y.Block, CΨ x i
include t
abbrev WgR (U:ℝ) := fourBill 32*Real.exp (4*fourBill 32) * U
lemma revenue: Nonempty (Account.Teller (gridBase wB) (Cabinet.Ready P Y T θ) (Esp Y rB) Y.Block (Total Y P T θ (Q.adjusted P Z k ξ K)) 4 (WgR (ρ * Kξ))) :=by
 let YF(i:House.Block Y.yard Y.c')(x:Pouch Y P T θ):= Q.correctedF P Z k ξ K x i; let G_(i:Y.Block):= Total Y P T θ (YF i); let V(i:Y.Block):=House.ray mH i 32
 refine ⟨ V,(fun _=>ρ *Kξ), G_, fun x p=>?_, priceRay Y 32 (mul_nonneg t.pos (mul_nonneg (by positivity) Q.C_pos)),fun i x p=> ?_, fun i=>⟨⟨i,ray_home ..⟩,ray_n mH _ 32⟩,fun i=> Total_m Y P T θ _ (Q.corrected_m P Z k ξ K i),fun b x y g t u=>?_⟩ -- p shadow
 · unfold Scope.Total adjusted G_; simp only [Scope.Total,dif_pos p,YF]
 · unfold G_ YF Scope.Total; rw [dif_pos p]; exact corrected_pay P Z k ξ K Q Lk t i ⟨x,p⟩ -- tune order
 unfold G_ Scope.Total; rw [dif_pos t,dif_pos u]; exact corrected_eq P Z k ξ K Q Lk b ⟨x,t⟩ ⟨y,u⟩ g -- tune
end Primer
end YM.CF.BProof.Prime
