import YM.CF.BProof.Prime.Primer
import YM.CF.BProof.Cabinet.Pour

/- Assign stockBook and short-read Arg. Primary terms at all shared scales. -/
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
namespace Primer
variable {μ:Support (More N)}
variable (w0:House.Block Y.yard Y.c')
abbrev smallSet := short (Y:=Y) k ξ Q
lemma small_t(i:I): i∈ (smallSet (Y:=Y) k ξ Q)↔ selected Y k ξ (Q.rent i):=by simp [smallSet,short] -- membership
variable (Y)
def entry (b:House.Block Y.yard Y.c') := (short (Y:=Y) k ξ Q).filter (fun i=> πX (Q.root i)=b)
lemma claim_H {i:I}: i∈ entry Y k ξ Q w0 ↔ selected Y k ξ (Q.rent i) ∧ addr mH g₀ (Q.root i)=w0:=by rw [entry,mem_filter,show (i∈_) ↔ _ from small_t (Y:=Y) k ξ Q i]; -- tune
variable {Y}
lemma clear_scope {i:I}(p: i∈ entry Y k ξ Q w0) (d: Q.tax i ≠0) (h:Clock Z k ξ) : Probe Y P T θ (ray mH w0 32) (Lattice.halo μz (Q.rent i)):=by obtain ⟨v,z⟩:= (claim_H ..).1 p; exact h.licenses P Z k ξ (Q.breadth i d) (Q.ch i) v.1 v.2 _ (by change House.ray _ _ _⊆_; rw [← z]; exact ray_in mH _ (by decide : 9≤32)) -- tune licenses arguments

def atBook(x:World N)(b:House.Block Y.yard Y.c') := ∑ i∈ entry Y k ξ Q b,Q.func i x
@[fun_prop] lemma book_m : Measurable (fun x:World N=> Q.atBook k ξ x w0):= Finset.measurable_sum _ fun i _=> (Q.Wt i).meas -- partial inferred Y
abbrev price_short(d k ξ t:ℕ)(C:ℝ):ℝ:= ((House.root_port d (k+ξ) t:ℕ):ℝ)*C
section
variable (p:0≤α)
local notation "Kξ"=> price_short Y.yard.short k ξ Y.g.count.val C
include Q
lemma C_pos:0≤C:= budget_nonneg (Q.toll.pays 0) -- tune quota
include p
lemma tax_pay (h: Clock Z k ξ):∑ i∈entry Y k ξ Q w0,Q.tax i ≤ (Bias.CircleR g₀ mH w0 (k+ξ)).card * C:=by
 let R:= Bias.CircleR g₀ mH w0 (k+ξ); let A:= Q.tax; let hit(k):= Moment.hit Q.rent A (4*α) k; apply le_trans (b:=∑ i∈entry Y k ξ Q w0, ∑ j∈ R,hit j i); apply sum_le_sum; intro i l; have hu(z: Seat N):0 ≤ hit z i:= (Q.toll.pays z).1 i; by_cases v:A i=0; change A i ≤_; rw [v]; apply sum_nonneg; exact fun j _=>hu j
 obtain ⟨b,k'⟩:= (claim_H ..).1 l; refine le_trans (b:=hit (Q.root i) i) ?_ (single_le_sum (f:=fun k=>hit k i) (fun j _=>hu j) (mem_filter.mpr ⟨mem_univ _,k',h.anchor Z k ξ (Q.breadth i v) (Q.ch i) b.1 b.2⟩))
 unfold hit Moment.hit A; rw [if_pos (Q.ch i)]; exact le_mul_of_one_le_left (Q.toll.nonneg i) (Real.one_le_exp (by positivity))
 rw [sum_comm]; refine le_trans (sum_le_sum fun j _=> budget_sum (Q.toll.pays j) (entry Y k ξ Q w0)) (by simp [R])
lemma earn (h:Clock Z k ξ) : ∑ i∈ entry Y k ξ Q w0,Q.tax i ≤price_short Y.yard.short k ξ Y.g.count.val C:=by
 apply (tax_pay Z k ξ Q w0 p h).trans; apply mul_le_mul_of_nonneg_right _ Q.C_pos; apply Nat.cast_le.mpr; exact Bias.circle_card Y.g mH w0 (k+ξ) (h.commuter Z k ξ _ (by unfold TimePlus; omega))
lemma amount (h: Clock Z k ξ)(x:World N): ‖Q.atBook k ξ x w0‖ ≤Kξ:= (norm_sum_le ..).trans ((sum_le_sum (fun i _=> (Q.Wt i).cost x)).trans (earn Z k ξ Q w0 p h))
end
-- local Pose proof
variable (xw x'w:Pouch Y P T θ)
lemma book_pose (h:Clock Z k ξ)(p:Esp Y rB (ray mH w0 32) xw.val x'w.val): Q.atBook k ξ (ψx xw) w0=Q.atBook k ξ (ψx x'w) w0:=by
 apply sum_congr rfl; intro i v; by_cases d:Q.tax i=0; · unfold func; rw [(Q.Wt i).zero d]
 exact (Q.Wt i).include_b (Z.recordW P K xw x'w (Q.rent i) (Q.clear_scope P Z k ξ w0 v d h) p)
-- budgets: reference sigma, variation; weak correction only on p not near. Need existence proof later. 
local notation "Kξ"=> price_short Y.yard.short k ξ Y.g.count.val C
variable (ρ σ:ℝ)
local notation "hot_"=> Air.atFall Y k
local notation "z_t"=> central Y
abbrev tNear := nearL Y
abbrev Varies (w0:House.Block Y.yard Y.c')(x: Pouch Y P T θ)(i:I)(z:Fin 5):Prop:= ‖Q.func i (Z.world1 P K x)-Q.func i (ψ0 z)‖ ≤ ρ*Q.tax i -- w0 unused
structure Guard (ρ σ:ℝ) : Prop where
 ok: 0≤α
 pos:0≤ρ
 varies (w0:House.Block Y.yard Y.c')(x:Pouch Y P T θ)(p:w0∉ nearL Y x.val) (i:I)(v:i∈ entry Y k ξ Q w0)(q:Q.tax i≠0): Varies P Z K Q ρ w0 x i (central Y x.val w0)
 bill(k':Fin 5)(p:k'≠0)(w':House.Block Y.yard Y.c'): (Q.atBook k ξ (Z.world0 P K k') w'-Q.atBook k ξ (Z.world0 P K 0) w').re ≤ -σ
-- choose after Shape compare; σ positive eventually.
abbrev relB(xw:Pouch Y P T θ) := Q.atBook k ξ (ψx xw) w0-Q.atBook k ξ (ψ0 (central Y xw.val w0)) w0
def correctedF(x:Pouch Y P T θ)(b:House.Block Y.yard Y.c') := if b∈ nearL Y x.val then (0:ℂ) else Q.relB P Z k ξ K b x
variable {ρ σ} (Ub: Q.Guard P Z k ξ K ρ σ) -- tune arg order
include Ub
lemma book_bill (h:Clock Z k ξ)(p:w0∉ nearL Y xw.val): ‖Q.relB P Z k ξ K w0 xw‖≤ ρ*Kξ:=by
 let S:= entry Y k ξ Q w0; let x:= xw; set g:=ρ -- tune remove
 unfold relB atBook; rw [←sum_sub_distrib]; apply (norm_sum_le ..).trans; apply le_trans (b:=∑ i ∈ entry Y k ξ Q w0,ρ* Q.tax i) _; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (earn Z k ξ Q w0 Ub.ok h) Ub.pos
 apply sum_le_sum; intro i l; by_cases p':Q.tax i=0; simp only [func,(Q.Wt i).zero p',sub_self,norm_zero,p',mul_zero,le_refl]; exact Ub.varies w0 xw p i l p'
end Primer
end YM.CF.BProof.Prime
