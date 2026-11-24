import YM.CF.BProof.Prime.Shelter
import YM.CF.BProof.Payment.Knot

/-! Outside phase words. assign to site-address over near radius. Magnitudes are
set_option autoImplicit false
 estimated but keep exact factors in measure assembly. cite B-lastQ. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Risk
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
variable (x' : Pod Y)
open Account
open Payment Garden Palot Oasis Scree Shelter
variable (B' : GramM N)
variable (o:Y.Block) (xw x'w:Pouch Y P T θ)
local notation "φf"=> Brick.Act.fields mH g₀
local notation "Hτ"=>B'.p.threshold
abbrev flash_ (V:Pod Y):= RG.flags B'.p.threshold (Seam.rawG Y P T θ V)
abbrev wound(i:Seat N)(x:Pod Y):ℂ:=star (glow ((φf x).1 i)) -- parentheses
lemma stars(i:Seat N): ‖wound (Y:=Y) i x‖=1:= by unfold wound; rw [norm_star,glow_p]
abbrev Tee(o:Y.Block)(x:Pod Y):= (flash_ P B' (Y:=Y) (T:=T) (θ:=θ) x).filter (fun i=>πX i=o)
def Loot(i:Seat N)(x:Pod Y):ℂ:=Complex.log (wound (Y:=Y) i x)
lemma earn (i:Seat N) : Complex.exp (Loot (Y:=Y) i x)=wound (Y:=Y) i x:= Complex.exp_log (norm_pos_iff.mp ((stars (Y:=Y) x i).symm ▸ zero_lt_one)) -- args order x
lemma earn_m (i:Seat N): Measurable (Loot (Y:=Y) i):=by
 let f:=fun x:Pod Y=> glow ((φf x).1 i); have ht:Measurable f:= glow.continuous.measurable.comp ((measurable_pi_apply i).comp (measurable_fst.comp (Brick.Act.fields_m ..)))
 exact Complex.measurable_log.comp (Complex.conjCLE.continuous.measurable.comp ht)
lemma flash_m (T:PathData G)(i:Seat N): MeasurableSet {x:Pod Y| i∈ flash_ P B' (T:=T) (θ:=θ) x}:= (raw_m ..) (flags_open i Hτ).measurableSet
abbrev settle_Z (b:Y.Block)(x:Pouch Y P T θ) := ∑ i∈ Tee P B' (T:=T) (θ:=θ) b x.val,Loot (Y:=Y) i x.val -- tune implicit
lemma reput : (settle_Z P B' o xw).re=0:=by unfold settle_Z Loot; rw [Complex.re_sum,sum_eq_zero]; intro i _; rw [Complex.log_re,stars,Real.log_one]
variable (xη:thresh y≤ B'.p.threshold) (h: Clock Z k ξ)
include Z xη
lemma seeing (i:Seat N)(p:i∈ flash_ P B' (Y:=Y) (T:=T) (θ:=θ) xw.val): Y.yard.Gap (Trek.tag mH i) (time i) ∧ πX i∈ nearL Y xw.val:=by
 obtain ⟨t,l⟩:= Rhythm.Lease.flag_here P Y T θ (tool Y xw.val) Z.lineT.raw Z.lineT.ok xw.property E.H Δ.clock Z.stageU.podium xη _ p; exact ⟨t,(Cabinet.nearer Y _ _ (Subset.refl (sick Y xw.val)) (by decide : 1≤hNear) ((Seam.nearhood Y).1 l))⟩
lemma occupation (i:Seat N)(p:πX i=o) (A:Cores Y rB)(t:A∈ recital Y rB xw.val) (u:Spiced Y (plate Y rB A) xw.val x'w.val)(v:o∈(Near Y rB).locations A xw.val)(g:i∈flash_ P B' (T:=T) (θ:=θ) xw.val): i∈ flash_ P B' (T:=T) (θ:=θ) x'w.val:=by
 let S:= Planet Y A.val (Seam.dome E.H Δ.clock) 40; have he:Agrees (↑(Lattice.halo 8 S)) (rawK xw.val) (rawK x'w.val):= pane_raw Y P T θ xw.val A x'w.val xw.property x'w.property Z.stageU u; have ht:S∩flash_ P B' (T:=T) (θ:=θ) xw.val=S∩flash_ P B' (T:=T) (θ:=θ) x'w.val:= RG.flags_agree _ _ _ _ (agrees_mono he (Finset.coe_subset.mpr (Micro.inspected_sub _)))
 have hp:i∈S:= (zone_mem ..).2 ⟨Y.yard.outside_gap _ _ _ (seeing P Z B' xw xη i g).1,?_⟩ -- arg order notations
 · exact (mem_inter.mp (show i∈S∩flash_ P B' (T:=T) (θ:=θ) x'w.val from ht ▸ (mem_inter.mpr ⟨hp,g⟩))).2
 rw [p]; exact Cabinet.nearer Y _ _ (inter_subset_right (s₁:=sick Y xw.val)) (by decide : hNear≤40) v
lemma ticket_Z : Shelter.Ticket P (Shelter.Near Y rB) (settle_Z (T:=T) (θ:=θ) P B') :=by
 constructor
 · intro i; change Measurable (fun x:Pouch Y P T θ=> settle_Z P B' i x); unfold settle_Z Tee;
   let K:= flash_ P B' (T:=T) (θ:=θ) (Y:=Y); have he:Measurable K:=by apply measurable_to_countable'; intro u; exact raw_m Y P T θ (RG.flags_measurable_eq B'.p.threshold u)
   exact Trek.meal (he.comp measurable_subtype_coe) (fun F (x:Pouch Y P T θ)=> ∑ j∈F.filter (fun j=>πX j=i),Loot (Y:=Y) j x.val) (fun F=>Finset.measurable_sum _ fun j _=>(earn_m (Y:=Y) j).comp measurable_subtype_coe)
 intro X x y k t u b p; have hv:b∈(Near Y rB).locations X y.val:= (Near Y rB).visible X x.val y.val u ▸ p; let V:=Tee P B' (Y:=Y) (T:=T) (θ:=θ); unfold settle_Z; apply sum_congr (s₁:=V b x.val) (s₂:=V b y.val) ?_ ?_
 · ext i; simp only [V,Tee, mem_filter]; apply and_congr_left; intro c; exact ⟨fun e=> occupation P Z B' b x y xη i c X k u p e,fun e=> occupation P Z B' b y x xη i c X t (fun i l=>(u i l).symm) hv e⟩
 intro i h; -- membership in second only
 have hx: addr mH g₀ i=b:= (mem_filter.mp h).2; unfold Loot wound; rw [Brick.Act.phase_y mH g₀ i (hx.symm ▸ crown_put Y x.val rB X Z.stageU.premium b p) u] -- tune
lemma flash_ball : (ticket_Z P Z B' xη).versionT.amt xw.val= ∑ i∈flash_ P B' (T:=T) (θ:=θ) xw.val,Loot (Y:=Y) i xw.val := by
 rw [(ticket_Z P Z B' xη).issues xw.val (nearL Y xw.val) (crown_all Y xw.val rB Z.stageU.premium).symm (crown_unique Y xw.val rB Z.stageU.premium) xw.property]; exact sum_fiberwise_of_maps_to (fun i g=> (seeing P Z B' xw xη i g).2) _ -- tune args
lemma touched_Z : (ticket_Z P Z B' xη).versionT.Income (fun _ _=>0):=by
 intro x i v p; apply le_trans ((ticket_Z P Z B' xη).version_income 0 (fun x i h u g=> _root_.le_of_eq (reput P B' u x)) x i v p); simp
lemma flash_cost : Complex.exp ((ticket_Z P Z B' xη).versionT.amt xw.val)=outFuel B' (F_' Y P T θ xw.val) (φf xw.val).1:=by
 rw [flash_ball P Z B' xw xη,Complex.exp_sum]; unfold outFuel style; rw [star_prod]; exact Finset.prod_congr rfl fun i _=> earn (Y:=Y) xw.val i -- tune star_prod name
end YM.CF.BProof.Risk
