import YM.CF.BProof.Prime.Shelter

/- Final amount of B-Fstock log. before calendar. -/
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
open Shelter
namespace Primer
variable (Ck:Clock Z k ξ)
include Ck
local notation "νμ"=>Near Y rB
local notation "νξ"=> Far Y rB
lemma economics : Shelter.Ticket (P:=P) (Near Y rB) (fun b=> Q.pastC P Z k ξ K b):=by
 constructor; exact Q.past_m P Z k ξ K
 intro X x y v t p b g; let h:= approved Y x.val rB X Z.stageU.premium v (show b∈ (Near Y rB).locations X x.val from g); exact congrArg (fun c=>c-Q.atBook k ξ (ψ0 0) b) (Q.book_pose P Z k ξ K b x y Ck (esp_stay Y y.val rB X v t h p)) -- notation hygiene
lemma heroics:Shelter.Ticket (P:=P) (Far Y rB) (fun b=> Q.liveC P Z k ξ K b):=by
 constructor; exact Q.live_m P Z k ξ K
 intro i x y v t p b g; have hp:= cent_eq Y x.val y.val b ((plan wB rB).sub i (Finset.mem_sdiff.mp (show b∈ Shelter.paid Y x.val rB i from g)).1) p; unfold liveC; rw [hp]
local notation "κΩ"=> price_short Y.yard.short k ξ Y.g.count.val C
local notation "minx"=> nearL Y
local notation "χΩ"=> Q.pastC P Z k ξ K
local notation "ξΩ"=> Q.liveC P Z k ξ K
local notation "γΩ"=> Q.correctedF P Z k ξ K
variable {ρ σ:ℝ}(W:Guard P Z k ξ K Q ρ σ)
abbrev Winter := (Q.economics P Z k ξ K Ck).versionT
abbrev Watch := (Q.heroics P Z k ξ K Ck).versionT
include W
lemma incomes_n : (Q.Winter P Z k ξ K Ck).Income (fun X x=> ((Shelter.crown Y x rB X).card:ℝ)*(2*κΩ)):= Shelter.Ticket.version_income (Q.economics P Z k ξ K Ck) (2*κΩ) (fun x _ _ b _=> Q.past_cap P Z k ξ K Ck W b x)
lemma incomes_f : (Q.Watch P Z k ξ K Ck).Income (fun X x=> ((Shelter.paid Y x rB X).card:ℝ)*(-σ)):=by
 apply Shelter.Ticket.version_income (Q.heroics P Z k ξ K Ck) (-σ); intro x i v b hb; apply Q.live_cap P Z k ξ K Ck W; have hz:= Finset.mem_sdiff.mp (Eq.subst (motive:=fun D=>b∈D) (paid_prop Y x.val rB i Z.stageU.premium v) (show b∈ Shelter.paid Y x.val rB i from hb)) -- tune
 exact (central_busy P Y T θ x.val b Z.lineT.raw Z.lineT.ok x.property hz.2).1 (excited Y rB i v hz.1)
lemma revenueX : ((Q.Winter P Z k ξ K Ck).add (Q.Watch P Z k ξ K Ck)).Income (fun X x=> (Mint.grey Y rB X x).card*(fourBill hNear*(2*κΩ))+(Mint.paid Y rB X x).card*(-σ)):=by
 let U:= Q.incomes_n P Z k ξ K Ck W; let V:= Q.incomes_f P Z k ξ K Ck W; intro x i v p; change ((Q.Winter P Z k ξ K Ck).F i x).re + ((Q.Watch P Z k ξ K Ck).F i x).re≤_ -- tune
 refine le_trans (add_le_add (U x i v p) (V x i v p)) ?_; apply add_le_add _ (le_of_eq rfl); change (↑(Shelter.crown Y x rB i).card:ℝ)*(2*κΩ)≤_; rw [←mul_assoc _ _ (2*κΩ)]; apply mul_le_mul_of_nonneg_right _ (mul_nonneg zero_le_two (mul_nonneg (by positivity) Q.C_pos)); exact_mod_cast Cabinet.halo_size Y (A:=fault Y rB x i) hNear -- tune x arg
omit W
lemma winter_stock(x:Pouch Y P T θ): (Q.Winter P Z k ξ K Ck).amt x.val=∑ i∈ minx x.val,χΩ i x:=by apply (Q.economics P Z k ξ K Ck).issues x.val (minx x.val) (crown_all Y x.val rB Z.stageU.premium).symm (crown_unique Y x.val rB Z.stageU.premium) x.property
lemma watch_out(x:Pouch Y P T θ): (Q.Watch P Z k ξ K Ck).amt x.val=∑ i∈ bitL Y x.val \ minx x.val, ξΩ i x := (Q.heroics P Z k ξ K Ck).issues x.val _ (paid_all Y x.val rB Z.stageU.premium).symm (ring_unique Y x.val rB Z.stageU.premium) x.property
lemma watch_more(x:Pouch Y P T θ) : (Q.Watch P Z k ξ K Ck).amt x.val=∑ i∈ (minx x.val)ᶜ,ξΩ i x:=by
 rw [Q.watch_out P Z k ξ K Ck]; apply Finset.sum_subset; intro i b; exact mem_compl.mpr (Finset.mem_sdiff.mp b).2
 intro b a u; unfold liveC; have ht:b∉bitL Y x.val:= fun l=>u (Finset.mem_sdiff.mpr ⟨l,mem_compl.mp a⟩); rw [show central Y x.val b=0 from not_not.mp ((central_busy P Y T θ x.val b Z.lineT.raw Z.lineT.ok x.property (mem_compl.mp a)).not.mp ht),sub_self] -- tune aura
omit Ck
def capital:= ∑ i:Y.Block,Q.atBook k ξ (Z.world0 P K 0) i
lemma tide (z:World N): ∑ i,Q.brief (Y:=Y) k ξ z i=∑ i:Y.Block,Q.atBook k ξ z i:=by
 unfold brief; rw [←sum_filter]; change ∑ i∈ short (Y:=Y) k ξ Q,Q.func i z=_; symm; exact sum_fiberwise_of_maps_to (t:=univ) (fun (_ : I) _=> Finset.mem_univ _) _ -- tune
lemma buy(α':0≤α) : ‖Q.capital P Z k ξ K‖ ≤ (Fintype.card (Seat N):ℝ)* C:=by
 unfold capital; rw [← Q.tide (Y:=Y)]; unfold brief; rw [←sum_filter]; refine (norm_sum_le ..).trans ((sum_le_sum (fun i _=>(Q.Wt i).tag.pays _)).trans (budget_sum (Q.toll.total _ _ (by positivity) (fun i=> ⟨_,Q.ch i⟩)) _)) -- tune
include Ck
lemma shares (x:Pouch Y P T θ): (∑ i,Q.brief (Y:=Y) k ξ (ψx x) i)= Q.capital P Z k ξ K + Q.adjusted P Z k ξ K x + ((Q.Winter P Z k ξ K Ck).add (Q.Watch P Z k ξ K Ck)).amt x.val:=by
 rw [Q.tide (Y:=Y), Shift.amt_add, Q.winter_stock P Z k ξ K Ck,Q.watch_more P Z k ξ K Ck]; let C:= minx x.val
 unfold capital adjusted; rw [add_assoc,← sub_eq_iff_eq_add',←sum_sub_distrib]; have he: (∑ i:Y.Block,Q.correctedF P Z k ξ K x i)=∑ i∈ (Cᶜ),γΩ x i:= by
    symm; apply Finset.sum_subset (subset_univ _); intros b u v; exact if_pos (not_not.mp (fun h=>v (mem_compl.mpr h)))
 rw [he,show (∑ i:Y.Block,(Q.atBook k ξ (ψx x) i - Q.atBook k ξ (ψ0 0) i))=∑ i,χΩ i x from rfl,← sum_add_sum_compl C (fun i=>χΩ i x),add_left_comm (_:ℂ)]; apply congrArg (fun z:ℂ=> _+z); rw [←sum_add_distrib]; apply sum_congr rfl; intro i v; unfold correctedF relB liveC pastC; rw [if_neg (mem_compl.mp v)]; ring -- tune
end Primer
end YM.CF.BProof.Prime
