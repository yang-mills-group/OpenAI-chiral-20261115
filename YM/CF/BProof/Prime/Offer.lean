import YM.CF.BProof.Prime.Gold
/-! B-Qbias from exact roots and approximation (omitting long pay). -/
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
open Air
namespace Primer
variable {σ:ℝ} (Ck:Clock Z k ξ) (o:House.Block Y.yard Y.c')
def diff_(z:Fin 5)(i:I):ℝ:= (Q.func i (ψ0 z)).re-(Q.func i (ψ0 0)).re
abbrev err := diff_ P Z K Q
abbrev Roots(i:Seat N) := univ.filter (fun z:I=> Q.root z=i)
abbrev bias_(z:Fin 5):= Tape.bias (Z.hom P K z) -- tune Reel name
variable (z:Fin 5) (t:0≤α)
structure MoneyZ : Prop where
 all(i:Seat N): (∑ j∈ Q.Roots i,Q.diff_ P Z K z j)= (Tape.bias (Z.hom P K z) i)
 stop(i:I)(t:¬atFall Y k (Q.rent i)): Q.diff_ P Z K z i=0 -- blob proof
variable (q:Q.MoneyZ P Z k K z)
local notation "ζ_"=> Q.diff_ P Z K z
local notation "Π_"=> bias_ P Z K
lemma diff_p(i:I) : ‖Q.diff_ P Z K z i‖ ≤ 2*Q.tax i:=by apply (norm_sub_le ..).trans; exact ((add_le_add ((Complex.abs_re_le_norm _).trans ((Q.Wt i).cost _)) ((Complex.abs_re_le_norm _).trans ((Q.Wt i).cost _))).trans_eq (two_mul _).symm)
def truncated(i:Seat N):= (Q.Roots i).filter fun a=>selected Y k ξ (Q.rent a)
lemma full (i:Seat N) : (truncated (Y:=Y) k ξ Q i)⊆ (Q.Roots i):= filter_subset ..
-- bound with nonpositive preferred direction
include t q
lemma tail_bill(i:Seat N): (∑ j∈Q.truncated (Y:=Y) k ξ i, ζ_ j)≤ Π_ z i +2*(expL α ξ*C) := by
 let C₀:= expL α ξ*C; let U:= Q.truncated (Y:=Y) k ξ i; let X:= Q.Roots i; let A:= X\ U; let D:= diff_ P Z K Q z; let fee:= Q.tail (Y:=Y) k ξ; let T':= Q.cargo (Y:=Y) k ξ t
 have ht:(∑ j∈ A,D j)≥ -(2*C₀):=by
    rw [ge_iff_le, neg_le]; -- tune neg_le
    rw [←sum_neg_distrib]; -- possibly direction? inspect
    -- placeholders
    apply le_trans (b:=∑ j∈ A,2*Moment.hit Q.rent fee (3*α) i j)
    · apply sum_le_sum; intro a v; obtain ⟨g,h⟩:= mem_sdiff.mp v; have he:Q.root a=i:= (mem_filter.mp g).2; have hp:i∈Q.rent a:=he ▸ Q.ch _; by_cases h:omitted Y k ξ (Q.rent a)
      · have hx: fee a=Q.tax a:= if_pos h; unfold Moment.hit; rw [if_pos hp,hx]; apply le_trans (b:=2*Q.tax a) ((neg_le_abs _).trans (Q.diff_p P Z K z _)); refine mul_le_mul_of_nonneg_left ?_ zero_le_two; exact le_mul_of_one_le_left (Q.toll.nonneg a) (Real.one_le_exp (by positivity))
      have ha:¬ atFall Y k (Q.rent a):=by intro w; by_cases p:(Q.rent a).card≤ξ; exact (Finset.mem_sdiff.mp v).2 (mem_filter.mpr ⟨g,w,p⟩); exact h ⟨w,lt_of_not_ge p⟩
      rw [show D a=0 from q.stop a ha,neg_zero]; exact mul_nonneg zero_le_two ((T'.pays i).1 a)
    rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (budget_sum (T'.pays i) A) zero_le_two
 have hv:(∑ j∈ A,D j)+(∑ j∈ U,D j)= Π_ z i:=(sum_sdiff (Q.full (Y:=Y) k ξ i)).trans (q.all _)
 change (∑ j∈ U,D j)≤ _+2*C₀; rw [← hv]; linarith
omit t q
lemma fitsD : (Q.atBook k ξ (ψ0 z) o-Q.atBook k ξ (ψ0 0) o).re=(∑ i∈ entry Y k ξ Q o,ζ_ i):=by unfold diff_ atBook; rw [←sum_sub_distrib, Complex.re_sum]; exact rfl
local notation "D_" => Bias.CircleR g₀ mH o (k+ξ)
local notation "Σβ"=> Bias.CircleR g₀ mH o k
lemma contribution (i:I) (t:i∈ entry Y k ξ Q o)(h:ζ_ i≠0)(Ck:Clock Z k ξ): Q.root i∈D_:=by
 have hv:Q.tax i≠0:=by intro p; apply h; unfold diff_ func; rw [(Q.Wt i).zero p]; exact sub_self _
 obtain ⟨l,k'⟩:=(Q.claim_H ..).1 t; exact mem_filter.mpr ⟨mem_univ _,k', Ck.anchor Z k ξ (Q.breadth i hv) (Q.ch i) l.1 l.2⟩
lemma factors (Ck:Clock Z k ξ): (∑ t∈ entry Y k ξ Q o,ζ_ t)=∑ t∈ D_,∑ i∈Q.truncated (Y:=Y) k ξ t,ζ_ i:=by
 let R:=fun i:Seat N=>truncated (Y:=Y) k ξ Q i; let X:=(D_).biUnion R; have hp:X⊆ entry Y k ξ Q o:=by intro i h; obtain ⟨a,u,v⟩:= mem_biUnion.mp h; obtain ⟨l,g⟩:=mem_filter.mp v; exact (Q.claim_H ..).2 ⟨g,(congrArg (addr mH g₀) ((mem_filter.mp l).2)).trans (mem_filter.mp u).2.1⟩
 have he:Set.PairwiseDisjoint (↑D_) R:=fun i p j q e=> disjoint_left.mpr (fun k l z=> e (((mem_filter.mp ((mem_filter.mp l).1)).2).symm.trans ((mem_filter.mp ((mem_filter.mp z).1)).2))) -- tune
 symm; rw [← Finset.sum_biUnion he]; refine Finset.sum_subset hp (fun i l h=> ?_); by_contra v; exact h (mem_biUnion.mpr ⟨Q.root i,contribution P Z k ξ K Q o z _ l v Ck,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩, ((Q.claim_H ..).1 l).1⟩⟩)
lemma circle_up : Σβ ⊆ D_:=by intro i v; obtain ⟨a,j,h⟩:= (mem_filter.mp v).2; exact mem_filter.mpr ⟨mem_univ _,a,j,Y.yard.vic_nearer j _ _ _ (by omega) h⟩ -- parser "D_."
include q Ck t
-- bound payment by truncated book.read
variable {cβ:ℝ}
lemma aperture (e: (∑ i∈Σβ,Π_ z i) ≤ -cβ/64*(Y.g.count.val:ℝ)^3)(h: σ+(House.root_port Y.yard.short (k+ξ) Y.g.count.val)*(2*(expL α ξ*C)) ≤ cβ/64*(Y.g.count.val:ℝ)^3) : (Q.atBook k ξ (ψ0 z) o-Q.atBook k ξ (ψ0 0) o).re ≤ -σ:=by
 rw [Q.fitsD P Z k ξ K o z, factors P Z k ξ K Q o z Ck]; apply (sum_le_sum (fun i _=> Q.tail_bill P Z k ξ K z t q i)).trans; rw [sum_add_distrib,sum_const,nsmul_eq_mul]; have he:(∑ i∈D_,Π_ z i)≤ -cβ/64 * (Y.g.count.val:ℝ)^3:=by rw [←sum_sdiff (circle_up (Y:=Y) k ξ o)]; exact (add_le_of_nonpos_left (sum_nonpos (fun i _=> Bias.bias_nonpos _ _ _ (Z.hom P K z) _))).trans e -- tune
 let d:=2*(expL α ξ*C); have hd: 0≤d:= mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le Q.C_pos); apply le_trans (add_le_add he (mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ) |>.2 (Bias.circle_card g₀ mH o (k+ξ) (Ck.commuter Z k ξ (k+ξ) (by unfold TimePlus; omega)))) hd)); push_cast; -- might break h
 unfold d; unfold House.root_port at h; push_cast at h; linarith only [h]
end Primer
end YM.CF.BProof.Prime
