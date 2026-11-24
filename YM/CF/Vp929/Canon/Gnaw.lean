import YM.CF.Vp929.Canon.Musc
import YM.CF.Tap.Pallet
import YM.CF.Vp929.Budget.Arith
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
namespace TestW
open Fir
open SU Bloch Tap
variable {n L:Side} {M:Male} {j:ℕ} {q C d a b v A t:ℝ}
variable {F:RegBudget n}{P:BudgetPoint}{s:Finset (Scree.Hub n)} (vS:liveB s)
local notation "E0"=> Op (Single n)
local notation "E2"=> SpinIdx × SU.Slot
local notation "WW" u:max=> heroP u
local notation "Ψ"=> StackL F s
local notation "μX"=> (1:Pane n)
local notation "ρX"=> spar j M (1:Pane n)
def zs (j:ℕ)(M:Male)(X:Op (Single n))(i:Axis):Pal:=zest j M (heroP X) i
abbrev τ_ (j:ℕ)(M:Male)(V:Op (Single n)):= zeus j M (heroP V)
lemma live_full (n:Side):liveB (univ:Finset (Scree.Hub n)):=by intro i; ext x; have ⟨u,h⟩:= Finite.surjective_of_injective (f:= moveHub i) (pure_s i) x; simp [mem_image,show ∃ j, moveHub i j=x from ⟨u,h⟩]
include vS in
lemma live_other : liveB sᶜ:=by
 intro i; ext x; obtain ⟨u,rfl⟩:= Finite.surjective_of_injective (f:=moveHub i) (pure_s i) x
 have h(v:Finset (Scree.Hub n)): moveHub i u∈v.image (moveHub i) ↔ u∈v:=by rw [mem_image]; exact ⟨fun ⟨t,d,w⟩=>pure_s i w ▸ d,fun x=>⟨u,x,rfl⟩⟩
 have hg: moveHub i u∈s↔u∈s:=by nth_rw 1 [←vS i]; exact h s
 rw [h,mem_compl,mem_compl,hg]

-- sample through actual frequencies. 'Read' repr of (1-P)D_F P
structure Scoria (j:ℕ)(M:Male)(V:Op (Single n))(u:ℝ):Prop where
 axisP : AxisP (heroP V)
 earm : let W:= Tap.Tern j M (loft V); let t:=Dial.spar j M (1:Pane n); (1-t)*V*t=love n (Rush.cart n W) ∧ RailP 2 W u ∧ Reads W (potion j M (heroP V))

abbrev pawe (j:ℕ)(p:1 ≤ j)(b:Bool):= (pawn_p j 2 p b).choose
abbrev fixC (j:ℕ)(p:1 ≤ j):ℝ:= Fintype.card (SpinIdx×SU.Slot)*(Fintype.card (SpinIdx ×SU.Slot)*(pawe j p false*4^2*(2^2*(16:ℝ)))* pawe j p true)
variable (pp:IncX Utrue F P a b)(ha:1 ≤ a)(sp:P.power=2)
include pp ha sp vS
lemma gem (p:1 ≤ j)(M:Male)(d:ℕ) (u:∀ i∈s, d ≤ coverNumber P.B i.val.2) : Scoria j M Ψ (fixC j p* (Real.exp (-(P.supportExponent*d))*b/a^2)):=by
 obtain ⟨X,Pw,H⟩:=pp.weight; let m:=P.supportExponent*d; let ν:=Real.exp (-m)*b; let η:=16*ν; let W:=Ψ; have hs(i:Scree.Hub n):0 ≤ X i:= Beau.grit_p P (Pw i) (zero_le_one.trans ha)
 have hp : ∑ i∈s,X i ≤ Fintype.card (Site n)*η:=by
    let Tc(i:Scree.Hub n):= P.mass i.val.2 (X i)
    have ht: ∑ i∈s,Tc i ≤ Fintype.card (Site n)*(16*b):=by
       refine le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun i _ _=>mul_nonneg (Real.exp_pos _).le (hs _))) ?_
       rw [←sum_fiberwise_of_maps_to (s:=univ) (g:=fun i:Scree.Hub n=> i.val.1) (t:=univ) (fun i _=>mem_univ _)]
       refine le_trans (sum_le_sum (fun i _=>show (∑ j: Scree.Hub n with j.val.1=i,Tc j)≤b from ?_)) ?_; swap
       · rw [sum_const,card_univ,nsmul_eq_mul]; change ((Fintype.card (Skye.Seat n)):ℝ)*b≤_
         simp [More,Skye.Seat,site_card]; nlinarith
       rw [sum_filter]; unfold Tc; simpa only [eq_comm] using H i
    have hh: ∑ i∈s,X i≤ Real.exp (-m) * ∑ i∈s,Tc i:=by
       rw [mul_sum]; apply sum_le_sum; intro i e; change X i≤ _*(Real.exp _*_); rw [←mul_assoc]; apply le_mul_of_one_le_left (hs _); rw [←Real.exp_add]; apply Real.one_le_exp; rw [add_comm,←sub_eq_add_neg]; apply sub_nonneg.mpr
       exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (u _ e)) P.exponent_pos.le
    exact hh.trans ((mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le).trans_eq (by unfold η ν m; ring))
 obtain ⟨r,hx,t,g⟩:= silver F s vS (Kred _ _ pp) X _ _ (fun i _=> Pw i) (zero_lt_one.trans_le ha) hp
 rw [sp] at t; let A:=t
 let J:=Tern j M (loft W); obtain ⟨_,hk⟩:= (pawn_p j 2 p true).choose_spec; obtain ⟨_,hm⟩:=(pawn_p j 2 p false).choose_spec; let h' := foldYP (hm M) A
 refine ⟨r, Eq.trans ?_ (winP j 2 p M (loft Ψ) _ A),?_,?_⟩
 · unfold Dial.spar; rw [profile_trivial]; conv_lhs => rw [hx]
 · change RailP 2 (Tern j M (loft Ψ)) _; convert foldYP h' (hk M) using 1 <;> first | rfl | ( unfold fixC pawe Ember.coneA η ν m; ring)
 let hp':= reads_fold (hm M) A (hel_pawn j p M false) (ladL Ψ); exact reads_fold h' (hk M) hp' (hel_pawn j p M true)
omit pp ha sp vS
def song (q:ℝ)(ϑ:Axis→ Bool):Momentum:=fun i=> q*signs (ϑ i)
variable {X Y:Op (Single n)}
abbrev sovX (q:ℝ)(A:Momentum→ Pal):Pal:= (16*q)⁻¹ • ∑ η : Axis→Bool, signs (η 0) • A (song q η)
variable (e:Frequency L n q)
include e
lemma sung (η:Axis→Bool): song q η ∈ baseCube:=by
 have hx:q≤1:=e.small.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
 constructor
 · ext i; simp [song]
 intro i; by_cases t:η i=true <;> simp [song,signs,t,abs_of_pos e.pos] <;> linarith only [Real.pi_gt_three,hx,e.pos]
lemma sung_fee (η:Axis→Bool)(f:Cover): mode (song q η) (n.val • f)=Rush.fee f:=by
 obtain ⟨m,v,rfl⟩:= e.matter; let q:ℝ:=m*(Real.pi/n.val); unfold mode Rush.fee; rw [mul_sum,Complex.exp_sum]; refine prod_congr rfl (fun i h=>?_)
 rw [show Complex.I * _= (f i:ℂ)*(m*((signs (η i):ℂ)*(Real.pi:ℂ)*Complex.I)) from ?_,Complex.exp_int_mul,Complex.exp_nat_mul,show Complex.exp ((signs (η i):ℂ)*(Real.pi:ℂ)*_)=-1 from ?_, v.neg_one_pow]
 all_goals first
 | (solve | (cases p:η i <;> simp [signs,Complex.exp_pi_mul_I,Complex.exp_neg, neg_mul]; done))
 | skip
 have h:n.val≠0:=Nat.ne_of_gt n.property; have hg:(n.val:ℂ)≠0:=by exact_mod_cast h
 simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]; unfold song; push_cast; field_simp
lemma hear (h: (1-ρX)*X*ρX=(1-ρX)*Y*ρX)(η:Axis→Bool)(p:Scoria j M X v)(w:Scoria j M Y d) : potion j M (WW X) (song q η)=potion j M (WW Y) (song q η):=by
 obtain ⟨hh,r,g⟩:=p.earm; obtain ⟨hk,x,t⟩:=w.earm; let A:=Tern j M (loft X); let B:=Tern j M (loft Y); have he:cart n A=cart n B:= (love n).injective (hh.symm.trans (h.trans hk)); let q':=song q η
 ext i j'; let y:=fun k:E2=>(1:Pal) k j'; let z:Site n:=0
 have hm: (mode q' (Rush.natural z) * (potion j M (WW X) q' *ᵥ y) i)= mode q' (Rush.natural z)*(potion j M (WW Y) q' *ᵥ y) i:=by
    rw [←Rush.earns g (sung e _) (sung_fee e _) y,←Rush.earns t (sung e _) (sung_fee e _) y]; rw [he]
 have hs:=mul_left_cancel₀ (show mode q' (Rush.natural z)≠0 from Complex.exp_ne_zero _) hm; simpa [Matrix.mulVec,dotProduct,y,Matrix.one_apply] using hs
lemma sov_back (h:(1-ρX)*X*ρX=(1-ρX)*Y*ρX)(p:Scoria j M X v)(w:Scoria j M Y d): sovX q (potion j M (WW X))=sovX q (potion j M (WW Y)):=by
 unfold sovX; simp_rw [hear e h _ p w]
omit e
end TestW
end Test
end YM.CF.Py.Rate
