import YM.SU5.Thin.Cascade.Costume
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder Classical
attribute [local instance] opCStarAlgebra
variable {a C r e:ℝ}{n m N:Side}
open Rapids BPress.Spin
open Pressure
open YM.Gleam
variable {d v:ℝ} {w l k:ℕ} {X:Scree.Loom n}{U:Orbit n}
variable {R:Lattice.Ratio m (More n)}(T:Tree.Forest R)
open Font
private def Mawk (S:Finset (Seat N)):Finset (Single N):= univ.filter (fun i=> place_x i ∈ S)
open Tenant
private lemma mawk_budget (S:Finset (Seat N)):(Mawk S).card ≤ S.card*180:=by
 let f(i:Single N) := (place_x i, i.1.2,i.2)
 let X:= S ×ˢ (univ: Finset (SpinIdx × SU.Slot))
 have hx(j : Single N)(p:j∈ Mawk S): f j∈ X:= mem_product.mpr ⟨(mem_filter.mp p).2,mem_univ _⟩
 rw [← card_image_of_injective (Mawk S) (show Injective f from fun ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩ e=> by obtain ⟨v,h,w⟩ : x=y ∧ i=k ∧ j=l:= ⟨needle (congrArg Prod.fst e),congrArg (fun i=> i.2.1) e, congrArg (fun i=> i.2.2) e⟩; rw [v,h,w])]
 apply (card_le_card (image_subset_iff.mpr hx)).trans_eq ?_; unfold X; rw [card_product,card_univ,Fintype.card_prod,SU.slots, show Fintype.card SpinIdx=4 from Fintype.card_fin _]
private lemma richColumns (P Q:Op (Single n)): DriveL1 (P-Q)=∑ i,∑ j, ‖(P-Q) j i‖:= sum_comm
abbrev poet (ξ C a k:ℝ)(d:ℕ):ℝ:=(2*Real.exp (-(a*d))+(d:ℝ)*4*(sphereRate*k)/ξ)*C
abbrev missed (r:Lattice.Ratio m (More n))(d:ℕ)(p:ℝ)(V:Pane n):= surfaceBill r d (broken r p V) ∅
open Gall
lemma poetry {δ v₀:ℝ}{N':ℕ}{a C:ℝ}(F:Finisher δ a C k N')(g:Skye.Roof n v r w X) (t: Odd R.count.val)(p:r≤δ)(s:N'≤n.val)(h:0≤ d)(pδ:r≥0)(E:l+w+1≤ R.count.val/2)(x:d≤v)(w':2*(R.count.val+1)<(More n).val)(U:Orbit n)(z:suitedFee R.count.val d≤v₀) (M:Tulip.Male): let V:= Lattice.gauge (frilly T U) (X U); DriveL1 (spar k M V - spar k M (1:Pane n)) ≤ poet δ C a v₀ l * (180*(n.val:ℝ)^4) + 2*C* (180*(missed R (l+w+1) d U.1:ℝ)):=by
 intro V; let P:= spar k M V; let Q:=spar k M (1:Bkg (More n)); let y:=frilly T U; have he: Guard V δ:=(((g.paid U).cov y).shrink p); have h₁:Filed P C:= F.column n s V he M; have h₂:Guard (1:Pane n) δ:=guard0 F.health.le; have hcore:Filed Q C:= F.column n s 1 h₂ M; let u:= l+w+1
 let T':=poet δ C a v₀ l; have hp : 0 ≤ T':=by unfold T' poet; have ht:=sphereRate_cost.positive; have h:=F.health; have hV:0 ≤ suitedFee R.count.val d:=(by unfold suitedFee; positivity); have he:= F.credit; have hx:=hV.trans z; positivity
 let A:=broken R d U.1; let W':Finset (Seat n):=univ.filter (fun i=>¬ Gleam.Safe R A u i); let HM:= Mawk W'; have hu(i: Single n): (∑ j,‖(P-Q) j i‖) ≤ T'+ if i ∈ HM then 2*C else 0:= by
    split
    · apply (show 2*C ≤ T'+(2*C) from le_add_of_nonneg_left hp).trans'; apply (sum_le_sum (g:=fun j=> ‖P j i‖+‖Q j i‖) (fun j _=> norm_sub_le ..)).trans; rw [sum_add_distrib]; exact (add_le_add (h₁ i) (hcore i)).trans_eq (two_mul C).symm
    next g'=>
       have hj:Gleam.Safe R A u (node i.1.1):= Classical.byContradiction fun x=> g' (mem_filter.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,x⟩⟩); -- node namespace
       have hh:= inSight T g h x w' hj; rw [add_zero]; exact F.wind n s V 1 he h₂ M l i _ (show 0 ≤ sphereRate*v₀ from (by have he:= sphereRate_cost.positive; have hk₀:0≤ suitedFee R.count.val d:=(by unfold suitedFee; positivity); have hh:=hk₀.trans z; positivity)) (fun i v=>(hh i v).trans (mul_le_mul_of_nonneg_left z sphereRate_cost.positive.le))
 let Ct:=missed R u d U.1; have ht:HM.card ≤ Ct*180:= (mawk_budget W').trans (Nat.mul_le_mul_right _ ((Gleam.wall_site (A:=A) t E).trans_eq (?_)))
 · have hx:(HM.card:ℝ) ≤180*(Ct:ℝ):= by rw [mul_comm]; exact_mod_cast ht
   rw [richColumns]; apply (sum_le_sum (fun i _=> hu i)).trans; rw [sum_add_distrib, sum_ite, sum_const_zero, sum_const,sum_const,card_univ,filter_mem_eq_inter,univ_inter,add_zero,nsmul_eq_mul,nsmul_eq_mul, Pic.units_t]; have he:= F.credit; linarith only [mul_le_mul_of_nonneg_right hx he.le] -- Pic.units_t exact? push_cast
 unfold Ct missed surfaceBill A; simp [u,pow_succ]
end YM.CF.Pannier.Chancel