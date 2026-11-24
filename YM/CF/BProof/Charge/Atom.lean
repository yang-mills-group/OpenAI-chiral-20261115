import YM.CF.BProof.Moment.Book
import YM.CF.BProof.Site.Visit
import YM.CF.BProof.Moment.Scan
import YM.Work.F05.Actions
import YM.Work.F03.Flat

/-! Each channel and loop/cubic/quartic charges: weak. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open RG Wilson Lattice Finset Function Filter Push.AbsoluteSums Work Micro Moment MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {s:Side} {G:Gauge} (c:Clip)(p:BudgetPoint)(T:PathData G)(M:ℕ)(σ: Signed)(β:ℝ)(U : Config G s){t W C Λ:ℝ}

-- avoid CF.Graph import
lemma atom_pay {i:ℕ}(A:Atom G i)(x:Site s) : ‖A.placed p U x‖ ≤ A.magnitude *p.threshold^i:=by
 have hg:=p.threshold_pos
 by_cases h:Healthy p.threshold (A.footprint x) U
 · rw [Atom.placed,masked_eq _ _ _ _ h]; unfold Atom.unmasked Atom.poly; let C (j:Fin i):=(A.leg j).atSite U x; have ht(j:Fin i):‖C j‖ ≤ p.threshold:=by
      let s:=A.leg j; let P:=F03.slotFace s x; have he:P.1∈A.footprint x:=by
         refine mem_image.mpr ⟨s.offset,mem_insert_of_mem ?_,rfl⟩; refine mem_biUnion.mpr ⟨j,mem_univ _,mem_union_right _ ?_⟩; exact List.mem_toFinset.mpr (show s.offset∈ s.offset::_ from List.mem_cons_self)
      unfold C; rw [F03.atSite_path,G.norm_adjoint]; refine le_trans (G.curvature_norm _) ?_; by_contra! t; exact Finset.disjoint_left.mp h he ((flags_spec ..).mpr ⟨P,Work.E01.base_touched _,t⟩)
   have hp(j)(b:G.ColorIndex): ‖C j b‖ ≤ p.threshold:= (PiLp.norm_apply_le _ _).trans (ht j)
   refine (norm_sum_le ..).trans ?_; rw [Atom.magnitude,sum_mul]; refine sum_le_sum fun b _=> ?_; rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Finset.abs_prod]; refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _); refine (prod_le_prod (fun i _=>abs_nonneg _) (g:=fun _=>p.threshold) (fun i _=> hp i (b i))).trans_eq (by simp)
 rw [Atom.placed,masked_ne _ _ _ _ h,norm_zero]; unfold Atom.magnitude; positivity
lemma atom_g {d:ℕ} (A:Atom G d)(x:Site s)(h:A.Invariant) (g:Site s→G.El) : A.placed p (Lattice.gauge g U) x=A.placed p U x := by
 have he : Healthy p.threshold (A.footprint x) (Lattice.gauge g U) = Healthy p.threshold (A.footprint x) U:=by simp [Healthy]
 unfold Atom.placed; by_cases hv:Healthy p.threshold (A.footprint x) U
 · rw [masked_eq p.threshold _ _ (Lattice.gauge g U) (show Healthy p.threshold _ _ from he.symm ▸ hv),masked_eq _ _ _ _ hv]; dsimp only [Atom.unmasked]; simp_rw [Work.F05.slot_gauge]; exact h ..
 rw [masked_ne p.threshold _ _ (Lattice.gauge g U) (show ¬Healthy p.threshold _ _ from he.symm ▸ hv),masked_ne _ _ _ _ hv] -- tune
variable {d:ℕ}(A:ℕ→Atom G d)(h: SumBudget (fun i=>(A i).budget W) C) (hu:∀ i,(A i).Invariant)(hw:0<W) (δ:ℝ)

abbrev Deed (s:Side):= Site s×ℕ
def aTax(i:Deed s)(U:Config G s):ℝ:= δ*(A i.2).placed p (pull σ 0 U) i.1 -- parameters U explicit end
def aSize(i:Deed s):ℝ:= |δ| *p.threshold^d * (A i.2).magnitude
def aFoot(i:Deed s) : Support s:= move σ (halo 8 ((A i.2).footprint i.1))
lemma aTax_norm(i:Deed s) : ‖aTax p σ A δ i U‖≤aSize p A δ i:=by
 rw [aTax,norm_mul,Real.norm_eq_abs]; apply le_trans (mul_le_mul_of_nonneg_left (atom_pay ..) (abs_nonneg _)); exact le_of_eq (by unfold aSize; ring)
lemma aFoot_ne (i:Deed s) : (aFoot σ A i).Nonempty:= ⟨_,moves σ (halo_subset 8 _ (Next.Rank.Thirst.stationed i.1 _ _))⟩

def ann (W:ℝ):= W/(4*17^4)
def atomUnit (W:ℝ)(C:ℝ):= (Real.exp (W/2)*(2*8+1 :ℝ)^4)*((W/2)⁻¹^4*(4:ℕ).factorial*Real.exp (W/2))*C
include h hw in
lemma atom_p (s:Side) : Toll (aFoot (s:=s) σ A) (aSize p A δ) (ann W) (atomUnit W C*(|δ| *p.threshold^d)):=by
 let ε:=W/2; have he : 0<ε:=half_pos hw; let u(i:ℕ):=(A i).length
 let F:=(aSize (s:=s) p A δ); have ht:=p.threshold_pos
 have hv : SumBudget (fun a:ℕ=>Real.exp (W*u a)*(A a).magnitude) C:=by unfold u; simpa only [mul_comm (Real.exp _),Atom.budget] using h -- tune
 let D:=|δ| *p.threshold^d
 convert scan (aFoot (s:=s) σ A) (equiv (s:=s) σ) 8 u F (fun x=> le_trans (norm_nonneg _) (aTax_norm p σ (1:Config G s) A δ x)) (ann W) he (budget_nonneg h) (fun i=>(A i).magnitude) hv (by unfold D; positivity : 0≤ D) (Real.exp_pos ε).le (fun p=>le_rfl) (fun a=> ?_) (fun a i=> ?_) using 1
 · unfold atomUnit ε D; norm_num; ring -- subgoals first?
 · rw [aFoot,move_card,← Real.exp_add]; have heq:=atomHL_card a.1 (A a.2); let r:=u a.2
   have hA:0≤ann W:=by unfold ann; positivity
   apply Real.exp_monotone; rcases a with ⟨x,i⟩; apply le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr heq) hA); unfold ann u ε; push_cast; exact le_of_eq (by ring)
 intro hi; obtain ⟨x,hx,rfl⟩:= mem_image.mp hi; have hg:=atomHL_span a.1 (A a.2) x hx
 change separation (σ.act _) (σ.act _)≤_; rw [separation_signed,separation_comm]; unfold u; omega

def atomBook (p:BudgetPoint)(σ:Signed) (A:ℕ→Atom G d)(δ:ℝ) {W C} (h: SumBudget (fun i=>(A i).budget W) C)(hu:∀ i,(A i).Invariant)(hw:0<W) : Letters G s (Deed s) where
 foot:=aFoot σ A
 map:= aTax p σ A δ
 size:=aSize p A δ
 spot:=aFoot_ne σ A
 loc i:=move_loc σ (atomHL_loc i.1 (A i.2))
 pushes i U V g:=congrArg (δ*·) (atomHL_local i.1 (A i.2) p _ _ (agrees_turn σ _ _ _ g)) -- dots
 kept i t U:=by unfold aTax; rw [F05.pull_gauge_zero,atom_g p _ _ _ (hu i.2)]
 meas i:=by refine measurable_const.mul (Measurable.comp (f:=pull σ 0) (masked_measurable _ _ _ ((A i.2).unmasked_cont i.1).measurable) ((continuous_pull ..).measurable))
 weight i U:= aTax_norm ..
 saved := ((atom_p p σ A h hw δ s).total (S:=aFoot σ A) (v:=aSize (s:=s) p A δ) (by unfold ann; positivity) (aFoot_ne σ A)).2.1
lemma atom_bookpay : ((atomBook (s:=s) p σ A δ h hu hw).charge).price U = δ * ∑ x:Site s, PathData.atomSeries A p (pull σ 0 U) x:=by
 let D:= atomBook (s:=s) p σ A δ h hu hw; rw [Letters.recorded]
 change (∑' i:Deed s,D.map i U)=_; rw [(D.sum_point U).tsum_prod,tsum_fintype,mul_sum]; apply sum_congr rfl; intro i hi; exact tsum_mul_left
end YM.CF.BProof.Charge
