import YM.CF.BPress.Lilac.Rise
/- Locality evidence: truncating only long-cardinality primary cost after field reference.Prefactor assembled. Center Tag f.Real error budget. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Lilac
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger Push.AbsoluteSums Born
variable {m s N:Side}{B:BandWidth}{A:Bands (More (mid m s)) B}{R:Hangar (More (mid m s))}
local notation "Λ"=> mid m s
local notation "η"=> More Λ
variable {H: Sugar.Crew A}{T:GramM (mid m s)}{X: Sugar.Stage (mid m s)}{Y:Driver (mid m s)}{k:ℕ} {c q d t v ε e d' C D ζ δ τ u b:ℝ}{p0 p1 p2 p3:Pledge}{h: Wish Y p0 p1 p2}{G: Brace.Duet m s}
namespace Stripe
variable (B0:Born A R X Y) (P:Edition Y)(L:Passports Y T G h P p3 q d ε t v) (r:ℕ)(z: Fin 5)
def Wanted (A:Bands (More N) B)(X:Sugar.Stage N) (S:Support (More N)):= currencyT A X.W.M S
def Tiny (A:Bands (More N) B)(X:Sugar.Stage N)(r:ℕ)(S:Support (More N)):= Wanted A X S∧ S.card≤r
def δop (x:Tenor η)(Z:Fin 5):= P.op x (B0.H₁ Z)-P.op x (B0.H₁ 0)
def rosy (x:Tenor η)(z:Fin 5):= if Tiny A X r x.2 then δop B0 P x z else 0
def chast (b:SiteX A R)(z : Fin 5):= ∑ x:Tenor η with plan A R x.1=b, rosy B0 P r x z -- Rost
abbrev blur(r:ℕ)(T:Pledge):= Real.exp (- (T.rate*r)) * (2*T.price)
variable {B0 P r}
include L
lemma due_iff(x:Tenor η)(h:P.opfee x=0):∀ t: Y.Pose, P.op x t=0:=fun t=>norm_le_zero_iff.mp (h ▸ L.known x t)
lemma δabs(i:Tenor η):‖δop B0 P i z‖≤2*P.opfee i:= (norm_sub_le ..).trans ((add_le_add (L.known i _) (L.known i _)).trans (two_mul ..|>.symm.le))
lemma δlate (x: Tenor η)(q:¬Wanted A X x.2): δop B0 P x z=0:=by
 unfold Wanted currencyT at q; obtain ⟨i,f⟩:=not_forall.mp q; let f:= not_not.mp f; unfold δop; rw [← L.theme x (B0.H₁ 0) (fun _=> pivotal z A i)]; exact (congrArg (P.op x (B0.H₁ z) - ·) (L.view _ _ _ ((B0.turnD i z h).drop f.2))).trans (sub_self _)
lemma rate (x:Site η): (∑ s:Support η,(rosy B0 P r (x,s) z).re) ≤ B0.BiasQ z x+ blur r p3:=by
 have ht(x:Site η): ∑ a:Support η,(δop B0 P (x,a) z).re=B0.BiasQ z x:=by unfold δop; simp_rw [Complex.sub_re,sum_sub_distrib,← L.real0, bask]
 rw [←ht]; -- use difference long
 let f(s:Support η):= (rosy B0 P r (x,s) z).re-(δop B0 P (x,s) z).re
 suffices t: ∑ s,f s≤ blur r p3 by unfold f at t; rw [sum_sub_distrib] at t; linarith
 let U:= L.cruise; let v(i:Tenor η):= Ledger.score scaffold P.opfee p3.rate x i; let A1:=Real.exp (-(p3.rate*r)); have he : ∑ i:Support η, v (x,i) ≤p3.price:= budget_sum (budget_pull (Prod.mk x) (fun i j a=> Prod.mk.inj a|>.2) (U.hits x)) _ -- tune estimator.Lookup
 have hf:0≤2*A1:=mul_nonneg (by norm_num) (Real.exp_pos _).le; have hx(i): f i ≤ 2*A1*v (x,i):=by
    by_cases p:P.opfee (x,i)=0; · simp only [f,rosy,δop, due_iff L _ p,sub_self,ite_self,Complex.zero_re]; exact mul_nonneg hf ((U.hits x).1 _)
    have hu:= L.point _ p; unfold f; unfold rosy; by_cases h:Tiny A X r i; · rw [if_pos h,sub_self]; exact mul_nonneg hf ((U.hits x).1 _)
    rw [if_neg (show ¬ Tiny A X r i from h),Complex.zero_re, zero_sub]; by_cases V: Wanted A X i; swap; · rw [δlate L z _ V, Complex.zero_re,neg_zero]; exact mul_nonneg hf ((U.hits x).1 _)
    have hJ:r < i.card:= Nat.lt_of_not_ge (fun p=>h ⟨V,p⟩); unfold v Ledger.score; rw [if_pos (show x∈ scaffold (x,i) from hu.2)]; apply le_trans _ ((show 2*P.opfee (x,i) ≤ _ from ?_)); · exact (neg_le_abs _|>.trans (Complex.abs_re_le_norm _)).trans (δabs L z _) -- tune n sign
    change 2*P.opfee _ ≤ 2*A1*( Real.exp (p3.rate*i.card)*P.opfee _); rw [mul_assoc,←mul_assoc A1,← Real.exp_add]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (U.pos _) (Real.one_le_exp (by have he:(r:ℝ)≤ (i.card:ℝ):=(by exact_mod_cast hJ.le); nlinarith [p3.pos]))) zero_le_two -- tune let A1
 apply (sum_le_sum (fun i _=>hx i)).trans; rw [←mul_sum]; exact (mul_le_mul_of_nonneg_left he hf).trans (le_of_eq (by unfold blur A1; ring))
-- only roots meeting in counting area (needed for cost & assignments), pay.CD.dusk.
lemma appointed {r:ℕ}(v:ShortP X H R r)(x:Tenor η)(h:Tiny A X r x.2)(p:P.opfee x≠0): x.1∈ positions A R (plan A R x.1) (mcap X H r):=by
 obtain ⟨p,g⟩:=L.point _ p; have he:= (morning (Abyss.foot A X.W.M p h.1) p h.2 v x.1 g x.1 (halo_subset _ _ g)).1; exact mem_filter.mpr ⟨mem_univ _,rfl,near_gap he⟩
lemma reachEq (v:ShortP X H R r)(i:BlockY A R): (chast B0 P r i z).re = ∑ a∈ positions A R i (mcap X H r), ∑ S:Support η,(rosy B0 P r (a,S) z).re:=by
 let Vx:=mcap X H r; unfold chast Locale.positions; rw [Complex.re_sum,sum_filter, Finset.sum_filter,Fintype.sum_prod_type]; apply sum_congr rfl; intro i0 h; dsimp only; by_cases t: plan A R i0=i; swap; · simp [t]
 simp only [t,ite_true,true_and]; by_cases g:NearBlock A (mcap X H r) i0; rw [if_pos g]; rw [if_neg g]; apply sum_eq_zero; intro j _; unfold rosy; split; next a=>
    have hp:P.opfee (i0,j)=0:= Classical.byContradiction fun h=> g ((mem_filter.mp (appointed L v (i0,j) a h)).2.2); unfold δop; rw [due_iff L _ hp,due_iff L _ hp,sub_zero]; rfl
 next a=>rfl
-- truncated Qbias. 
theorem Qbias {r₀:ℕ}(h:ShineZ B0 r₀ C z)(g:ShortP X H R r)(f : r₀ ≤ mcap X H r)(e:Even R.L.val)(t:(B.D+2*mcap X H r+1:ℕ)*blur r p3≤ C/16)(Q:BlockY A R) : (chast B0 P r Q z).re ≤ -(C/16)*(R.L.val:ℝ)^3:=by
 let n:= mcap X H r; let S:= positions A R Q n; let F:= blur r p3; rw [reachEq L z g]; have ht(i):=rate (B0:=B0) L (r:=r) z i; refine (sum_le_sum (fun i _=> ht i)).trans ?_; rw [sum_add_distrib]; let G:=lowP g.μWide.le; have hp:=B0.ledgers Q h f G e; have hx:(0:ℝ)≤ F:= mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) p3.bought.le)
 change _+(∑ i∈S,F)≤_; have hv:S.card≤_:= pinned_cost A R Q G; apply le_trans (add_le_add hp ((((sum_const ..).trans (nsmul_eq_mul ..)).le).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hv) hx))); push_cast; push_cast at t; change ( _ :ℝ)+ _* _ *F ≤_; unfold F n; push_cast; nlinarith only [mul_le_mul_of_nonneg_left t (by positivity: (0:ℝ) ≤ (R.L.val:ℝ)^3)]
omit L
end Stripe
end YM.CF.BPress.Lilac
