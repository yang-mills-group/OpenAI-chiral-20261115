import YM.CF.BPress.Lily.Gardener
/-! § VolumeB-phase eq:B-Jrep. Letters of species one. Explicit row convention and site localization, not diagonal approximation. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Lily
open Function MeasureTheory Filter NormedSpace Finset Fock Lattice Cube Lat Spin Spin.Paint SU SU.Pair Chalk Pf Pressure Branch Bias Dial Nacre Tulip
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{C: Op I}
open Submodule Module
namespace Course
variable {T:Finset I}(x:Wave I)(u:Wave I)(D:I→FC I)
local notation "X"=> vacuum I
abbrev sacred (D:I→FC I)(t:stem T): Bool:= decide (t.val.card % 2=1) -- dummy D drop!
lemma sector_κ(t:stem T)(p:∀ i∈T,Sector T true (D i)): Sector T (sacred D t) (filament D (string t)) := by
 have he(l:List I)(h:l.toFinset⊆T): Sector T (decide (l.length % 2=1)) (filament D l):=by
    induction l with|nil=> exact (show Sector T false _ from Sector.one)|cons i l ih=> have ht:= p i (h (by simp)); have hx:= ht.contr.mul (ih (fun x p=> h (by simp [List.mem_toFinset.mp p]))); rw [show decide ( (i::l).length%2=1)=Bool.xor true (decide (l.length%2=1)) by rw [List.length_cons]; by_cases v:(l.length+1)%2=1; rw [decide_eq_true v, decide_eq_false (by omega : ¬ l.length%2=1)]; rfl; rw [decide_eq_false v, decide_eq_true (by omega : l.length%2=1)]; rfl]; exact hx
 have ht:= he (string t) (by simpa [string] using mem_powerset.mp t.property); simpa [string,sacred] using ht -- tune nil prod def
abbrev weights (x : Wave I)(u: Wave I)(D:I→FC I)(s:stem T):ℂ:= inner ℂ (seaH (L:=D) x s) u/ inner ℂ x x
variable {x u D}(F: Course T D x) (h:x≠0)
local notation "Z" => fun t:stem T => seaH (L:=D) x t
local notation "μ"=> inner ℂ x x
include F h
lemma pμ : μ≠0:= inner_self_ne_zero.mpr h -- tune
lemma seed_basis : LinearIndependent ℂ (Z) := by
 apply Fintype.linearIndependent_iff.mpr; intro g h' i; have he:=congrArg (inner ℂ (Z i)) h'; rw [inner_zero_right,inner_sum] at he; simp_rw [inner_smul_right,F.frame i, mul_ite, mul_zero] at he; simp only [sum_ite_eq,mem_univ,ite_true] at he; exact (mul_eq_zero.mp he).resolve_right (F.pμ h)
lemma reset(u:Wave I)(v:u∈ span ℂ (Set.range (seaH (L:=D) x (T:=T)))) : ∑ t:stem T, weights x u D t • (Z t)=u:=by -- notation BigOps
 let H(t:stem T):= Z t; let f(x':Wave I):=∑ t: stem T, weights x x' D t • H t; change f u=_; apply Submodule.span_induction (p:=fun x _=> f x=x) ?_ ?_ ?_ ?_ v
 · rintro x' ⟨i,k⟩; rw [←k]; change f (H i)=_; unfold f weights; rw [sum_eq_single i]; unfold H; rw [F.frame,if_pos rfl, div_self (F.pμ h),one_smul]; intro b _ v; unfold H; simp [F.frame,v]; simp
 · simp [f,weights]
 · intro x y u v h p; unfold f weights; simp_rw [inner_add_right,add_div, add_smul,sum_add_distrib]; exact congrArg₂ (·+·) h p
 intro a x' xM h; unfold f weights; simp_rw [inner_smul_right, mul_div_assoc a,mul_smul,←smul_sum]; rw [show (∑ t:stem T,_)=_ from ?_] -- tune equality binder, use directly
 exact h
lemma ownedB(t:FC I)(p: Sector T false t) (b:FC I) (e:u=acts b X)(w:Sector T false b) (q:x=acts t X) (L:∀ i∈T,Sector T true (D i)) : u∈span ℂ (Set.range (seaH (L:=D) x (T:=T))):=by
 let g(Y:stem T):= basisKet Y.val; let A:=span ℂ (Set.range g); have he (s:FC I){b:Bool}(p:Sector T b s) : acts s X∈ A:=by
    rw [←basis_expand (acts s X)]; apply Submodule.sum_mem; intro i _; by_cases h:i∈ T.powerset
    · exact Submodule.smul_mem _ _ (subset_span (Set.mem_range.mpr ⟨⟨_,h⟩,rfl⟩))
    rw [vacuum,basis_act,show s i ∅=0 from ?_,zero_smul]; exact Submodule.zero_mem _; by_contra t; apply h; refine mem_powerset.mpr (fun j s =>?_); by_contra f; exact notMem_empty j ((p.dotGrade _ _ t _ f).mpr s)
    -- patch_grade
 have hx: span ℂ (Set.range (seaH (L:=D) x (T:=T)))=A:=by
    refine Submodule.eq_of_le_of_finrank_le (span_le.mpr ?_) ?_; rintro x' ⟨y,rfl⟩; change winged D x _∈ A; unfold winged; rw [q,←act_mul]; exact he _ ((sector_κ D _ L).mul p)
    rw [finrank_span_eq_card (F.seed_basis h)]; exact finrank_range_le_card _ -- tune
 rw [hx, e]; exact he _ w
lemma odd_weight (t b:FC I)(p: Sector T false t)(w:Sector T false b)(e:u=acts b X)(q:x=acts t X)(L:∀ i∈T,Sector T true (D i))(s:stem T)(f:sacred D s=true): weights x u D s=0:=by
 let Z₀:= filament D (string s)*t; have hZ₀:Sector T true Z₀:=by simpa [f] using (sector_κ D s L).mul p
 unfold weights; rw [show seaH (L:=D) x s=acts Z₀ X from by rw [act_mul]; rw [q],e,← star_star Z₀, act_inner,←act_mul]; -- wrongly rw star? last
 rw [vacuum,basis_inner, basis_act, show (star Z₀*b) ∅ ∅=0 from (show Sector T true _ from (hZ₀.contr.mul w)).odd_lost ∅,zero_div] -- tune inner notation
lemma price_e (t:ℝ)(k:1≤‖x‖)(g:‖u‖ ≤ t)(A:stem T) : ‖weights x u D A‖ ≤ t:=by
 let v:= seaH (L:=D) x A; have ht:‖v‖=‖x‖ := by apply sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp; rw [←inner_self_eq_norm_sq (𝕜:=ℂ),←inner_self_eq_norm_sq (𝕜:=ℂ),show inner ℂ v v=μ from (F.frame A A).trans (if_pos rfl)] -- tune
 rw [weights,norm_div,inner_self_eq_norm_sq_to_K]; norm_cast; rw [abs_of_nonneg (sq_nonneg _),div_le_iff₀ (sq_pos_of_pos (zero_lt_one.trans_le k))]; apply (norm_inner_le_norm v u).trans; rw [ht,mul_comm]; exact mul_le_mul g (le_self_pow₀ k (by norm_num)) (norm_nonneg _) ((norm_nonneg _).trans g)
end Course
end YM.CF.BPress.Lily
