import YM.CF.Pastry.Puff
set_option linter.unusedSectionVars false

/-! Letter substitutions and the unit, with compatible covariances. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pastry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Finset NormedSpace Petal
attribute [local instance] opCStarAlgebra
variable {n m : Type*} [LinearOrder n] [Fintype n] [LinearOrder m] [Fintype m]
namespace Poly
variable (v : Poly n m)
def eval : FC n→ₗ[ℂ] FC m where
  toFun A:= ∑ S:Finset n, crumb A S • v.tag S
  map_add' A B:= by simp [crumb_add,add_smul,sum_add_distrib]
  map_smul' c x:= by simp [crumb_scale,smul_sum,mul_smul]
lemma eval_oneT (S : Finset n) : v.eval (poke S)=v.tag S := by change ∑ _,_=_; simp [chip,ite_smul]
lemma eval_one : v.eval 1=1 := by rw [← show poke ∅=(1:FC n) from tag_void _, eval_oneT,tag_void]
lemma eval_r (A : FC n) (w : ℝ) : v.eval (w • A)=w • v.eval A := by
  rw [show w • A=(w:ℂ) • A by ext i j; simp [Complex.real_smul],map_smul]; ext i j; simp [Complex.real_smul]
lemma eval_prod (S T : Finset n) : v.eval (poke S*poke T)=v.tag S*v.tag T := by
  rw [poke, poke,Poly.tag_mul, v.tag_mul]; split_ifs; rw [map_smul]; exact congrArg (fun z:FC m=>_ • z) (v.eval_oneT _); rw [map_zero]
lemma eval_mul (x y : Dough n) : v.eval (x.val*y.val)=v.eval x.val*v.eval y.val := by
  rw [(fineShape x).allP,(fineShape y).allP,sum_mul,map_sum,map_sum,map_sum,sum_mul]; apply sum_congr rfl; intro i _; rw [mul_sum,map_sum,mul_sum]; apply sum_congr rfl; intro j _
  rw [map_smul,map_smul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc, map_smul,map_smul, eval_prod,eval_oneT,eval_oneT,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
lemma eval_double (i j:n) : v.eval (put i*put j)=v.term i*v.term j := by
  rw [show put i=poke {i} from (tag_once (cane n) i).symm, show put j=poke {j} from (tag_once (cane n) j).symm, eval_prod,v.tag_once,v.tag_once]
def cook : Dough n→ₐ[ℝ] FC m where
  toFun x:=v.eval x.val
  map_one' := eval_one v
  map_mul' := eval_mul v
  map_add' x y:=map_add _ _ _
  map_zero' :=map_zero _
  commutes' r:= by
    simp_rw [Algebra.algebraMap_eq_smul_one]; change v.eval (r • 1)=_; rw [eval_r, eval_one]
lemma cookC : Continuous v.cook := v.cook.toLinearMap.continuous_of_finiteDimensional
lemma rising (x : Dough n) : v.cook (exp x)=exp (v.cook x) := by
  letI : NormedAlgebra ℚ (Dough n):= NormedAlgebra.restrictScalars ℚ ℝ (Dough n); letI : NormedAlgebra ℚ (FC m):= NormedAlgebra.restrictScalars ℚ ℝ (FC m)
  exact map_exp v.cook v.cookC _
end Poly
lemma Flour.putPut (S : Finset n) {i j:n} (g:i∈S) (h:j∈S) : Flour S (put i*put j) := by
  rw [show put i=(cane n).tag {i} from (Poly.tag_once (cane n) i).symm, show put j=(cane n).tag {j} from (Poly.tag_once (cane n) j).symm, Poly.tag_mul]; split_ifs with w
  · apply Flour.smul; apply Flour.point; apply mem_filter.mpr; refine ⟨mem_powerset.mpr (union_subset (singleton_subset_iff.mpr g) (singleton_subset_iff.mpr h)),?_⟩; rw [card_union_of_disjoint w, card_singleton,card_singleton]; exact ⟨1,rfl⟩
  exact Flour.trivial
lemma white_two {i j : n} (H:ℝ) (v:0≤H) : tier H (put i*put j)≤H*H := by
  have ht p : H ^ (@Finset.card n {p})= H := by simp
  have he := white_mul H v ({i}:Finset n) {j}; unfold poke at he; simp only [ht, Poly.tag_once] at he; exact he
def mast (x : FC n) := crumb x ∅
lemma mast_cont : Continuous (mast (n:=n)) := by change Continuous fun A:FC n => A ∅ ∅; exact (continuous_apply _).comp (continuous_apply _)
lemma mast_row (i j:n) : mast (put i*put j)=0 := by unfold mast crumb; rw [Matrix.mul_apply,sum_eq_zero]; intro k _; rw [put_entry]; split; rw [zero_mul]; rw [if_neg (show (∅:Finset n) ≠ insert i k from (show (insert i k).Nonempty from ⟨i,mem_insert_self ..⟩).ne_empty.symm),zero_mul]
lemma mast_word (S T : Finset n) : mast (poke S*poke T)=mast (poke S)*mast (poke T) := by
  unfold mast; simp_rw [chip]; unfold poke; rw [Poly.tag_mul]; by_cases h:S=∅ <;> by_cases g:T=∅
  · subst S T; simp [Poly.sail,show crumb ((cane n).tag ∅) ∅=1 by change crumb (poke _) _=1; rw [chip,if_pos rfl]]
  all_goals
    have he : ∅≠ S∪T := by intro q; have ht := union_eq_empty.mp q.symm; tauto
    by_cases l:Disjoint S T
    · rw [if_pos l,crumb_scale,show crumb ((cane n).tag _) _=0 from Eq.trans (chip _ _) (if_neg he),mul_zero]; simp [h,g,eq_comm]
    rw [if_neg l,show crumb (0:FC n) ∅=0 from rfl]; simp [h,g,eq_comm]
lemma mast_mul (x y : Dough n) : mast (x.val*y.val)=mast x.val*mast y.val := by
  rw [(fineShape x).allP,(fineShape y).allP]; unfold mast; rw [sum_mul,crumb_sum,crumb_sum,crumb_sum,sum_mul]; apply sum_congr rfl; intro i _; rw [mul_sum,mul_sum,crumb_sum]; apply sum_congr rfl; intro j _
  rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; simp_rw [crumb_scale]; rw [show crumb _ ∅=_ from mast_word i j]; unfold mast; ring
abbrev pane (x:Dough n) : ℂ := mast x.val
lemma mast_scaleR (x: Dough n) (b:ℝ) : pane (b • x)=b • pane x:= rfl
def panHom (n : Type*) [LinearOrder n] [Fintype n] : Dough n →ₐ[ℝ] ℂ where
  toFun := pane
  map_mul':=mast_mul
  map_add' _ _:= rfl
  map_zero':= rfl
  map_one' := by change (1:FC n) ∅ ∅=1; simp
  commutes' c:= by rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one,mast_scaleR,show pane (1:Dough n)=1 from Matrix.one_apply_eq _]
lemma pane_cost {x : Dough n} (H:ℝ) (h:0≤H) : ‖pane x‖ ≤ tier H x.val := by
  calc
    _ = H^(∅:Finset n).card*‖pane x‖ := by simp
    _ ≤ _ := single_le_sum (f:=fun i:Finset n=> H^i.card*‖crumb x.val i‖) (fun i _=>by positivity) (mem_univ _)
def cloudless (x: Dough n) := x-hollow (pane x)
lemma hollow_cost (H : ℝ) (x: ℂ) : tier H (hollow (n:=n) x).val=‖x‖ := by unfold hollow; dsimp only; rw [whiteℂ,white1,mul_one]
lemma cloudless_two (x: Dough n) : crumb (cloudless x).val ∅=0 := by change pane x-((pane x) • (1:FC n)) ∅ ∅=0; simp
lemma cloudy_cost (x: Dough n) (H a : ℝ) (h:1≤H) (p:0<a) (g:a≤1) : tier H (cloudless x).val ≤ a*tier (H/a) x.val := by
  unfold tier; rw [mul_sum]; apply sum_le_sum; intro i _; by_cases e:i=∅
  · subst i; rw [cloudless_two,norm_zero,mul_zero]; have hp : 0≤H/a:= by have hx:=zero_lt_one.trans_le h; positivity
    positivity
  have he : crumb (cloudless x).val i=crumb x.val i := by change crumb x.val i-((pane x) • (1:FC n)) i ∅=_; simp [e]
  rw [he, ←mul_assoc a]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have ht : a^i.card≤a := by
    have he : 1 ≤ i.card := (nonempty_iff_ne_empty.mpr e).card_pos
    nth_rw 2 [← pow_one a]; exact pow_le_pow_of_le_one p.le g he
  calc _ = a^i.card*(H/a)^i.card := by rw [←mul_pow]; field_simp
       _ ≤ _ := mul_le_mul_of_nonneg_right ht (by have he:=zero_lt_one.trans_le h; positivity)
-- action by unitary. preserve flour by pairs
variable (U : UNI n)
lemma twist_putPut (i j:n) : Flour univ (twist (quantU U) (put i*put j)) := by
  rw [map_mul,twist_p,twist_p]; simp only [prong, sum_mul, mul_sum]
  refine Flour.sum _ (fun i _=> Flour.sum _ (fun j _=>?_)); rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]; exact ((Flour.putPut univ (mem_univ _) (mem_univ _)).smul _).smul _ -- tune sums order
lemma pivotT (s : Finset n) (p : Even s.card) : Flour univ (twist (quantU U) (poke s)) := by
  induction s using Finset.strongInductionOn with
  | _ s ih=>
    by_cases k:s.Nonempty
    · obtain ⟨j,g⟩:=k; have he : (s.erase j).Nonempty := by rw [←card_pos,card_erase_of_mem g]; have hx:= (show s.Nonempty from ⟨j,g⟩).card_pos; obtain ⟨i,f⟩:=p; omega
      obtain ⟨l,u⟩:=he; let t := (s.erase j).erase l
      have hx : t ⊂ s := lt_trans (erase_ssubset u) (erase_ssubset g)
      have hv : Even t.card := by unfold t; rw [card_erase_of_mem u,card_erase_of_mem g]; have hj:= (show (s.erase j).Nonempty from ⟨l,u⟩).card_pos; obtain ⟨i,f⟩:=p; rw [card_erase_of_mem g] at hj; exact ⟨i-1,by omega⟩
      unfold poke; rw [← insert_erase g,Poly.tag_any _ _ _ (notMem_erase j s)]
      rw [twist_scalar, show (cane n).tag _=parity l t • ((cane n).term l*poke t) from by nth_rw 1 [← insert_erase u]; exact Poly.tag_any _ _ _ (notMem_erase l (s.erase j)),Algebra.mul_smul_comm,twist_scalar,←mul_assoc,map_mul]; exact (((twist_putPut U j l).mul (ih _ hx hv)).smul _).smul _
    rw [not_nonempty_iff_eq_empty.mp k,show poke ∅=(1:FC n) from Poly.tag_void _,map_one]; exact Flour.grainE
lemma Flour.pivot {s : Finset n} {A : FC n} (h : Flour s A) : Flour univ (twist (quantU U) A) := by rw [h.pin,map_sum]; apply Flour.sum; intro i k; rw [twist_scalar]; exact (pivotT U i (mem_filter.mp k).2).smul _
def foldE (x : Dough n) : Dough n := ⟨twist (quantU U) x.val,(fineShape x).pivot U⟩
def fold (U : UNI n) : Dough n →ₐ[ℝ] Dough n where
  toFun := foldE U
  map_zero' := Subtype.ext (map_zero (twist (quantU U)))
  map_one' := Subtype.ext (map_one (twist (quantU U)))
  map_add' x y:= Subtype.ext (map_add _ _ _)
  map_mul' x y:= Subtype.ext (map_mul _ _ _)
  commutes' c:= by rw [Algebra.algebraMap_eq_smul_one]; apply Subtype.ext; change twist (quantU U) (c • 1)=_; rw [map_smul,map_one]; rfl
lemma center_b (x : Dough n) : pane (fold U x)=pane x := by
  change (twist (quantU U) _) ∅ ∅= _; rw [twist_formula]; change (quant U.val*x.val*star (quant U.val)) ∅ ∅= _
  rw [←basis_act (quant U.val*x.val*star (quant U.val)),act_mul,remove_vac_pair,act_mul,←basis_inner,←act_inner] -- tune
  rw [show basisKet (∅:Finset n)=vacuum n from rfl,remove_vac_pair]; simp [pane,mast,vacuum,crumb]
lemma cloudT (x : Dough n) : fold U (cloudless x)=cloudless (fold U x) := by unfold cloudless; rw [map_sub,center_b]; congr 1; apply Subtype.ext; exact (twist_scalar _ _ _).trans (by rw [map_one]; rfl) -- tune
end YM.CF.Pastry
