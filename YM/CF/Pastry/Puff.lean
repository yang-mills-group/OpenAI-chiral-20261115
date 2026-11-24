import YM.CF.Pastry.Works
import YM.CF.Petal.Cabin
set_option linter.unusedSectionVars false

/-! Supported even coefficient spaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pastry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Finset NormedSpace Petal
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n] {A B : FC n} {s t : Finset n}
-- support cost as home⇐some enlarged union predicates later. Sublattice in formal extent.
def Wheat (s : Finset n) := s.powerset.filter fun S=> Even S.card
def Flour (S : Finset n) (A : FC n) := ∃ f : Finset n→ℂ,A=∑ s∈Wheat S, f s • poke s
lemma Flour.door {S T : Finset n} (p : Flour S A) (k : T∉ Wheat S) : crumb A T=0 := by
  obtain ⟨f,rfl⟩:=p; rw [crumb_sum,sum_eq_zero]; intro i hi; rw [crumb_scale,chip,if_neg (fun (g:T=i)=> k (g.symm ▸ hi)),mul_zero]
lemma Flour.pin {S : Finset n} (h : Flour S A) : A=∑ s∈Wheat S, crumb A s • poke s := by
  obtain ⟨f,g⟩:=h
  nth_rw 1 [g]; apply sum_congr rfl; intro s l; congr 1; rw [g,crumb_sum,sum_eq_single_of_mem _ l,crumb_scale,chip,if_pos rfl,mul_one]
  intro j p w; rw [crumb_scale,chip,if_neg w.symm,mul_zero]
lemma Flour.allP (h : Flour s A) : A=∑ t:Finset n, crumb A t • poke t := by
  rw [←sum_subset (subset_univ (Wheat s))]; exact h.pin
  intro i _ k; rw [h.door k,zero_smul]
lemma Flour.trivial : Flour s (0:FC n) := ⟨fun _=>0,by simp⟩
lemma Flour.point (h : s∈Wheat t) : Flour t (poke s) := by
  refine ⟨fun j=>crumb (poke s) j,?_⟩; rw [sum_eq_single_of_mem _ h]; dsimp only; rw [chip,if_pos rfl,one_smul]; intro j l p; dsimp only; rw [chip,if_neg p,zero_smul]
lemma Flour.grainE : Flour s (1:FC n) := by rw [show (1:FC n)=poke ∅ from (Poly.tag_void (cane n)).symm]; apply Flour.point; simp [Wheat]
lemma Flour.add (h : Flour s A) (k : Flour s B) : Flour s (A+B) := by
  refine ⟨fun t=>crumb (A+B) t,?_⟩; simp_rw [crumb_add,add_smul,sum_add_distrib]; rw [←h.pin,←k.pin]
lemma Flour.smul (h : Flour s A) (c : ℂ) : Flour s (c • A) := by obtain ⟨f,rfl⟩:=h; exact ⟨fun x=>c*f x,by simp [smul_sum,mul_smul]⟩
lemma Flour.rsmul (h : Flour s A) (c : ℝ) : Flour s (c • A) := by
  have he : c • A=(↑c:ℂ) • A := by ext i j; simp [Complex.real_smul]; -- tune
  rw [he]; exact h.smul _
lemma Flour.sum {I : Type*} (S : Finset I) {v : I→FC n} (h : ∀ i∈S,Flour s (v i)) : Flour s (∑ i∈S,v i) := by
  classical
  induction S using Finset.induction_on with
  | empty=> rw [sum_empty]; exact Flour.trivial
  | insert i S p ih=> rw [sum_insert p]; exact (h i (mem_insert_self ..)).add (ih (fun i g=>h i (mem_insert_of_mem g)))
lemma Flour.mul (h : Flour s A) (g : Flour s B) : Flour s (A*B) := by
  rw [h.pin,g.pin,sum_mul]; apply Flour.sum; intro i u; rw [mul_sum]; apply Flour.sum; intro j t
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]; apply Flour.smul; apply Flour.smul
  unfold poke; rw [Poly.tag_mul]; split_ifs with k
  · apply Flour.smul; apply Flour.point; apply mem_filter.mpr
    obtain ⟨h,g⟩:=mem_filter.mp u; obtain ⟨x,l⟩:=mem_filter.mp t
    exact ⟨mem_powerset.mpr (union_subset (mem_powerset.mp h) (mem_powerset.mp x)), by rw [card_union_of_disjoint k]; exact Even.add g l⟩
  exact Flour.trivial
def pasta (s : Finset n) : Subalgebra ℝ (FC n) where
  carrier := Flour s
  zero_mem' := Flour.trivial
  one_mem' := Flour.grainE
  add_mem' := Flour.add
  mul_mem' := Flour.mul
  algebraMap_mem' c:= by rw [Algebra.algebraMap_eq_smul_one]; exact Flour.grainE.rsmul c
lemma Flour.flour {A : pasta s} : Flour s A.val:= A.property
lemma Flour.lift (h : Flour s A) (p : s⊆t) : Flour t A := by rw [h.pin]; apply Flour.sum; intro i v; exact (point (filter_subset_filter _ (powerset_mono.mpr p) v)).smul _
lemma Flour.comm (h : Flour s A) (p : Flour t B) : A*B=B*A := by
  conv_lhs=> arg 1; rw [h.pin];
  nth_rw 2 [h.pin] -- tune
  rw [mul_sum,sum_mul]; apply sum_congr rfl; intro i _; rw [p.pin,mul_sum,sum_mul]; apply sum_congr rfl; intro j k
  simp only [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; rw [show poke i*poke j=poke j*poke i from (Poly.commute _ _ _ (mem_filter.mp k).2),smul_comm]
abbrev Dough (n : Type*) [LinearOrder n] [Fintype n] := pasta (univ:Finset n)
instance ringM : NormedCommRing (Dough n) := { Subalgebra.normedRing (Dough n) with
  mul_comm:= fun x y=> Subtype.ext (Flour.comm (s:=univ) (t:=univ) x.property y.property) }
instance ringOneM : NormOneClass (Dough n) := ⟨show ‖(1:FC n)‖=(1:ℝ) by simp⟩
instance ringCompM : CompleteSpace (Dough n) := FiniteDimensional.complete ℝ _
lemma natNorm (x : Dough n) : ‖x‖=‖x.val‖:= rfl
lemma fineShape (x : Dough n) : Flour univ x.val := x.property
def stretch (s : Finset n) := (pasta s).comap (Subalgebra.val (Dough n))
lemma stretch_ok (A : Dough n) : A∈stretch s ↔ Flour s A.val := Iff.rfl
def hollow (x : ℂ) : Dough n := ⟨x • 1, Flour.grainE.smul x⟩
-- weight
def tier (H : ℝ) (x : FC n) := ∑ i:Finset n,H^i.card*‖crumb x i‖
lemma pitch {H:ℝ} (g : 0≤H) (x : FC n) : 0≤tier H x := sum_nonneg (fun i _=>by positivity)
lemma chaff (H : ℝ) : tier H (0:FC n)=0 := by simp [tier,crumb]
lemma white (H : ℝ) (S : Finset n) : tier H (poke S)=H^S.card := by simp [tier,chip, apply_ite _ _]
lemma white1 (H : ℝ) : tier H (1:FC n)=1 := by rw [show (1:FC n)=poke ∅ from (Poly.tag_void (cane n)).symm,white]; simp
lemma whiteℂ (H : ℝ) (S : FC n) (v : ℂ) : tier H (v • S)= ‖v‖*tier H S := by simp only [tier,crumb_scale,norm_mul,mul_sum,mul_left_comm ‖v‖]
lemma whiteℝ (H : ℝ) (S : FC n) (v : ℝ) : tier H (v • S)= ‖v‖*tier H S := by simp only [tier,crumb_scaleR,norm_smul,mul_sum,mul_left_comm ‖v‖]
lemma lies {H : ℝ} (g : 1≤H) (x : Dough n) : ‖x‖≤ tier H x.val := by
  rw [natNorm]; nth_rw 1 [(fineShape x).allP]; apply (norm_sum_le ..).trans; refine sum_le_sum ?_; intro i _; rw [norm_smul,mul_comm]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact (tag_size i).trans (one_le_pow₀ g)
lemma tier_plus {H:ℝ} (g : 0≤H) (x y : FC n) : tier H (x+y)≤tier H x+tier H y := by
  unfold tier; rw [← sum_add_distrib]; apply sum_le_sum; intro i _; rw [crumb_add,← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le ..) (by positivity)
lemma tier_sum {I : Type*} {H:ℝ} (g : 0≤H) (S : Finset I) (f : I→FC n) : tier H (∑ i∈S,f i) ≤ ∑ i∈S,tier H (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty=> rw [sum_empty,sum_empty,chaff]
  | insert i S v ih=> rw [sum_insert v,sum_insert v]; exact (tier_plus g ..).trans (add_le_add_right ih _)
lemma white_mul (H:ℝ) (p:0≤H) (S T : Finset n) : tier H (poke S*poke T) ≤ H^S.card * H^T.card := by
  unfold poke; rw [Poly.tag_mul]; split_ifs with k
  · rw [whiteℂ,Poly.sail_size,one_mul,show tier H ((cane n).tag _) = _ from white H (S∪T),card_union_of_disjoint k,pow_add]
  rw [chaff]; positivity
lemma tier_mul {H:ℝ} (g : 0≤H) (x y : Dough n) : tier H (x.val*y.val) ≤ tier H x.val*tier H y.val := by
  nth_rw 1 [(fineShape x).allP]; nth_rw 1 [(fineShape y).allP]; rw [sum_mul]; conv_rhs => simp only [tier] -- tune
  apply (tier_sum g ..).trans; rw [sum_mul]; apply sum_le_sum; intro i _; rw [mul_sum,mul_sum]; apply (tier_sum g ..).trans; apply sum_le_sum; intro j _
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, whiteℂ, whiteℂ]
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (white_mul H g i j) (norm_nonneg _)) (norm_nonneg _)).trans ?_; exact le_of_eq (by ring)
lemma Bellprep (H:ℝ) : Continuous (fun x : Dough n=> tier H x.val) := by
  unfold tier crumb; apply continuous_finsetSum; intro i _; exact continuous_const.mul (((continuous_apply ∅).comp ((continuous_apply i).comp continuous_subtype_val)).norm)
variable {Y : Type*} [DecidableEq Y] [Fintype Y]
def shelf (H : ℝ) (p : 1≤H) (K : Finset Y→Finset n) (L : Monotone K) : Petal.Bell Y (Dough n) where
  fare x := tier H x.val
  sound := Bellprep ..
  plus x y := tier_plus (zero_le_one.trans p) ..
  times := tier_mul (zero_le_one.trans p)
  single := white1 _
  free := chaff _
  normF := lies p
  scale x c := whiteℝ ..
  store S := stretch (K S)
  stair h := fun v e=> (show Flour _ _ from (stretch_ok v).mp e).lift (L h)
  wallL S := Submodule.closed_of_finiteDimensional (stretch (K S)).toSubmodule -- tune
end YM.CF.Pastry
