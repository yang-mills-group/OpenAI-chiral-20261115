import GaugeFieldConstruction.Keeping
import GaugeFieldConstruction.Square

/-!
# Orders needed for (93) and for injection tests
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice
open Cauchy Row Phys Calibration Finset U1 Submodule Record Floor Raw
open scoped BigOperators
variable {α β γ η : Type*}
local instance : DecidableEq GIndex := inferInstance
local instance : DecidableEq FIndex := inferInstance

def deg (i : MI) := i.1+i.2.1+i.2.2
lemma step_up (i : MI) (k : S3) : deg (bump k i)=deg i+1 := by fin_cases k <;> simp [deg,bump] <;> omega

def rim (n : ℕ) := ((range (n+1)) ×ˢ (range (n+1)) ×ˢ range (n+1)).filter (fun i:MI=>decide (deg i≤n))
lemma side (n : ℕ) (u : MI) : u∈rim n ↔ deg u ≤ n := by simp [rim,deg]; omega

def bound (n : ℕ): Finset FIndex := Finset.univ ×ˢ rim n
def formG (n : ℕ): Finset GIndex :=
  Finset.univ ×ˢ ((Finset.univ (α:=S3) ×ˢ rim n).subtype fun i=> i.1=2→i.2.2.2=0)
lemma inside_f (n i) : i∈bound n ↔ deg i.2≤n := by rw [bound,mem_product]; simp [side]
lemma inside_g (n i) : i∈formG n ↔ deg i.2.val.2≤n := by rw [formG,mem_product]; simp [side]
lemma rising {s t : Finset α} (h : s⊆t) : Area s≤Area t := Finsupp.supported_mono h

lemma cut_C (b k n) : Area (bound n) ≤ comap (Cder b k) (Area (bound (n+1))) := map_area (fun i H=>by
  have ht (s : S3) (a) : C a (bump s i.2) ∈ Area (bound (n+1)) := by
    have p : (a,bump s i.2)∈ bound (n+1) := by rw [inside_f]; change deg (bump _ _) ≤ _; rw [step_up]; exact Nat.add_le_add_right ((inside_f n i).mp H) 1
    exact Finsupp.single_mem_supported ℂ 1 p
  refine Fin.lastCases (i:=k) ?_ fun j=>?_
  · rw [show Fin.last 3=τ from rfl,Clast,Ctime,on_ket]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun s _=> Submodule.sum_mem _ (fun c _=> smul_mem _ _ (ht ..)))
  rw [Cspace, Cshift,on_ket]; exact ht ..)
lemma beds (b k n) : C  b k ∈ Area (bound n) ↔ deg k≤ n := Finsupp.mem_supported ℂ _ |>.trans (by simp [bound,C, ket,side])
lemma flower (b i n) : G b i n∈ Area (formG (deg n)) := by
  unfold G; split_ifs with hp
  · exact Finsupp.single_mem_supported ℂ 1 ((inside_g _ _).mpr le_rfl)
  push Not at hp
  have he (a) : deg (bump a (strip n))=deg n := by
    rw [step_up]; unfold strip deg; dsimp only; omega
  apply Submodule.neg_mem; apply Submodule.add_mem
  · exact Finsupp.single_mem_supported ℂ 1 ((inside_g _ _).mpr (he 0).le)
  exact Finsupp.single_mem_supported ℂ 1 ((inside_g _ _).mpr (he 1).le)
lemma bud (i j : Axis) (n) : F i j n ∈ Area (formG (deg n)) := by
  refine Fin.lastCases (i:=i) ?_ (fun a=>?_) <;> refine Fin.lastCases (i:=j) ?_ (fun d=>?_)
  all_goals simp only [F,Fin.lastCases_castSucc,Fin.lastCases_last]
  · exact Submodule.zero_mem _
  · exact flower ..
  · exact Submodule.neg_mem _ (flower ..)
  split_ifs
  · exact Submodule.zero_mem _
  · exact flower ..
  exact Submodule.neg_mem _ (flower ..)
lemma growing {m n} (h : m≤n) : formG m ⊆ formG n := fun i u=> (inside_g _ _).mpr (((inside_g _ _).mp u).trans h)
lemma raising {m n} (h : m≤n) : bound m⊆bound n := fun i u=> (inside_f _ _).mpr (((inside_f _ _).mp u).trans h)
lemma cut_G (k n) : Area (formG n) ≤ comap (Gder k) (Area (formG (n+1))) := map_area (fun i h=>by
  have hu (a b j) : G b j (bump a i.2.val.2) ∈ Area (formG (n+1)) := rising (growing (by rw [step_up]; exact Nat.add_le_add_right ((inside_g ..).mp h) 1)) (flower ..) -- args
  refine Fin.lastCases (i:=k) ?_ fun s=>?_
  · rw [show Fin.last 3=τ from rfl,Glast, Gtime,on_ket]; dsimp only; exact Submodule.sub_mem _ (hu ..) (hu ..)
  rw [Gspace,Gshift,on_ket]; exact hu ..)
lemma both {p : Finset α} {q : Finset β} {x : J α} {y : J β} (a : x∈ Area p) (b : y∈ Area q) :
    times' x y ∈ Area (p ×ˢ q) := by
  have ht : Area q≤comap (times' x) (Area (p ×ˢ q)) := map_area fun i hi=>by
    have he : Area p≤comap (times'.flip (ket i)) (Area (p ×ˢ q)) := map_area (fun j hj=>by
      change times' _ _∈_; rw [takes]; exact Finsupp.single_mem_supported ℂ 1 (Finset.mem_product.mpr ⟨hj,hi⟩))
    exact he a
  exact ht b
lemma splits {p q : Finset α} {r s : Finset β} {X : Module.End ℂ (J α)} {Y : Module.End ℂ (J β)}
    (h : Area p ≤ comap X (Area q)) (k : Area r≤comap Y (Area s)) (U : p⊆q) (V : r⊆s) :
    Area (p ×ˢ r) ≤ comap (splitD X Y) (Area (q ×ˢ s)) := map_area fun i v=>by
  rw [← takes i.1 i.2, split_legs]
  obtain ⟨b,c⟩:= Finset.mem_product.mp v
  have hi : ket i.1∈ Area p:=Finsupp.single_mem_supported ℂ 1 b
  have hj : ket i.2∈ Area r:=Finsupp.single_mem_supported ℂ 1 c
  exact Submodule.add_mem _ (both (h hi) (rising V hj)) (both (rising U hi) (k hj))
lemma squiggle (k) (n : ℕ) : Area (formG n ×ˢ formG n) ≤ comap (P_g k) (Area (formG (n+1) ×ˢ formG (n+1))) :=
  splits (cut_G k n) (cut_G k n) (growing (by omega)) (growing (by omega))
lemma spark (k) (n : ℕ) : Area (bound n ×ˢ bound n) ≤ comap (P_f k) (Area (bound (n+1) ×ˢ bound (n+1))) :=
  splits (cut_C false k n) (cut_C true k n) (raising (by omega)) (raising (by omega))
lemma slope' (k) (n : ℕ) : Area (bound n ×ˢ bound n) ≤ comap (L k) (Area (bound (n+1) ×ˢ bound (n+1))) := by
  apply splits _ (cut_C true k n) (raising (by omega)) (raising (by omega)); intro x v
  change -(Cder false k x)∈Area _; apply Submodule.neg_mem; exact (cut_C false k n) v
lemma lines {h k : ℕ} (p : h≤k) : Area (bound h ×ˢ bound h)≤ Area (bound k ×ˢ bound k) := rising (Finset.product_subset_product (raising p) (raising p))
lemma stepY (n m : ℕ) k : Area ((bound m ×ˢ bound m) ×ˢ formG n) ≤ comap (P_x k) (Area ((bound (m+1) ×ˢ bound (m+1)) ×ˢ formG (n+1))) :=
  splits (spark k m) (cut_G k n) (Finset.product_subset_product (raising (by omega)) (raising (by omega))) (growing (by omega))
lemma image {H : Submodule ℂ (J α)} [Fintype γ] (p : γ→ J α) (h : ∀ i,p i∈H) : space p ≤ H := by
  rw [space,Fintype.range_linearCombination]; exact Submodule.span_le.mpr (by rintro a ⟨v,rfl⟩; exact h v)

lemma seedF (a : Spin) : C a 0∈ Area (bound 0) := (beds ..).mpr le_rfl
lemma seeds (i) : B i∈ Area (bound 0 ×ˢ bound 0) := by
  unfold B; apply Submodule.sum_mem; intro a _; apply Submodule.sum_mem; intro b _; apply Submodule.smul_mem; exact Invoice.both (seedF a) (seedF b)
lemma spark_s {n} k {x : J Row.f} (h : x∈ Area (bound n ×ˢ bound n)) : P_f k x∈ Area (bound (n+1) ×ˢ bound (n+1)) := spark k n h
lemma slope_s {n} k {x : J Row.f} (h : x∈ Area (bound n ×ˢ bound n)) : L k x∈ Area (bound (n+1) ×ˢ bound (n+1)) := slope' k n h
lemma f_earns (i : F4) : evalTf i∈ Area (bound 1 ×ˢ bound 1) := by
  rcases i with ⟨j,k|l⟩
  · simp only [evalTf,Sum.elim_inl]; exact slope_s k (seeds j)
  simp only [evalTf, Sum.elim_inr]; exact spark_s l (seeds j)
lemma priorF : SF four ≤ Area (bound 1 ×ˢ bound 1) := sup_le (image B (fun i=> lines (by decide) (seeds i))) (image evalTf f_earns)
lemma f_res (i : F5) : evalF i∈ Area (bound 2 ×ˢ bound 2) := by
  rcases i with ⟨i,g|k|⟨u,w⟩⟩ <;> simp only [evalF, Sum.elim_inr,Sum.elim_inl]
  · exact slope_s g.val.1 (slope_s g.val.2 (seeds i))
  · exact spark_s k.val.1 (spark_s k.val.2 (seeds i))
  exact spark_s u (slope_s w (seeds i))
theorem STF : SF five≤ Area (bound 2 ×ˢ bound 2) := by
  change SF four ⊔ space evalF≤_
  exact sup_le (le_trans priorF (lines (by decide))) (image evalF f_res)
lemma AR (i) : arc i∈ Area (formG 0) := bud i.toBlade.val.1 i.toBlade.val.2 0
lemma AR' (i) : arc i∈ Area (formG 1) := rising (growing (show 0≤1 from by decide)) (AR i)
lemma riseB {a b} {n} (p : a∈ Area (formG n)) (q : b∈Area (formG n)) : Bose a b ∈ Area (formG n ×ˢ formG n) := Submodule.add_mem _ (Invoice.both p q) (Invoice.both q p)
lemma ARd (i j) : Gder i (arc j)∈Area (formG 1) := cut_G i 0 (AR j)
lemma priorG : SG four ≤ Area (formG 0 ×ˢ formG 0) := image evalTg fun i=>riseB (AR i.val.1) (AR i.val.2)
theorem STG : SG five≤ Area (formG 1 ×ˢ formG 1) := sup_le
    (le_trans priorG (rising (Finset.product_subset_product (growing (by decide)) (growing (by decide))))) (image evalG (fun i=>riseB (AR' i.1) (ARd i.2.2 i.2.1)))
private lemma x_part (M N : ℕ) (h:2=M) (p:1=N) : SX five ≤ Area ((bound M ×ˢ bound M) ×ˢ formG N) := by
  change space evalX≤_; apply image; intro i
  rw [evalX]; apply Invoice.both
  · apply lines (show 0≤M from by omega); exact seeds _
  rw [← p]; exact AR' _
theorem STX : SX five≤ Area ((bound 2 ×ˢ bound 2) ×ˢ formG 1) := x_part 2 1 rfl rfl
end YM.GaugeFieldConstruction.Invoice
