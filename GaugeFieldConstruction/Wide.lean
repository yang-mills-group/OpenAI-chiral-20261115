import GaugeFieldConstruction.Movers
/-!
# Raw tensor presentations (unsorted, include zeroes)
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Stage.Wide
open Cauchy Row Record Phys Function Submodule Finset U1
open Cell Flux One
open Raw (Wed)
open scoped BigOperators

abbrev W := Axis × Axis
abbrev GE:= W × W
abbrev G1:= W × (W×Axis)
abbrev PH:=Axis
abbrev T1:=Raw.F4 -- S, L'
abbrev T2:= Axis × (W ⊕ W ⊕ W)
abbrev MX:=Axis×W

def sheet (i : W) := F i.1 i.2
def page (i : GE):=Bose (sheet i.1) (sheet i.2)
def pageV (i : G1):=Bose (sheet i.1) (Gder i.2.2 (sheet i.2.1))
def foldP (i : T2) := i.2.elim (fun j : W=> L j.1 (L j.2 (B i.1))) (fun x=>x.elim (fun j:W=>P_f j.1 (P_f j.2 (B i.1))) (fun j:W=> P_f j.1 (L j.2 (B i.1))))
def log (i : MX) := times' (B i.1) (sheet i.2)

def leaves : Labels W:= Raw.v.tensorProd Raw.v
def leaf4 : Labels GE:= leaves.tensorProd leaves
def leaf5 : Labels G1:= leaves.tensorProd (leaves.tensorProd Raw.v)
def reeds : Labels W:= Raw.f3Act.tensorProd Raw.f3Act
def stem5 : Labels T2:= Raw.f3Act.tensorProd (reeds.directSum (leaves.directSum (Raw.v.tensorProd Raw.f3Act)))
def horse:=Raw.v.tensorProd leaves

lemma pull (p : Signed) (a : Maxwell) (i j : Axis): (Maxwell.still p a).point.read (F i j) = pay ((p.flip i).xor (p.flip j)) (a.read (F (p.perm i) (p.perm j))) := by
  rw [Maxwell.read_F,Maxwell.read_F]; simp only [power,Prod.fst_zero,Prod.snd_zero,pow_zero,mul_one]; exact (Maxwell.still p a).create ..
lemma mark (s : Signed) (u : Maxwell) (i: W): (Maxwell.still s u).point.read (sheet i)=pay (leaves.cost s i) (u.read (sheet (leaves.move s i))) := pull ..
lemma leafR : recG.Reading leaf4 page := by
  constructor
  rintro s w u t ⟨a,b⟩
  change productRead u.1.read u.2.read _=pay ((leaves.cost s a).xor (leaves.cost s b)) (productRead w.1.read w.2.read (page (leaves.move s a,leaves.move s b)))
  rw [show u.1=_ from t.1, show u.2=_ from t.2]; simp only [page,bose_charge,Stage.Wide.mark, Row.paymul,pay_add, Bool.xor_comm]
lemma leafV : recG.Reading leaf5 pageV := by
  constructor
  rintro s w u t ⟨a,b,c⟩
  change productRead u.1.read u.2.read _=pay ((leaves.cost s a).xor ((leaves.cost s b).xor (s.flip c))) (productRead w.1.read w.2.read (pageV (leaves.move s a,leaves.move s b,s.perm c)))
  rw [show u.1=_ from t.1, show u.2=_ from t.2]
  have he (u:Maxwell) i d:u.read (Gder i d)=u.p i*u.read d:= LinearMap.congr_fun (u.frequency i) d
  simp only [pageV,bose_charge,he, Stage.Wide.mark]; dsimp only [Maxwell.Bianchi.point]; repeat rw [return_p]
  simp only [paymul,pay_add, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
lemma stem : ph.Reading stem5 foldP := by
  constructor
  rintro s w u h ⟨i,a|b|v⟩
  · change tester_f u _= pay ((Raw.f3Act.cost s i).xor ((Raw.f3Act.cost s a.1).xor (Raw.f3Act.cost s a.2))) (tester_f w _)
    rw [Bool.xor_comm (Raw.f3Act.cost s a.1),← Bool.xor_assoc]; exact atL s w u h (evalTf (i,Sum.inl a.2)) (evalTf (s.perm i,Sum.inl (s.perm a.2))) ((Raw.f3Act.cost s i).xor (Raw.f3Act.cost s a.2)) a.1 (readingTf.moving s w u h _)
  · change ph.tester u _=pay ((Raw.f3Act.cost s i).xor ((s.flip b.1).xor (s.flip b.2))) (ph.tester w _)
    rw [Bool.xor_comm (s.flip b.1), ← Bool.xor_assoc]; exact ph.atP b.1 (evalTf (i,Sum.inr b.2)) (evalTf (s.perm i,Sum.inr (s.perm b.2))) s w u h ((Raw.f3Act.cost s i).xor (s.flip b.2)) (readingTf.moving s w u h _)
  exact readingF.moving s w u h (i,Sum.inr (Sum.inr v))
lemma X_stamp : recX.Reading horse log:=by
  constructor
  rintro s w u h ⟨a,b⟩
  change productRead (tester_f u.1) u.2.read _=pay ((s.flip a).xor (leaves.cost s b)) (productRead (tester_f w.1) w.2.read (times' (B (s.perm a)) (sheet (leaves.move s b))))
  rw [show u.2=_ from h.2]; dsimp only [log,tester_f]; simp only [read_times,mark,h.1.tax,Bool.and_false,Bool.false_xor,Row.paymul]

-- mapping into the grade submodule
lemma grade4g (r : GE) : page r∈ space evalTg := by
  rcases r with ⟨⟨a,b⟩,c,d⟩
  change Bose (F a b) (F c d) ∈_
  have he i j : Bose (arc i) (arc j)∈space evalTg := by
    rw [space, Fintype.range_linearCombination]; apply subset_span; refine ⟨ordered i j,?_⟩; unfold ordered; split; exact bose_swap ..; rfl
  rcases lt_trichotomy a b with u|u|u <;> rcases lt_trichotomy c d with v|v|v
  · exact he (Wed.mk _ _ u) (Wed.mk _ _ v)
  · rw [v,Gauge97.zero_angle]; simp [Bose]
  · skip
    -- adjust
    rw [Gauge97.turnover c d]
    have H: Bose (F a b) (-F d c) = -Bose (F a b) (F d c) := by simp only [Bose,map_neg,LinearMap.neg_apply,neg_add]
    rw [H]; exact Submodule.neg_mem _ (he (Wed.mk _ _ u) (Wed.mk _ _ v))
  · rw [u,Gauge97.zero_angle]; simp [Bose]
  · rw [u,Gauge97.zero_angle]; simp [Bose]
  · rw [u,Gauge97.zero_angle]; simp [Bose]
  · rw [Gauge97.turnover a b]; rw [show Bose (-F b a) (F c d) = -Bose (F b a) (F c d) from by simp only [Bose,map_neg,LinearMap.neg_apply,neg_add]]; exact Submodule.neg_mem _ (he (Wed.mk _ _ u) (Wed.mk _ _ v))
  · rw [v,Gauge97.zero_angle]; simp [Bose]
  conv_rhs => lhs; rw [Gauge97.turnover a b]
  conv_rhs => rhs; rw [Gauge97.turnover c d]
  rw [show Bose (-F b a) (-F d c) = Bose (F b a) (F d c) from by simp [Bose]]; exact he (Wed.mk _ _ u) (Wed.mk _ _ v)
-- efficient linear `arc` membership for F as any map after Bose
lemma spill {X : Type*} [AddCommGroup X] [Module ℂ X] (A : GJet →ₗ[ℂ] X) (U : Submodule ℂ X) (p : ∀ i,A (arc i)∈U) (i : W) : A (sheet i)∈U := by
  rcases i with ⟨i,j⟩; rcases lt_trichotomy i j with e|e|e
  · exact p (Wed.mk _ _ e)
  · subst i; simp [sheet,Gauge97.zero_angle]
  change A (F i j)∈ _; rw [Gauge97.turnover i j,map_neg]; exact Submodule.neg_mem _ (p (Wed.mk _ _ e))
lemma range_sets {α β : Type*} [Fintype α] (q : α→ J β) (i : α): q i∈space q := by rw [space,Fintype.range_linearCombination]; exact subset_span ⟨i,rfl⟩
lemma grade5g (r : G1): pageV r∈ space evalG := by
  let D : GJet →ₗ[ℂ] GJet →ₗ[ℂ] J g := times'+times'.flip
  rcases r with ⟨x,y,c⟩
  apply spill (D.flip (Gder c (sheet y))) _ _ x
  intro i; exact spill (D (arc i) ∘ₗ Gder c) _ (fun j=> range_sets evalG (i,j,c)) y
lemma grade5X (r:MX): log r∈ space evalX:= spill (times' (B r.1)) _ (fun i=>range_sets evalX (r.1,i)) _
lemma grade5F (i:T2): foldP i∈space evalF := by
  rcases i with ⟨i,p|p|q⟩
  · change L p.1 (evalTf (i,.inl p.2))∈_; rw [← eval_LL]; exact range_sets evalF _
  · change P_f p.1 (evalTf (i,.inr p.2))∈_; rw [← eval_SS]; exact range_sets evalF _
  exact range_sets evalF (i,Sum.inr (Sum.inr q))
lemma pagesG : space page=space evalTg := le_antisymm (Invoice.image page grade4g) (Invoice.image evalTg fun j=>range_sets page (j.val.1.toBlade.val,j.val.2.toBlade.val))
lemma pagesH : space pageV=space evalG := le_antisymm (Invoice.image pageV grade5g) (Invoice.image evalG (fun j=>range_sets pageV (j.1.toBlade.val,j.2.1.toBlade.val,j.2.2)))
lemma pagesF : space foldP=space evalF := le_antisymm (Invoice.image foldP grade5F) <| Invoice.image evalF fun j=>by
  rcases j with ⟨j,p|p|v⟩
  · exact range_sets foldP (j,Sum.inl p.val)
  · exact range_sets foldP (j,Sum.inr (Sum.inl p.val))
  exact range_sets foldP (j,Sum.inr (Sum.inr v))
lemma pagesX : space log=space evalX:= le_antisymm (Invoice.image log grade5X) (Invoice.image evalX (fun i=>range_sets log (i.1,i.2.toBlade.val)))
end YM.GaugeFieldConstruction.Stage.Wide
