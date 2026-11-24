import GaugeFieldConstruction.TurnMaxwell
import GaugeFieldConstruction.TurnWeyl

/-!
# Covariance certificate on the evaluation classes of the U1 rows
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Finset Function Matrix
open scoped BigOperators Matrix
namespace Cauchy.Row
open Raw
variable {α β γ : Type*}

def tester_g (w : Maxwell × Maxwell) := productRead w.1.read w.2.read
def tester_f (w : Weyl false × Weyl true) := productRead w.1.read w.2.read
def tester_x (w : (Weyl false × Weyl true) × Maxwell) := productRead (tester_f w.1) w.2.read

theorem paymul {K : Type*} [Ring K] (a b : K) (p q : Bool) : pay p a*pay q b=pay (p.xor q) (a*b) := by
  cases p <;> cases q <;> simp

/-- A row with off-center (wave) tests. `poses` gives how the test moves;
we only use it one way (all post-, some pre-evaluation).
Translation natural across these costs, *on the jets after shell relations*. -/
structure Record (X W : Type*) where
  tester : W → J X →ₗ[ℂ] ℂ
  faith : DeterminedBy tester
  poses : Signed → W → W → Prop -- Args g, test after, test before
  permit (s : Signed) (w : W) : ∃ u, poses s w u
  P : Axis → Module.End ℂ (J X)
  momentum : W → P4
  bond (w : W) (k : Axis) : tester w ∘ₗ P k = momentum w k • tester w
  frequency {s : Signed} {w u : W} (h : poses s w u) (i : Axis) :
    momentum u i = pay (s.flip i) (momentum w (s.perm i))

def recG : Record g (Maxwell×Maxwell) where
  tester:=tester_g
  faith X h:=chart_g _ (fun ⟨i,j⟩ => h (i.1.val.face i.2,j.1.val.face j.2))
  poses s w a:=a.1=(Maxwell.still s w.1).point ∧ a.2=(Maxwell.still s w.2).point
  permit s w:=⟨((Maxwell.still s w.1).point,(Maxwell.still s w.2).point),rfl,rfl⟩
  P:=P_g
  momentum w i:= w.1.p i+w.2.p i
  bond w i:= ge_charge i w.1 w.2
  frequency {s w u} h i:=by rw [h.1,h.2]; exact (by
    change s⁻¹.act w.1.p i + s⁻¹.act w.2.p i = _; rw [return_p,return_p,pay_add])

def ferm (extra : Bool) : Record f (Weyl false × Weyl true) where
  tester:=tester_f
  faith X h:=chart_f _ (fun ⟨i,j⟩ => h (i.val.fermi false,j.val.fermi true))
  poses s w t:= BoundsCR s extra w.1 w.2 t.1 t.2
  permit s w:=by obtain ⟨c,r,h⟩ := costCR s w.1 w.2 extra; exact ⟨(c,r),h⟩
  P:=P_f
  momentum w i:=w.1.p i+w.2.p i
  bond w i:=ph_charge i w.1 w.2
  frequency {s w u} h i:=by rw [h.cr,h.ct, return_p,return_p,pay_add]; cases signBit s <;> simp [add_comm]

def recX : Record x ((Weyl false × Weyl true) × Maxwell) where
  tester:=tester_x
  faith X h:=chart_x _ (fun ⟨⟨i,j⟩,v⟩ => h ((i.val.fermi false,j.val.fermi true),v.1.val.face v.2))
  poses s w u:= BoundsCR s false w.1.1 w.1.2 u.1.1 u.1.2 ∧ u.2=(Maxwell.still s w.2).point
  permit s w:=by
    obtain ⟨c,r,h⟩ := costCR s w.1.1 w.1.2 false; exact ⟨((c,r),_),h,rfl⟩
  P:=P_x
  momentum w i:=(ferm false).momentum w.1 i+w.2.p i
  bond w i:= x_charge i w.1.1 w.1.2 w.2
  frequency {s w u} h i:=by
    rw [(ferm false).frequency (w:=w.1) (u:=u.1) h.1,h.2,pay_add]
    congr 1
    exact return_p ..
namespace Record
variable {X KP : Type*} (R : Record X KP)
/-- Evaluation kernel admits invariant quotient using just these rotations.
Also identifies the raw permutations on evaluation costs. -/
structure Reading (A : Labels α) (q : α → J X) : Prop where
  moving (s : Signed) (w u) (h : R.poses s w u) (i : α) :
    R.tester u (q i) = pay (A.cost s i) (R.tester w (q (A.move s i)))
lemma transl (i : Axis) (a) (u : KP) :
    R.tester u (R.P i a) = R.momentum u i * R.tester u a := LinearMap.congr_fun (R.bond u i) a

lemma atP (i : Axis) (a b : J X) (s : Signed) (w u : KP) (h : R.poses s w u)
    (e : Bool) (k : R.tester u a=pay e (R.tester w b)) :
    R.tester u (R.P i a)=pay (e.xor (s.flip i)) (R.tester w (R.P (s.perm i) b)) := by
  rw [R.transl,R.transl,k,R.frequency h, Row.paymul,Bool.xor_comm e]
end Record

lemma bose_charge (r : J GIndex →ₗ[ℂ] ℂ) (s : J GIndex →ₗ[ℂ] ℂ) (x y : J GIndex) :
    productRead r s (Bose x y) = r x*s y + r y*s x := by rw [Bose,map_add,read_times,read_times]
lemma bose_swap (x y : J GIndex) : Bose x y = Bose y x := add_comm ..

lemma readingTg : recG.Reading g4Act evalTg := by
  constructor
  intro s w u h i
  change productRead u.1.read u.2.read _=pay _ (productRead _ _ _)
  rw [show u.1=_ from h.1,show u.2=_ from h.2]
  -- sorted symmetry (use evaluation after sorting too)
  have hx (a b : Wed) : evalTg (ordered a b)=Bose (arc a) (arc b) := by
    unfold ordered; split; exact bose_swap ..; rfl
  dsimp only [g4Act]
  rw [Labels.sym_mv,hx,evalTg,bose_charge,bose_charge,Labels.sym_fee,pay_add]
  rw [Maxwell.turns, Maxwell.turns, Maxwell.turns,Maxwell.turns, Row.paymul,Row.paymul, Bool.xor_comm (wedAct.cost _ i.val.2)]
lemma readingG : recG.Reading g5Act evalG := by
  constructor
  rintro s w u h ⟨i,j,k⟩
  change productRead u.1.read u.2.read _=pay ((wedAct.cost s i).xor ((wedAct.cost s j).xor (s.flip k)))
    (productRead w.1.read w.2.read (evalG (wedAct.move s i,wedAct.move s j,s.perm k)))
  rw [show u.1=_ from h.1,show u.2=_ from h.2]
  have he (u : Maxwell) (i : Axis) (x : J GIndex) : u.read (Gder i x)=u.p i*u.read x :=
    LinearMap.congr_fun (u.frequency i) x
  simp only [evalG,bose_charge,he,Maxwell.turns]
  dsimp only [Maxwell.Bianchi.point]
  repeat rw [return_p]
  simp only [Row.paymul,pay_add,Bool.xor_left_comm,Bool.xor_comm,Bool.xor_assoc]

lemma readingX : recX.Reading x5Act evalX := by
  constructor
  rintro s w u h ⟨i,j⟩
  change productRead (tester_f u.1) u.2.read _=pay ((s.flip i).xor (wedAct.cost s j))
    (productRead (tester_f w.1) w.2.read (evalX (s.perm i,wedAct.move s j)))
  rw [show u.2=_ from h.2]
  dsimp only [evalX,tester_f]
  rw [read_times,read_times,Maxwell.turns,h.1.tax]
  simp only [Bool.and_false,Bool.false_xor,Row.paymul]

lemma readingB : (ferm true).Reading f3Act B := by
  constructor
  intro s w u h i
  change tester_f u (B i) = pay ((signBit s).xor (s.flip i)) (tester_f w (B (s.perm i)))
  exact (by simpa only [Bool.and_true] using
    (show tester_f u (B i)=pay ((signBit s && true).xor (s.flip i)) (tester_f w (B (s.perm i))) from h.tax i))
lemma atL (s : Signed) (w u) (h : (ferm true).poses s w u) (a b : J f) (e : Bool) (i : Axis)
    (p : tester_f u a=pay e (tester_f w b)) : tester_f u (L i a)=
    pay (e.xor (f3Act.cost s i)) (tester_f w (L (s.perm i) b)) := by
  have he (j) (x : J f) (v : Weyl false × Weyl true) :
      tester_f v (L j x)= (v.2.p j - v.1.p j)*tester_f v x := LinearMap.congr_fun (l_charge j v.1 v.2) x
  rw [he,he,p,h.cr,h.ct,return_p,return_p]
  dsimp only [f3Act, Labels.twist,Raw.v]
  cases signBit s <;> cases s.flip i <;> cases e <;>
    simp <;> ring_nf <;> simp
lemma readingTf : (ferm true).Reading f4Act evalTf := by
  constructor
  rintro s w u h ⟨i,a|b⟩
  · exact atL s w u h _ _ _ a (readingB.moving s w u h i)
  exact (ferm true).atP b _ _ _ w u h _ (readingB.moving s w u h i)
lemma readingF : (ferm true).Reading f5Act evalF := by
  constructor
  rintro s w u h ⟨i,a|b|⟨j,r⟩⟩
  · have he := atL s w u h (evalTf (i,Sum.inl a.val.2)) (evalTf (s.perm i,Sum.inl (s.perm a.val.2)))
      ((f3Act.cost s i).xor (f3Act.cost s a.val.2)) a.val.1 (readingTf.moving s w u h (i,Sum.inl a.val.2))
    change _ = pay ((f3Act.cost s i).xor ((f3Act.cost s a.val.1).xor (f3Act.cost s a.val.2)))
      (tester_f w (evalF (s.perm i,Sum.inl (ordered _ _))))
    rw [eval_LL, Bool.xor_comm (f3Act.cost s a.val.1),← Bool.xor_assoc]
    exact he
  · have he := (ferm true).atP b.val.1 (evalTf (i,Sum.inr b.val.2)) (evalTf (s.perm i, Sum.inr (s.perm b.val.2)))
      s w u h ((f3Act.cost s i).xor (s.flip b.val.2)) (readingTf.moving s w u h (i,Sum.inr b.val.2))
    change _ = pay ((f3Act.cost s i).xor ((s.flip b.val.1).xor (s.flip b.val.2)))
      (tester_f w (evalF (s.perm i,Sum.inr (Sum.inl (ordered _ _)))))
    rw [eval_SS, Bool.xor_comm (s.flip b.val.1),← Bool.xor_assoc]
    exact he
  have he := (ferm true).atP j (evalTf (i, Sum.inl r)) (evalTf (s.perm i, Sum.inl (s.perm r)))
    s w u h ((f3Act.cost s i).xor (f3Act.cost s r)) (readingTf.moving s w u h (i,Sum.inl r))
  change _ = pay ((f3Act.cost s i).xor ((s.flip j).xor (f3Act.cost s r))) _
  rw [Bool.xor_comm (s.flip j),← Bool.xor_assoc]; exact he
end Cauchy.Row
end YM.GaugeFieldConstruction
