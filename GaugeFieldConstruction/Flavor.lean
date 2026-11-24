import GaugeFieldConstruction.FactorNames
import GaugeFieldConstruction.Orbit

/-!
# Flavor transport. Proper signed permutations on each set of generations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open CF Function Matrix
open scoped BigOperators Matrix
open Matter (Sheet Generation FlavorIndex Slot)

def proper3 : Subgroup Signed where
  carrier := {s|s.perm timeAxis=timeAxis ∧ s.flip timeAxis=false ∧ signBit s=false}
  one_mem' := ⟨rfl,rfl,rfl⟩
  mul_mem' {x y} := fun a b => by
    obtain ⟨p,q,t⟩:=a; obtain ⟨s,u,v⟩:=b
    simp [p,q,t,s,u,v,signBit_mul]
  inv_mem' {a} := fun h=> by
    obtain ⟨b,v,p⟩:=h
    have t : a.perm.symm timeAxis=timeAxis := a.perm.symm_apply_eq.mpr b.symm
    simp [signBit_inv,b,v,p,t]

abbrev Flavor := Bool → proper3
instance : Finite Flavor := inferInstanceAs (Finite (Bool → proper3))

namespace Flavor
variable (g : Flavor) (f : proper3)

private lemma live (i : Generation) : ∃ x : Generation,x.castSucc=f.val.perm i.castSucc := by
  have hv : f.val.perm i.castSucc ≠ Fin.last 3 := by
    change _ ≠ timeAxis; rw [← f.property.1]; exact f.val.perm.injective.ne (Fin.castSucc_ne_last _)
  obtain ⟨x,e⟩ := Fin.eq_castSucc_of_ne_last hv; exact ⟨x,e⟩ -- tune
def leg (i : Generation) := (live f i).choose
lemma cast_leg (i : Generation) : (leg f i).castSucc=f.val.perm i.castSucc := (live f i).choose_spec

lemma leg_one (i : Generation) : leg 1 i=i := Fin.castSucc_inj.mp (cast_leg ..)
lemma leg_mul (s t : proper3) (i : Generation) : leg (s*t) i=leg s (leg t i) := by
  apply Fin.castSucc_inj.mp
  rw [cast_leg,cast_leg,cast_leg]; rfl

def mark (f : proper3) (i : Generation) : Bool := f.val.flip i.castSucc
lemma mark_one (i : Generation) : mark 1 i=false := rfl
lemma mark_mul (s t : proper3) (i : Generation) : mark (s*t) i=(mark s (leg t i)).xor (mark t i) := by
  unfold mark; rw [cast_leg]; rfl

def reprice (i : FlavorIndex) : FlavorIndex := (i.1,leg (g i.1) i.2.1, leg (g i.1) i.2.2)
def bit (i : FlavorIndex) := (mark (g i.1) i.2.1).xor (mark (g i.1) i.2.2)
lemma rise1 (i : FlavorIndex) : reprice 1 i=i := by unfold reprice; simp only [Pi.one_apply,leg_one]
lemma bit1 (i : FlavorIndex) : bit 1 i=false := rfl
lemma rises (h : Flavor) (i : FlavorIndex) : reprice (g*h) i=reprice g (reprice h i) := by simp [reprice,leg_mul]
lemma bit_mul (h : Flavor) (i : FlavorIndex) : bit (g*h) i=(bit g (reprice h i)).xor (bit h i) := by
  simp only [bit,reprice,Pi.mul_apply, mark_mul, Bool.xor_assoc, Bool.xor_left_comm,Bool.xor_comm]

def tagged : Sheet → Bool := Sum.elim (fun _=>true) (fun _=>false)
def sensor (s : Slot) : Slot := (leg (g (tagged s.2)) s.1,s.2)
def sensation (s : Slot) := mark (g (tagged s.2)) s.1

/-! Sensor gives movement on actual primitive sheet matrices. -/
open Matter
lemma both_apply (a b : ℂ) (x y : Sheet) : two a b x y=
    if x=y then if tagged x then a else b else 0 := by
  cases x <;> cases y <;> simp [two,Join.both, tagged, Matrix.one_apply] <;> split_ifs <;> simp_all
lemma wear (p : FlavorIndex → ℂ) (x y : Slot) : coeffs p x y=
    if x.2=y.2 then p (tagged x.2,x.1,y.1) else 0 := by
  rw [show coeffs p x y=two _ _ _ _ from rfl,both_apply]; split_ifs with h' h
  · rw [h]
  · have t : tagged x.2=false := Bool.eq_false_iff.mpr h; rw [t]
  rfl
lemma layer (a b : ℂ) (x : C) (i j : Sheet) : tint a b x i j =
    (if tagged i then a else b)*repX (H x) i j := by
  change (two _ _*_) i j= _; rw [Matrix.mul_apply,Finset.sum_eq_single_of_mem i (Finset.mem_univ _),both_apply,if_pos rfl]
  · rfl
  intro q _ h; rw [both_apply,if_neg (Ne.symm h),zero_mul]
lemma roof (p : FlavorIndex→ℂ) (x y : Slot) (z : C) : costing p z x y=
    p (tagged x.2,x.1,y.1)*repX (H z) x.2 y.2 := by
  rw [show costing p z x y=tint (p (true,x.1,y.1)) (p (false,x.1,y.1)) z _ _ from rfl,layer]
  cases tagged x.2 <;> rfl

theorem case_coeff {p q : FlavorIndex → ℂ} (h : ∀ i,q (reprice g i)=pay (bit g i) (p i)) (x y : Slot) :
    coeffs q (sensor g x) (sensor g y)=pay ((sensation g x).xor (sensation g y)) (coeffs p x y) := by
  rw [wear,wear]; by_cases e:x.2=y.2
  · simp only [sensor,sensation,← e, ↓reduceIte]; exact h (tagged x.2,x.1,y.1)
  simp only [sensor,e,↓reduceIte,pay_zero]
theorem case_cost {p q : FlavorIndex→ℂ} (h : ∀ i,q (reprice g i)=pay (bit g i) (p i)) (x y:Slot) (z : C) :
    costing q z (sensor g x) (sensor g y) = pay ((sensation g x).xor (sensation g y)) (costing p z x y) := by
  rw [roof,roof]; by_cases e : tagged x.2=tagged y.2
  · unfold sensor sensation; simp only [← e]
    change q (g.reprice (tagged x.2,x.1,y.1))*_=pay (bit g (tagged x.2,x.1,y.1)) _
    rw [h]
    cases bit g (tagged x.2,x.1,y.1) <;> simp
  have hp : repX (H z) x.2 y.2=0 := by
    cases X:x.2 <;> cases Y:y.2 <;> first | rfl | (exfalso; apply e; rw [X,Y]; rfl)
  simp [sensor,hp]

-- invariants iff indexed by species sum
private lemma mover (i j : Generation) (h : i≠j) : ∃ f : proper3, leg f i=j := by
  let s := Signed.mirror j.castSucc * unsigned (Equiv.swap i.castSucc j.castSucc)
  have hi := Fin.castSucc_ne_last i; have hj := Fin.castSucc_ne_last j
  have t : s∈proper3 := by
    refine ⟨?_,?_,?_⟩
    · change _ = Fin.last 3; unfold s; simp only [Signed.mul_perm_apply]; change Equiv.swap _ _ _ = _
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj)
    · rw [show s=s from rfl] -- tweak
      unfold s; rw [Signed.mul_flip]
      unfold unsigned Signed.mirror; dsimp only
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj)]; simp; exact hj
    rw [signBit_mul,signBit_swap _ _ (Fin.castSucc_injective .. |>.ne h),signBit_mirror]; rfl
  refine ⟨⟨s,t⟩,Fin.castSucc_inj.mp ?_⟩
  rw [cast_leg]; simp [s,unsigned,Signed.mirror]

private lemma off (i j: Generation) (p : i≠j) : ∃ f : proper3, leg f i=i ∧ leg f j=j ∧
    ((mark f i).xor (mark f j))=true := by
  obtain ⟨l,h,g⟩ : ∃ l:Generation,l≠i∧l≠j := by
    have h:∀ i j:Generation,∃ l:Generation,l≠i∧l≠j:=by decide
    exact h i j
  let a := Signed.mirror i.castSucc* Signed.mirror l.castSucc
  have hm : a∈proper3 := by
    refine ⟨rfl,?_,?_⟩
    · simp only [a,Signed.mul_flip,Signed.mirror,Equiv.refl_apply, timeAxis]
      simp; exact ⟨fun x => False.elim (Fin.castSucc_ne_last i x),fun x=> False.elim (Fin.castSucc_ne_last l x)⟩
    simp [a,signBit_mul]
  let f : proper3 := ⟨a,hm⟩
  exact ⟨f,Fin.castSucc_inj.mp (cast_leg f i), Fin.castSucc_inj.mp (cast_leg f j),by simp [f,a,mark,Signed.mirror,p,h,g,Ne.symm]⟩

variable {A : Type*} [AddCommGroup A] [instM : Module ℂ A]
def bundle_ (a : Bool → A) : FlavorIndex → A := fun i => if i.2.1=i.2.2 then a i.1 else 0
lemma keeps (a : Bool→A) (i : FlavorIndex) : bundle_ a (reprice g i)=pay (bit g i) (bundle_ a i) := by
  obtain ⟨b,c,d⟩:=i
  by_cases e:c=d
  · subst c; simp [bundle_,bit,reprice]
  have t : leg (g b) c ≠ leg (g b) d := fun h=> by
    apply e; apply Fin.castSucc_inj.mp
    apply (g b).val.perm.injective; rw [← cast_leg, ← cast_leg,h]
  simp [t,e,bundle_,reprice]
include instM in
theorem settles (p : FlavorIndex→A) (h : ∀ g : Flavor, ∀ i,p (reprice g i)=pay (bit g i) (p i)) :
    p=bundle_ (fun i=>p (i,0,0)) := by
  funext i; obtain ⟨b,i,j⟩:=i
  by_cases e:i=j
  · subst j; by_cases t:i=0
    · subst i; simp [bundle_]
    obtain ⟨g,hg⟩:= mover i 0 t
    have hp:=h (fun _=> g) (b,i,i); simpa [reprice,hg,bundle_,bit,eq_comm] using hp
  obtain ⟨g,he,hj,ht⟩:= off i j e
  suffices p (b,i,j)=0 by simp [this,bundle_,e]
  have hc:= h (fun _=>g) (b,i,j)
  simp only [reprice,he,hj,bit,ht,pay_true] at hc
  apply (smul_eq_zero.mp (?_ : (2:ℂ) • p (b,i,j)=0)).resolve_left
  · norm_num
  rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp hc
end Flavor
end YM.GaugeFieldConstruction
