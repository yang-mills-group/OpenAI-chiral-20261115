import Zephyr.Chern.Lint
import YM.CF.Scroll.Mug
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology YM.CF YM.CF.Tulip YM.CF.Cube YM.CF.Lat YM.CF.Rush YM.Laurent YM.CF.Scroll 

open scoped Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra


variable {N:Side}

def drag (d:Cover):Shape := ⟨1,d⟩

lemma drag_flee (d x:Cover): (drag d).flee x=x+d:=by
  have e := (drag d).mote x
  simp only [Shape.motion,drag,Signed.act_one] at e
  rw [add_right_comm] at e
  have h: (2:ℕ) • (drag d).flee x=(2:ℕ) • (x+d):=by
    rw [smul_add]; exact (add_right_cancel e).symm
  exact nsmul_right_injective (by decide) h

lemma drag_flag (d x:Cover):
    flag N x*(drag d).payA (wrap N x)=flag N (x+d) := by
  have h : periods N x+(drag d).rent (wrap N x)= periods N (x+d):=by
    have hx:= (drag d).vibes (wrap N x)
    rw [Shape.mill,drag_flee,drag_flee] at hx
    apply nsmul_right_injective (M:=Cover) N.prop.ne'
    change N.val • _=N.val • periods N (x+d)
    rw [smul_add]
    linear_combination (norm:=abel) carrying N x+hx-carrying N (x+d)
  rw [flag,flag,Shape.payA,←dues,h]

lemma sings_one {κ:Type} [Fintype κ] [DecidableEq κ] (A:Op κ):
    sings false 1 A=A:=by
  change twist (1:UNI κ) A=A
  rw [twist_formula]
  change (1:Op κ)*A*star 1=A
  simp

def idleC : ColorT false where
  lens:=MulEquiv.refl _
  V:=1
  X:=IsometryEquiv.refl _
  trek _ _:=rfl
  shore g:= (sings_one _).symm
  born _ _:=rfl
  facing x := by
    change _=Fock.congrC (1:UNI _) _
    unfold Fock.congrC
    simp
    rfl

lemma drag_jet (d:Cover) : JetS (drag d).s false false 1 := by
  constructor
  · intro i
    rw [sings_one];rfl
  · rw [sings_one];rfl
  change 1*_=_* cc 1;rw [one_mul,cc_one,mul_one]

def Tugs (d:Cover)(N:Side) := prepU (drag d) 1 idleC N

lemma tug_entry (d x:Cover)(i:IS)(k:Single N):
    (Tugs d N).val (tag N x i) k= if tag N (x+d) i=k then (drag d).payA (wrap N x) else 0:=by
  rcases k with ⟨⟨y,j⟩,w⟩
  have h(x:Site N):(milU (drag d) 1 idleC x).val= (drag d).payA x • (1:Op IS):=by
    change _ • ((1:Op SpinIdx) ⊗ₖ (1:Op SU.Slot))=_
    rw [Matrix.one_kronecker_one]
  change jump (Tofu (drag d) N) (fun y=>(milU (drag d) 1 idleC y).val)
    (wrap N x,i) (y,j,w)=_
  have t:Tofu (drag d) N (wrap N x) = wrap N (x+d):= by
    change (drag d).mills _ _=_
    rw [Shape.mill,drag_flee]
  rw [jump_apply,t,h,Matrix.smul_apply,smul_eq_mul]
  rcases i with ⟨l,v⟩
  simp [tag,Matrix.one_apply,ite_and]

lemma tug_lint (P:Op (Single N))(d x y:Cover)(i j:IS):
    lint (sings false (Tugs d N) P) x y i j=lint P (x+d) (y+d) i j:=by
  change lint (twist _ P) _ _ _ _=_
  simp only [lint,twist_formula,Matrix.mul_apply,Matrix.star_apply,tug_entry]
  -- collapse inner
  simp_rw [ite_mul,zero_mul]
  simp
  have e(k:Single N):starRingEnd ℂ (if tag N (y+d) j=k then (drag d).payA (wrap N y) else 0)=
      if tag N (y+d) j=k then (drag d).payA (wrap N y) else 0 := by
    split; exact Shape.real_payA ..;exact map_zero _
  simp [e,mul_ite]
  rw [←drag_flag,←drag_flag]
  ring

lemma petals_trans (z:Cover)(t:ℝ):
    petals (transA N z) t = stir idleC (drag (-z)) (petals (stream N) t) := by
  funext i
  rcases i with ⟨x,a⟩
  let v:=petals (stream N) t
  have h: stir idleC (drag (-z)) v (x,a)= v
      (x+wrap _ ((2:ℕ) • -z),a):=by
    simp [stir,Lattice.pull,drag,idleC,affine] -- tune
  exact h.symm

/-- Eventual translation of jets, with NO uniform assumption on plaque qualifications
of links at nonzero angle. -/
def Down (F:Oil N) := ∀ z x i j,
  tuft F (stream N) (-x-z) (-z) i j = tuft F (transA N z) (-x) 0 i j

lemma down (s:ℕ)(h:1≤s) :
    ∃ v:ℕ, ∀ (N:Side), v≤N.val → ∀ (M:Male), Down (funde s M N):=by
  obtain ⟨e,p,v,H⟩:=radiance s h
  refine ⟨v,?_⟩
  intro N n M z x i j
  apply bud_congr
  filter_upwards [petals_safe (stream N) p] with t q
  have y:= funde_f (drag (-z)) idleC 1 (drag_jet _) _ s h M e (H N n) q
  change sings false (Tugs (-z) N) (funde s M N (profile _)) = funde s M N (profile (stir _ _ _)) at y
  rw [←petals_trans] at y
  simp only [tap,←y,tug_lint,zero_add,sub_eq_add_neg]
