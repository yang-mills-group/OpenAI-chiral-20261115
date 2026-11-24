import YM.CF.Buffered.RiseReflect
import YM.CF.Continuum.Current

/-!
# Fixed cover data of the two limits: checking reflection of sites with actual frames
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Lifted
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance
open Window Nacre Spire Scroll Peaks Rush Tulip Skye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
attribute [local instance] opCStarAlgebra

variable (i : Axis) (s : ℤ)
local notation "T" => plane i s
local notation "z" => (2:ℕ) • (s • step i : Cover)
abbrev LinksC := Links ℤ SU.E
abbrev PairsC := LinksC × LinksC
variable (N : Side)
def onC (V : Pane N) : LinksC := expandAt 0 V
def moveC (V : LinksC) := pull (Signed.mirror i) (2 • (s • step i)) V
lemma onC_spec (x : Pane N) (e : Edge Cover) : onC N x e=x (wrap (More N) e.1,e.2) := by rw [onC,expandAt,add_zero]
lemma reflect_onC (V : Pane N) : onC N (fling i s N V) = moveC i s (onC N V) := by
  funext ⟨x,t⟩; rw [onC_spec,fling_eq]; change ((posDir t).rotate (Signed.mirror i)).read V ((T).anon N (wrap (More N) x)) = ((posDir t).rotate (Signed.mirror i)).read _ ((T).motion x); rw [Shape.anno]
  let d:=((posDir t).rotate (Signed.mirror i)); let X:=(T).motion x; have he:= travel_at 0 V X [d]; simpa [X,d,onC, travel] using he.symm
lemma move_cont : Continuous (moveC i s) := by apply continuous_pi; intro j; unfold moveC Lattice.pull Step.read; split <;> fun_prop
lemma on_cont : Continuous (onC N) := by apply continuous_pi; intro j; exact continuous_apply _
-- analogue of Orientation on cover
variable {S : Finset Cover}
lemma moved_agree {X Y : LinksC} (p : Agrees (S.image ((plane i s).motion)) X Y) :
    Agrees S (moveC i s X) (moveC i s Y) := by
  rintro ⟨x,j⟩ hx ht
  let d:=(posDir j).rotate (Signed.mirror i)
  have hh: (T).motion (x+step j)=(T).motion x+d.vec := by rw [Shape.motion_v]; rw [show (T).s.act (step j : Cover)=_ from (Step.vec_rotate (R:=ℤ) (posDir j) (Signed.mirror i)).symm]
  let S':=S.image ((T).motion)
  have ha : (T).motion x∈ S':= mem_image_of_mem ((T).motion) hx
  have he : (T).motion x+d.vec∈ S':= hh ▸ mem_image_of_mem ((T).motion) ht
  change d.read X _=d.read Y _; cases h:d with|mk a b=>
  rw [h] at he; cases b
  · exact p ((T).motion x,a) ha he
  have hv : (T).motion x-step a ∈ S' := by simpa only [show (⟨a,true⟩ : Lattice.Step)=negDir a from rfl, Lattice.Step.vec_neg,sub_eq_add_neg] using he
  exact congrArg Inv.inv (p ((T).motion x-step a,a) hv (by change _+step a ∈ S'; rw [sub_add_cancel]; exact ha))
lemma on_agree {X Y : Pane N} (p : Agrees (S.image (wrap (More N))) X Y) : Agrees S (onC N X) (onC N Y) := by
  rintro ⟨x,j⟩ hx ht; rw [onC_spec,onC_spec]; apply p _ (mem_image_of_mem (wrap _) hx); have he:= mem_image_of_mem (wrap (More N)) (show x+step j∈ S from ht); rw [map_add,wrap_step] at he; exact he

def winding (x : Cover) := Rush.fee (periods N x)
def index (x : Cover) (a : SpinIdx) (b : Slot) : Single N := ((wrap N x,a),b)
def basisC (x : Cover) (a : SpinIdx) (b : Slot) := winding N x • basisKet (index N x a b)
def nodeC (x : Cover) := (2:ℕ) • x + 1
lemma node_of (x : Cover) : node (wrap N x)=wrap (More N) (nodeC x) := by
  unfold node nodeC; rw [map_add,Ratio.root_embed,Ratio.embed_wrap,show wrap (More N) 1=1 from funext fun t=> Int.cast_one]; rfl
lemma flee_pos (x : Cover) (a : Axis): (T).flee x a=if i=a then -x a + s-1 else x a:=by
  have ht:=congr_fun ((T).mote x) a; rw [fling_move] at ht; by_cases h:i=a <;> simp [h,two_smul] at ht ⊢ <;> omega
lemma flee_twice (x : Cover) : (T).flee ((T).flee x)=x:=by
  funext t; by_cases h:i=t <;> simp_rw [flee_pos]; all_goals simp [h]
  ring

lemma winding_move (x : Cover) : winding N ((T).flee x)=(T).payA (wrap N x)*winding N x := by
  let a:= natural (wrap N x); let t:=(T).flee x; let Q:= periods N x; let R:=(T).rent (wrap N x)
  have hp:= (T).vibes (wrap N x); rw [Shape.mill] at hp
  suffices he : periods N t=R+(Signed.mirror i).act Q by unfold winding; change fee (periods N t)=_; rw [he,dues, dueShape]; rfl
  apply nsmul_right_injective (M:=Cover) N.property.ne'; change N.val • _=N.val • _; rw [smul_add, ←show (Signed.mirror i).act (N.val • Q)= N.val • (Signed.mirror i).act Q from map_nsmul ((Signed.mirror i).actEquiv (R:=ℤ)) _ _]
  apply add_left_cancel (a:=natural (wrap N t)); rw [Rush.carrying]
  calc
    _ = (T).flee (a+ N.val • Q) := congrArg ((T).flee) (Rush.carrying N x).symm
    _ = _ := by rw [Shape.flee_p,←add_assoc]; change _=natural _+_+_; congr 1; exact hp.symm
lemma winding_frame (x : Cover) : winding N x * (T).payA (wrap N ((T).flee x))=winding N ((T).flee x) := by
  nth_rw 1 [← flee_twice i s x, winding_move i s N ((T).flee x)]; rw [mul_right_comm,Shape.reflex, one_mul]

lemma acted_basisC (x : Cover) (a : SpinIdx) (b : Slot) :
    acts (carR i s N).val (basisC N x a b) = ∑ j, pin i j a • basisC N ((plane i s).flee x) j b := by
  apply PiLp.ext; rintro ⟨⟨y,j⟩,l⟩; simp_rw [basisC,map_smul,WithLp.ofLp_sum,Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, basis_act,basis_apply]; let v:= wrap N ((T).flee x)
  have hp : Tofu T N v=wrap N x := by change (T).mills N v= _; rw [show v= _ from (Shape.mill T x).symm, matter_invol]
  have hv : (carR i s N).val ((y,j),l) (index N x a b) = if y=v then (T).payA y*(pin i j a * (1 : Op Slot) l b) else 0 := by
    change jump (Tofu T N) (fun i'=>(milU T (pinLift i) inert i').val) (y,j,l) ((wrap N x),a,b)= _; by_cases h:y=v <;> simp only [jump_apply]; rw [if_pos h, if_pos (show Tofu T N y=_ from h.symm ▸ hp)]; rfl
    rw [if_neg h, if_neg (fun e=> h ((Tofu T N).injective (e.trans hp.symm)))]
  rw [hv]
  by_cases t:y=v; swap; · rw [if_neg t]; unfold v at t; simp [t,index]
  rw [if_pos t]; by_cases p:l=b; swap; · simp [index,p]
  subst y l; simp [index,v,winding_frame, ← mul_assoc,mul_comm (a:=winding N ((T).flee x))]
lemma flips_basisC (x : Cover) (a : SpinIdx) (b : Slot) :
    theta (carR i s N) (create (basisC N x a b)) = (-Complex.I) • Fock.remove (∑ j, pin i j a • basisC N ((T).flee x) j b) ∧
    theta (carR i s N) (Fock.remove (basisC N x a b)) = Complex.I • create (∑ j, pin i j a • basisC N ((T).flee x) j b) := by rw [theta_upV,theta_downV, acted_basisC]; trivial

lemma gaugeSquare (g : Seat N→E) : carR i s N * tradew N (g ∘ (plane i s).anon N)=tradew N g * carR i s N := by
  unfold carR; rw [envoy]; exact congrArg (fun g=> _ * _) (show g ∘ (T).anon N ∘ (T).anon N=g from funext fun x=>congrArg g (fling_there ..))
end YM.CF.Buffered.Lifted
