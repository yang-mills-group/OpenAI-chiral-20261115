import Organdy.Cygnet

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal



open Sour Swell

open Hive Levier Urn
variable {N:Side} (N':Side)
abbrev twin (T:Shape): Shape:=⟨T.s⁻¹, -T.s⁻¹.act T.t⟩

variable (T:Shape)(b:Bool)

lemma tunnel_choice : Levier.ray (N:=N) b (twin T)=(Levier.ray b T)⁻¹:=by
 apply eq_inv_of_mul_eq_one_right
 -- check order (eq_inv... gives y= inverse x if x*y=1)
 rw [ray_join,Bool.xor_self]
 have h:joinX T (twin T) = incX 1 :=by
    change Shape.mk (T.s*T.s⁻¹) (T.s.act (-T.s⁻¹.act T.t)+T.t)= Shape.mk 1 0
    rw [mul_inv_cancel, Signed.act_neg,Signed.act_inv, neg_add_cancel]
 rw [h];exact gish

lemma double_motion(x:Cover): (twin T).motion (T.motion x)=x:=by
 unfold Shape.motion twin
 dsimp only
 rw [Signed.act_add,← Signed.act_mul,inv_mul_cancel,Signed.act_one]
 rw [two_smul ℕ, two_smul ℕ,Signed.act_add];abel

lemma double_flee (x:Cover): (twin T).flee (T.flee x)=x:=by
 have h: 2 • (twin T).flee (T.flee x)+1= 2 • x +1:=by rw [←Shape.mote,←Shape.mote,double_motion]
 exact nsmul_right_injective (by decide : (2:ℕ)≠0) (add_right_cancel h)


lemma winding_pass (n:Side)(x : Cover) : Lifted.winding n ((T).flee x)=(T).payA (wrap n x)*Lifted.winding n x := by
  let a:= natural (wrap n x); let t:=(T).flee x; let Q:= periods n x; let R:=(T).rent (wrap n x)
  have hp:= (T).vibes (wrap n x); rw [Shape.mill] at hp
  suffices he : periods n t=R+(T.s).act Q by unfold Lifted.winding; change fee (periods n t)=_; rw [he,dues, dueShape]; rfl
  apply nsmul_right_injective (M:=Cover) n.property.ne'; change n.val • _=n.val • _; rw [smul_add, ←show (T.s).act (n.val • Q)= n.val • (T.s).act Q from map_nsmul ((T.s).actEquiv (R:=ℤ)) _ _]
  apply add_left_cancel (a:=natural (wrap n t)); rw [Rush.carrying]
  calc
    _ = (T).flee (a+ n.val • Q) := congrArg ((T).flee) (Rush.carrying n x).symm
    _ = _ := by rw [Shape.flee_p,←add_assoc]; change _=natural _+_+_; congr 1; exact hp.symm

lemma hiddenPay (n:Side)(x:Cover):
 Lifted.winding n x * (twin T).payA (wrap n (T.flee x))= Lifted.winding n (T.flee x):=by
 have h:=winding_pass (twin T) n (T.flee x)
 rw [double_flee] at h
 rw [h, mul_right_comm,Shape.payA,Rush.fee_one,one_mul]

section
variable (U:UNI SpinIdx)
def styleB_U(U:UNI SpinIdx)(T:Shape)(n:Side):=prepU (twin T) U inert n
lemma sunWings (n:Side)(x : Cover) (a : SpinIdx) (b : SU.Slot) :
    acts (styleB_U U T n).val (basisC n x a b) = ∑ j, U.val j a • basisC n ((T).flee x) j b := by
  apply PiLp.ext; rintro ⟨⟨y,j⟩,l⟩; simp_rw [basisC,map_smul,WithLp.ofLp_sum,Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, basis_act,basis_apply]; let v:= wrap n ((T).flee x)
  have hp : Tofu (twin T) n v=wrap n x := by change (twin T).mills n (wrap _ _) = _; rw [Shape.mill,double_flee]
  have hv : (styleB_U U T n).val ((y,j),l) (Lifted.index n x a b) = if y=v then (twin T).payA y*(U.val j a * (1 : Op SU.Slot) l b) else 0 := by
    change jump (Tofu (twin T) n) (fun i'=>(milU (twin T) U inert i').val) (y,j,l) ((wrap n x),a,b)= _; by_cases h:y=v <;> simp only [jump_apply]; rw [if_pos h, if_pos (show Tofu (twin T) n y=_ from h.symm ▸ hp)]; rfl
    rw [if_neg h, if_neg (fun e=> h ((Tofu (twin T) n).injective (e.trans hp.symm)))]
  rw [hv]
  by_cases t:y=v; swap; · rw [if_neg t]; unfold v at t; simp [t,Lifted.index]
  rw [if_pos t]; by_cases p:l=b; swap; · simp [Lifted.index,p]
  subst y l; simp [Lifted.index,v,hiddenPay, ← mul_assoc,mul_comm (a:=Lifted.winding n ((T).flee x))]
end

def drape(U:LinksC):LinksC:= (polarT b) ∘ Lattice.pull T.s (2 • T.t) U
lemma drapeC:Continuous (drape T b):=by
 apply continuous_pi;intro j
 apply (rev_C b).comp
 unfold Lattice.pull Step.read
 split <;> fun_prop
-- analogue of Orientation on cover
variable {S : Finset Cover}
lemma drape_agree {X Y : LinksC} (p : Agrees (S.image (T.motion)) X Y) :
    Agrees S (drape T b X) (drape T b Y) := by
  rintro ⟨x,j⟩ hx ht
  let d:=(posDir j).rotate T.s
  have hh: (T).motion (x+step j)=(T).motion x+d.vec := by rw [Shape.motion_v]; rw [show (T).s.act (step j : Cover)=_ from (Step.vec_rotate (R:=ℤ) (posDir j) T.s).symm]
  let S':=S.image ((T).motion)
  have ha : (T).motion x∈ S':= mem_image_of_mem ((T).motion) hx
  have he : (T).motion x+d.vec∈ S':= hh ▸ mem_image_of_mem ((T).motion) ht
  change polarT b (d.read X _)=polarT b (d.read Y _); apply congrArg (polarT b); cases h:d with|mk a b=>
  rw [h] at he; cases b
  · exact p ((T).motion x,a) ha he
  have hv : (T).motion x-step a ∈ S' := by simpa only [show (⟨a,true⟩ : Lattice.Step)=negDir a from rfl, Lattice.Step.vec_neg,sub_eq_add_neg] using he
  exact congrArg Inv.inv (p ((T).motion x-step a,a) hv (by change _+step a ∈ S'; rw [sub_add_cancel]; exact ha))


lemma drape_seen {n:Side}(U:Pane n):
 onC n (stir (xtra b) T U)=drape T b (onC n U):=by
 funext p; obtain ⟨x,t⟩:=p
 rw [onC_spec]
 change polarT b (((posDir t).rotate T.s).read U (T.anon n (wrap (More n) x)))=
        polarT b (((posDir t).rotate T.s).read (onC n U) (T.motion x))
 apply congrArg (polarT b)
 rw [Shape.anno]
 let d:=((posDir t).rotate T.s)
 let X:=T.motion x
 have he:= travel_at 0 U X [d]
 simpa [X,d,onC,travel] using he.symm

lemma chord_dove{n:Side}(x:Cover)(a:SpinIdx)(j:SU.Slot):
 dove true (basisC n x a j)=basisC n x a j:=by
 rw [basisC,dove_scale,dove_base,cSignX,if_pos rfl]
 unfold Lifted.winding; rw[Rush.fee_real]
