import Bay.Slip
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff

/- H center chosen at a matter node (H as in (105) includes C).
ℂ-linear on scalar expressions. -/
namespace Carol
variable {N:Side}(x: Site N)
def room(s:Signed):Sweep N:=
  let r:Sweep N:=⟨s,0,detX s⟩
  taxiPlus (x-(castX r).mills N x)*r

variable {s t:Signed}
lemma p_s:(room x s).s=s:=one_mul _
lemma p_c:(room x s).charge=detX s:=Bool.false_xor ..
lemma pole(s:Signed):boxA (room x s) (node x)=node x:=by
 unfold room
 rw [←sitV]
 let r:Sweep N:=⟨s,0,detX s⟩
 have h:boxA r (node x)=node ((castX r).mills N x):= ((castX r).nodex x).symm
 rw [h,platforms,add_sub_cancel]
lemma sole{u:Sweep N}
   (e:u.s=s)(h:u.charge=detX s)(w:boxA u (node x)=node x): u=room x s:=by
 have v:(assembly N).embed u.b=(assembly N).embed (room x s).b:= by
   rw[sitA,affine,e] at w
   have H:=pole x s; rw[sitA,affine,p_s] at H
   exact add_left_cancel (w.trans H.symm) -- rewrite s deep
 let r:=room x s
 have H:u.s=r.s:=e.trans (p_s x).symm
 have Q:u.b=r.b:= (assembly N).embed_injective v
 have T:u.charge=r.charge:= h.trans (p_c x).symm
 rw[show u=Sweep.mk u.s u.b u.charge from rfl,H,Q,T]

lemma hall :room x s * room x t=room x (s*t):=by
 apply sole _ 
 · exact congrArg₂ (·*·) (p_s x) (p_s x)
 · rw [det_p]; exact congrArg₂ Bool.xor (p_c x) (p_c x)
 rw [←sitV, pole, pole]

lemma gap (y:Cover):
   boxA (room x s) (node (x+wrap N y)) = node (x+wrap N (s.act y)):=by
 let r:=room x s
 have h:(castX r).mills N x=x:=unaryN (by rw[(castX r).nodex];exact pole ..)
 rw [show boxA _ _= node ((castX r).mills N (x+wrap N y)) from ((castX r).nodex _).symm,Shape.tow,h,show (castX r).s=s from p_s x]

def σ (s:Signed):ℂ:=if detX s then -1 else 1
lemma sig_mul : σ s * σ t=σ (s*t):=by simp only [σ,det_p];cases detX s <;> cases detX t <;>simp
lemma sig_norm (s:Signed):‖σ s‖=1:=by unfold σ;split<;>simp
lemma sig_flip : σ t*σ t=1:=by unfold σ;split<;>simp
lemma sig_re: star (σ s)=σ s:=by unfold σ;split <;>simp


-- pseudoscalar projection on scalar first Pane.
def step (s:Signed) (f:Pane N→ℂ):= f ∘ flashA (room x s)
lemma compose (f:Pane N→ℂ): step x s (step x t f)=step x (s*t) f:=funext fun v=>by
 simp [step,lights,hall]

def count:ℝ := Fintype.card Signed
lemma count_pos:0<count:=Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨1⟩)
def tune(s:Signed):ℂ:=((count⁻¹:ℝ):ℂ)*σ s
lemma tune_norm(s:Signed):‖tune s‖=count⁻¹:=by simp [tune,sig_norm,abs_of_pos count_pos]
lemma tuned_fee : (∑u, ‖tune u‖)=1:=by
 simp_rw[tune_norm];rw [sum_const, nsmul_eq_mul,card_univ]
 exact mul_inv_cancel₀ count_pos.ne'
def hema(x:Site N) (f:Pane N→ℂ):Pane N→ℂ:=∑s:Signed, tune s • step x s f
lemma paints(f:Pane N→ℂ): step x s (hema x f)=σ s • hema x f:=by
 funext v
 let e:=Equiv.mulLeft s
 rw[step, Function.comp_apply, hema,Pi.smul_apply,Finset.sum_apply, Finset.sum_apply, Finset.smul_sum]
 conv_rhs => rw[←Equiv.sum_comp e]

 refine sum_congr rfl fun u _=>?_
 change tune u*step x s (step x u f) v = σ s * (tune (s*u)* step x (s*u) f v)
 rw [compose,tune,tune,←sig_mul]
 generalize hp: (count⁻¹:ℝ)=a
 generalize step x (s*u) f v=b
 linear_combination -(a*σ u*b)*(sig_flip (t:=s)) -- goal lhs-rhs
lemma flash_id (u:Sweep N):flashA u (1:Pane N)=1:=by
 funext i;rw [Skye.flash]; change (xtra u.charge).lens _=1
 rw [show (if u.s.flip i.2 then ((1:Pane N) (lane u i))⁻¹ else (1:Pane N) (lane u i))=1 from by simp]
 exact map_one ..

lemma dead(f:Pane N→ℂ): hema x f 1=0:=by
 have h:=congrFun (paints (s:=Signed.mirror 0) x f) 1
 rw[step, Function.comp_apply,flash_id,Pi.smul_apply,σ, det_t,smul_eq_mul] at h
 simp at h
 exact (mul_eq_zero.mp (show 2*hema x f 1=(0:ℂ) by linear_combination h)).resolve_left two_ne_zero

end Carol
end YM.CF.Bay.D
