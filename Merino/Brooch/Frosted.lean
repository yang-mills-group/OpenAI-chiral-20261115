import Merino.Brooch.Seal
import YM.SU5.Exchange.Pipe.Raw

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Brooch
open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier
variable {N:Side}
local notation "Jk"=> Single N

variable {o:Seat N}{A B:SOp N}{a b d z:ℝ}

lemma hare (p:Soak o A a b d):Soak o (pale A) a b d:=by
 obtain ⟨F,C,h,t,u,r⟩:=p
 let X:=Openc (More N) d
 let f:↥X→↥X:=fun x=>⟨ice x.val, ice_o x.val d x.property⟩
 let v:=forum N d
 have hv: Continuous f:=(burnOut.comp continuous_subtype_val).subtype_mk _
 have hF(S):Suite (badge _) (bail N d) (bail N d) S (fun i j=>C S j i)
       (fun x=>star (F S (f x))):=by
    refine ⟨?_,?_⟩
    · have hx:Ticket (bail N d) (bail N d) S (C S) (fun x=>F S (f x)):=by
       refine ⟨?_,?_⟩
       · have e(g:Seat N→SU.E)(y:↥X):f (v.drive g y)=v.drive g (f y):=Subtype.ext (icy_g ..)
         intro i x; change F S (f (v.drive i x)) * _ = _; rw [e]; exact (h S).frame ..


       intro i j
       have hq(x y):v.eval S (f x) (f y)=v.eval S x y:= congrArg (· / |d|) (ice_f _ _ _)
       have H:=(h S).expo i j
       exact ⟨H.positive,H.triggered,fun x=>H.bounded (f x),fun x y=>by rw [←hq]; exact H.variation ..,H.connected.comp hv⟩
      exact hx.starT
    exact fun i j=> realigns ((h S).fuel j i) f fun V e γ p=> snowy e (fun z=>(γ z).val) p
 refine ⟨_,_,hF,fun i x=>by rw [t _ x]; rfl,?_,?_⟩
 · refine le_trans ?_ u
   refine sum_le_sum fun i _=>le_of_eq ?_
   congr 1
   exact Finset.sum_comm
 intro x; change star (A (f x).val)=_
 rw [r,star_sum]


variable (s:Sweep N)
abbrev actSpin := Sour.γS s⁻¹
abbrev actB := (s⁻¹).charge
abbrev actR := detX (s⁻¹).s -- adjust
def icyPose (A:SOp N):SOp N:=
  if actR s then pale (julStep s A) else julStep s A
lemma icy_purchase (p:Soak o A a b d):
   Soak (boxA s o) (icyPose s A) a (Tenant.quota^2*b) d:=by
 have hx:=jul_sells s p
 unfold icyPose; split; exact hare hx; exact hx
lemma icy_equation (V:Pane N):
  icyPose s A (profile V)=form (actB s) (actR s) (actSpin s) (A (profile (flashA s V))):=by
  have hh:julStep s A (profile V)=sings (actB s) (actSpin s) (A (profile (flashA s V))):=by
     unfold flashA julStep; rw [Levier.veil_p]
  unfold icyPose form; split
  · rw [Tulip.pale,ice_pr,hh]
  exact hh


lemma icy_fixed (W:Op Jk):
  icyPose s (fun _=> W) = (fun _=>form (actB s) (actR s) (actSpin s) W):=by
  funext x; unfold icyPose form; split <;> rfl
end YM.CF.Merino.Brooch
