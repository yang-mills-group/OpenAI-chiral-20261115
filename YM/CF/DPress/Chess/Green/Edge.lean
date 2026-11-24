import YM.CF.DPress.Chess.Green.Move
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Green
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube RP Phase Branch Mir Mir.Trip Brace Nacre Window Tenant
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m B:Side}{l':Site (More m)}
local notation "V_"=> CSide m B
local notation "I_"=> northTrip m l'
local notation "α_"=> W.i
omit W
private lemma glue_edge (x y: Site n)(i:Axis):seam x y i≠0:=by unfold seam; split <;> simp
private lemma travel_peer (c d:Site n)(x y:Site n→ℂ)(u:∀ z i,x z*seam c z i=seam d z i*x (z+step i)) (v:∀ z i,y z*seam c z i=seam d z i*y (z+step i))(p:x 0=y 0): x=y:=by
 have he(w:Site n)(i:Axis):x w=y w ↔ x (w+step i)=y (w+step i):= ⟨fun h=>mul_left_cancel₀ (glue_edge d w i) ((u w i).symm.trans ((congrArg (· * seam c w i) h).trans (v w i))), fun h=>mul_right_cancel₀ (glue_edge c w i) ((u w i).trans ((congrArg (seam d w i *·) h).trans (v w i).symm))⟩
 have ht(T:Walk)(w:Site n)(p:x w=y w) : x (Lattice.stop w T)=y (Lattice.stop w T):=by
    induction T generalizing w with
    | nil=> exact p
    | cons a t ih=> apply ih; rcases a with ⟨i,h|h⟩; exact (he w i).1 p; change x (w+ -step i)=y (w+ -step i); rw [←sub_eq_add_neg]; exact (he (w-step i) i).2 (by rw [sub_add_cancel]; exact p)
 funext z; have hz:= ht (Lattice.route 0 (lift z) 1) 0 p; rw [← show wrap n (0:Cover)=(0:Site n) from map_zero _,←wrap_stop_cover,route_end,wrap_lift] at hz; exact hz -- tune ambiguity
local notation "Θx"=> lagX W.od
local notation "XU"=>northZ m B
local notation "P0"=> Trip.far B (I_) (XU)
local notation "Θ_"=> axisCut m B W.i (XU)
include W
variable (p:Attend W B l')
include p
lemma capT (x:Site V_)(i:Axis): seam (P0) x i=seam (XU) (x+wrap V_ W.od) i:=by
 unfold seam; have hv : (P0) i=XU i - wrap V_ W.od i:=by unfold Trip.far; rw [if_neg (by simp [northTrip]),shift_v W p]
 rw [hv,Pi.add_apply]; simp only [eq_sub_iff_add_eq]

lemma march_cost (x:Site V_)(i:Axis): (Θx).payA x* seam (P0) x i=seam (XU) x i*(Θx).payA (x+step i):=by
 rw [capT W p]; have ht:= footFee (Θx) x (Lattice.step i); rw [show (Θx).s.act (step i :Cover)=step i from Signed.act_one _,wrap_step,lag_i,seam_eq,seam_eq] at ht; exact ht
lemma prince : ∃ k:ℂ,∀ x:Site V_, edging (P0) (Θ_) x = k*(edging (XU) (Θ_) x*(Θx).payA x):=by
 let u:=edging (P0) (Θ_); let v:=edging (XU) (Θ_); let h(x:Site V_):=(Θx).payA x; let k:= u 0*(h 0*v 0); let r(x:Site V_):= k*(v x*h x); have hz:u=r:=by
    refine travel_peer (P0) (Θ_) u r (edge_jump (P0) (Θ_)) (fun i y=>?_) ?_
    · unfold r
      rw [mul_assoc k,mul_assoc (v _),show h i* _= _ from march_cost W p i y,←mul_assoc (v i),show v i* _=_ from edge_jump _ (Θ_) i y]; ring
    unfold r k; rw [mul_assoc, show h 0*v 0*(v 0*h 0)=v 0*v 0*(h 0*h 0) by ring, show v 0*v 0=1 from edging_n ..,show h 0*h 0=1 from Shape.reflex ..]; rw [one_mul,mul_one]
 exact ⟨k,fun x=> congrFun hz x⟩
end YM.CF.DPress.Chess.Green
