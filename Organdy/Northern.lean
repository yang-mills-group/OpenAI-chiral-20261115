import Organdy.Cauliflower
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset

open Regis Head Lattice Precision Wilson Pressure Work.F03 Exterior
open Larva (Chip Tint dot blush stains decree wet_iff)
variable {n N:Side}
local notation "G" => SU.group

open RG Gleam ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
variable {M:Bed}{Z:PathData G}{q: Clip}{ρ θ v a η C:ℝ}


open Onyx Ember Lat Circuit Brecht
open Stationary (Gaia)
open scoped Topology 

abbrev north:Gaia:=YM.basis timeAxis
lemma apart:north≠0:=norm_pos_iff.mp (by rw [north,basis_norm];exact one_pos)

def argent:ℝ:=4*Maxwell.normal
lemma argent_pos:0<argent:=mul_pos (by norm_num) Maxwell.normal_pos

open Maxwell
lemma hue_north (i:Axis):
 grad i (grad i Green) north=(if timeAxis=i then 6 else -2)*normal:=by
 rw [second_Green apart]
 unfold north
 by_cases h:timeAxis=i
 · simp [h]; ring
 · simp [h,Ne.symm h]
lemma hue_nil {i j:Axis}(u:i≠j): grad j (grad i Green) north=0:=by
 rw [second_Green apart]
 unfold north
 by_cases h:timeAxis=i
 · simp [h,u,u.symm]
 simp [u,u.symm,h,Ne.symm h]
lemma lamp (I:PlaqAxes):
 (bareCurl I.val.1 I.val.2 I.val.1 I.val.2 north)= flash I * argent:=by
 rw [bareCurl,Pi.sub_apply,Bare.opp_grad apart,Bare.opp_grad apart]
 simp only [hue_north,if_neg I.property.ne,if_neg I.property.ne', if_neg (Ne.symm (plain I)), if_true,flash]
 unfold argent
 split_ifs <;> ring

lemma pale(I J:PlaqAxes)(e:I≠J):
  (bareCurl I.val.1 I.val.2 J.val.1 J.val.2 north)=0:=by
 let a:=I.val.1; let b:=I.val.2
 let k:=J.val.1; let m:=J.val.2
 have x:a<b:=I.property
 have y:k< m:=J.property
 have n:a≠k ∨ b≠m:= by
   by_contra! h
   exact e (Subtype.ext (Prod.ext h.1 h.2))
 have o:a≠m ∨ b≠k:=by
   by_contra! h
   rw [h.1,h.2] at x
   exact lt_asymm y x
 have H (i j l p:Axis)(z:i≠j ∨ l≠p):
   (if i=j then grad l (grad p Green) north else 0)=0:=by
     split
     · exact hue_nil (Or.resolve_left z (not_not.mpr ‹_›)).symm
     rfl
 change bareCurl a b k m north=_
 rw [bareCurl, Pi.sub_apply, Bare.opp_grad apart, Bare.opp_grad apart,
   H k b a m (o.symm.imp_left Ne.symm), H m b a k (n.symm.imp_left Ne.symm),
   H k a b m (n.imp_left Ne.symm), H m a b k (o.imp_left Ne.symm)]; abel

lemma beam_north (I J:PlaqAxes):
   specter I J north=(if I=J then flash J*argent else 0:ℂ):=by
 unfold specter
 by_cases h:I=J
 · subst J; rw [lamp, if_pos rfl,Complex.ofReal_mul]
 rw [pale I J h,if_neg h, Complex.ofReal_zero]
