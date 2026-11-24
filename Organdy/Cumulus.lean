import YM.SU5.Regis.Visions
import Organdy.Domaine
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


def pace(s:Signed)(i:Axis):ℝ:= if s.flip i then -1 else 1
open scoped Matrix
def brake {K:Type}[AddCommGroup K][One K](s:Signed)(i:Axis):Four K:=
    if s.flip i then -step (s.perm i) else 0

variable (s:Signed)(b:Site n)
lemma runs(X:Larva.Dir n)(x:Site n)(i:Axis):
 bank s b X (x,coord i)=
    pace s i • X (affine s b x+brake s i, coord (s.perm i)):=by
 rw [bank, LinearMap.comp_apply,show dusk s (arbor b X)=Bid.pulled (arbor b X) s from rfl]
 unfold Bid.pulled
 rw [←coord_map,Equiv.symm_apply_apply]
 have a(y z:Site n):y+(-z)+b=y+b+(-z):=by abel
 cases h:s.flip i
 <;> simp [Step.used,Step.rotate,posDir,h,pace,brake,arbor,affine,sub_eq_add_neg,a]
def run (X:Larva.Dir n)(x:Site n)(i j:Axis)(a:SU.group.ColorIndex):ℝ:=
 X (x+step i,coord j) a - X (x,coord j) a

lemma runA (X:Larva.Dir n)(x:Site n)(i j:Axis)(a:SU.group.ColorIndex):
 run (bank s b X) x i j a=
 pace s i*pace s j*run X (affine s b x+(brake s i+brake s j)) (s.perm i) (s.perm j) a:=by
 unfold run
 rw [runs,runs]; simp only [PiLp.smul_apply,smul_eq_mul]
 have h: s.act (step i:Site n)=if s.flip i then - step (s.perm i) else step (s.perm i):=by
   simpa [Step.rotate,posDir,Step.vec] using (Step.vec_rotate (R:=Per n) (posDir i) s).symm
 simp only [affine,Signed.act_add,h]
 by_cases e:s.flip i=true
 · rw [if_pos e,
    show s.act x+b+(brake s i+brake s j)+step (s.perm i)=s.act x+b+brake s j from by rw [brake,if_pos e];abel,
    show s.act x+-step (s.perm i)+b+brake s j=s.act x+b+(brake s i+brake s j) from by rw [show brake s i=- (step (s.perm i):Site n) from if_pos e];abel,
    show pace s i= -1 from if_pos e]
   ring
 rw [if_neg e,show pace s i= 1 from if_neg e,show (brake s i:Site n)=0 from if_neg e, zero_add,
    show s.act x+step (s.perm i)+b+brake s j=s.act x+b+brake s j+step (s.perm i) from by abel]
 ring

lemma blush_eq (X:Larva.Dir n)(x:Site n)(q:PlaqAxes)(a:SU.group.ColorIndex):
  blush X ((x,q),a) =
  run X x q.val.1 q.val.2 a-run X x q.val.2 q.val.1 a:=by
 change (Exterior.d 1 n *ᵥ parts G 1 X a) (x,plaquette q)=_
 rw [d_plaquettes]
 rfl

lemma port (x:Site n)(q:PlaqAxes):
  Face.send s b (x,q) =
    (affine s b x+(brake s q.val.1+brake s q.val.2),q.rotate s):=by
   cases h:s.flip q.val.1 <;> cases u:s.flip q.val.2 <;>
    simp [Face.send,Face.lower,atFace,Step.rotate,posDir,Step.vec,brake,h,u,add_assoc]

def relay(i:Chip n):Chip n:=(Face.send s b i.1,i.2)
def turn(s:Signed)(q:PlaqAxes):ℝ:=
  pace s q.val.1*pace s q.val.2*(if s.perm q.val.1<s.perm q.val.2 then 1 else -1)
abbrev draftSig (i:Chip n):= turn s i.1.2

lemma turn_one (q:PlaqAxes): |turn s q|=1:=by simp [turn,pace,abs_mul,apply_ite (|·|)]

lemma blush_bank (i:Chip n)(X:Larva.Dir n):
 blush (bank s b X) i=draftSig s i *blush X (relay s b i):=by
 rcases i with ⟨⟨x,q⟩,a⟩
 simp only [relay,port,draftSig,blush_eq,runA,turn]
 have e:s.perm q.val.1≠s.perm q.val.2:= s.perm.injective.ne q.property.ne
 rw [add_comm (brake s q.val.2) (brake s q.val.1)]
 rcases lt_or_gt_of_ne e with e|e
 · rw [if_pos e]
   simp only [PlaqAxes.rotate,PlaqAxes.ordered,min_eq_left e.le,max_eq_right e.le]
   ring
 rw [if_neg e.not_gt]
 simp only [PlaqAxes.rotate,PlaqAxes.ordered,min_eq_right e.le,max_eq_left e.le]
 ring

lemma relay_one (i:Chip n):
 relay 1 0 i=i ∧ draftSig 1 i=1:=by
 rcases i with ⟨⟨x,q⟩,c⟩
 simp [relay,port,brake,affine,PlaqAxes.rotate,PlaqAxes.ordered,q.property.le,
     draftSig,turn,pace,q.property]

/-- axial mirror, shift by arbitrary b; sorted last still. -/
abbrev mir := Signed.mirror timeAxis
lemma plain (q:PlaqAxes):q.val.1≠ timeAxis:=by
 have h:= q.property
 exact ne_of_lt (lt_of_lt_of_le h (Fin.le_last _))
def flash (q:PlaqAxes):ℝ:=if timeAxis=q.val.2 then -1 else 1
lemma flash_turn(q:PlaqAxes): turn mir q=flash q:=by
 simp [mir,Signed.mirror,pace,turn,flash,Ne.symm (plain q),q.property]
lemma mirror_rotate(q:PlaqAxes): q.rotate mir = q:=by
 ext <;> simp [PlaqAxes.rotate,mir,Signed.mirror,PlaqAxes.ordered,q.property.le]
lemma sameTint (b:Site n)(i:Chip n):dot (relay mir b i)=dot i:=
 Prod.ext (mirror_rotate i.1.2) rfl

lemma port_fee(i:Axis):pdist (brake s i:Site n)≤1:=by
 unfold brake
 split
 · rw [pdist_neg];exact pdist_step _
 have h:= separation_self (0:Site n); rw [separation,sub_self] at h; rw [h]; omega
lemma stay (x:Site n)(q:PlaqAxes):
 separation (affine s b x) (Face.send s b (x,q)).1≤2:=by
 rw [separation_comm,port]
 simp only
 rw [separation,add_sub_cancel_left]
 exact (pdist_triangle ..).trans (Nat.add_le_add (port_fee ..) (port_fee ..))
lemma dock {k:ℕ}{o:Site n}(i:Chip n)(h:separation o i.1.1≤k):
 separation (affine s b o) (relay s b i).1.1≤k+2:=
 (separation_triangle _ (affine s b i.1.1) _).trans
   (Nat.add_le_add (by simpa only [affine,separation_translate,separation_signed]) (stay s b ..))
lemma relay_fee{k:ℕ}(i:Chip n)(h:separation 0 i.1.1≤k):
 separation b (relay s b i).1.1 ≤ k+2:=by
 simpa [affine] using dock s b i h
-- k=0 h implies i.1.1=0? not needed
lemma runs_norm(X:Larva.Dir n)(x:Site n)(i:Axis):
 ‖bank s b X (x,coord i)‖≤‖X‖:=by
 rw [runs,norm_smul,Real.norm_eq_abs]
 rw [show |pace s i|=1 by unfold pace;split<;>norm_num, one_mul]
 exact norm_le_pi_norm ..
lemma seats (X:Larva.Dir n):‖bank s b X‖ ≤ ‖X‖:=by
 refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr ?_
 rintro ⟨x,y⟩
 simpa [←coord_map] using runs_norm s b X x (axisEquiv.symm y)

lemma tandem (t: Signed)(c:Site n)(i:Chip n)(X:Larva.Dir n):
   blush (bank t c (bank s b X)) i = blush (bank (s*t) (affine s b c) X) i:= by
 change faceCurl i.1 _ i.2=faceCurl i.1 _ i.2
 have h(Y:Larva.Dir n): HasDerivAt
    (fun r:ℝ=>SU.group.curvature (faceValue (represent (r • Y)) i.1)) (faceCurl i.1 Y) 0:=
      curvature_of_hasDerivAt (face_deriv i.1 Y)
 have a:= h (bank t c (bank s b X))
 simp_rw [bank_at,pull_pull,←bank_at] at a
 rw [a.unique (h ..)]
