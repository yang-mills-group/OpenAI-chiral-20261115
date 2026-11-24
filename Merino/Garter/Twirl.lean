import YM.SU5.Regis.Visions
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Garter
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

section Tread
variable {D:Type*}[AddCommGroup D]
abbrev bound (w:Links (Per n) D) : Links (Per n) (Multiplicative D) :=
 fun i=>Multiplicative.ofAdd (w i)
lemma read_sum (w:Links (Per n) D)(x:Site n)(a:Walk) :
    (travel (bound w) x a).toAdd=linkSum w x a := by
 induction a generalizing x with
 | nil => rfl
 | cons d l ih =>
   simp only [travel,toAdd_mul,ih,linkSum,Step.read]
   split <;> rfl


lemma flip_walk (w:Links (Per n) D)(a b:Lattice.Step)(x:Site n):
   linkSum w x (oriented a b) = -linkSum w (x+a.vec) (oriented a.rev b) := by
 rw [← read_sum,←read_sum,oriented_swap b a.rev,oriented_next]
 simp [mul_comm]

lemma swap_walk (w:Links (Per n) D)(a b:Lattice.Step)(x:Site n):
   linkSum w x (oriented a b) = - linkSum w x (oriented b a) := by
 rw [←read_sum,←read_sum,oriented_swap b a]
 simp

def turnb (b:Bool):ℝ:=if b then -1 else 1
lemma spiral₁ [Module ℝ D](w:Links (Per n) D)(a:Axis)(b:Lattice.Step)(x:Site n):
   linkSum w x (oriented (posDir a) b) =
    turnb b.neg • linkSum w (atFace x (posDir a) b) (square a b.dir) := by
 rcases b with ⟨j,_|_⟩
 · simp [turnb, atFace,posDir]; rfl
 change linkSum w x (oriented (posDir a) (negDir j)) = (-1:ℝ) •
    linkSum w (atFace x (posDir a) (negDir j)) (square a j)
 rw [swap_walk,flip_walk,neg_neg,Step.rev_neg,swap_walk]
 simp [atFace,posDir,negDir]; rfl


lemma spiral [Module ℝ D](w:Links (Per n) D)(a b:Lattice.Step)(x:Site n):
   linkSum w x (oriented a b) = turnb a.neg • turnb b.neg •
      linkSum w (atFace x a b) (square a.dir b.dir):= by
 rcases a with ⟨i,_|_⟩
 · change _=(1:ℝ)•_; rw [one_smul]; exact spiral₁ w i b x
 rw [flip_walk]
 change - linkSum _ _ (oriented (posDir i) b) = (-1:ℝ) • _
 rw [spiral₁,neg_smul,one_smul]; simp [atFace, posDir]

end Tread

lemma read_bank (s:Signed)(u:Site n)(Y:Dir G n) :
   bound (collect G (bank s u Y)) = pull s u (bound (collect G Y)) := by
 funext i
 rw [bank,LinearMap.comp_apply]
 let a:=arbor u Y
 change Multiplicative.ofAdd (Bid.pulled (arbor u Y) s (i.1,coord i.2)) = _
 simp only [Bid.pulled,show Exterior.coord i.2 = axisEquiv i.2 from rfl,Equiv.symm_apply_apply,
    pull,Step.read,Step.used,affine,add_zero]
 split
 · exact congrArg (fun x=>Multiplicative.ofAdd (- Y (x,coord _))) (show _ = s.act i.1 + u - step ((posDir i.2).rotate s).dir from sub_add_eq_add_sub .. )
 exact rfl



/-- sign from orienting Face.send positively -/
def orient(s:Signed)(p:PlaqAxes) : ℝ :=
 turnb (s.flip p.val.1) * turnb (s.flip p.val.2) *
   turnb (decide (s.perm p.val.2 < s.perm p.val.1))

lemma orient_abs(s)(p): |orient s p| =1 := by unfold orient turnb; split_ifs <;> norm_num

lemma twirl(s:Signed)(u:Site n)(i:Face (Per n))(V:Dir G n):
   faceCurl i (bank s u V) =
      orient s i.2 • faceCurl (Face.send s u i) V:= by
 rw [faceCurl,faceCurl,← fundamental,← fundamental]
 conv_lhs => rw [←read_sum,read_bank,travel_pull]
 let a := i.2.val.1
 let b := i.2.val.2
 let c := (posDir a).rotate s
 let d := (posDir b).rotate s
 rw [show List.map _ (square i.2.val.1 i.2.val.2) = oriented ((posDir a).rotate s) ((posDir b).rotate s) by
    rw [show square _ _ = oriented (posDir a) (posDir b) from rfl, oriented, oriented]; simp [← Step.rev_rotate]]
 rw [read_sum, spiral]
 let x:=atFace (affine s u i.1) c d


 have H : s.perm a ≠ s.perm b := s.perm.injective.ne i.2.property.ne
 let C:=s.perm a
 let D:=s.perm b
 change turnb c.neg • turnb d.neg • linkSum (collect G V) x (square C D) =
  (turnb (s.flip a)*turnb (s.flip b)*turnb (decide (D<C))) •
     linkSum (collect G V) x (square (min C D) (max C D))
 have ht (z): ((posDir z).rotate s).neg=s.flip z:=by simp [Step.rotate,posDir]
 rw [ht a, ht b, mul_smul,mul_smul]
 rcases lt_or_gt_of_ne (show C ≠ D from H) with h|h
 · rw [min_eq_left h.le,max_eq_right h.le,decide_eq_false h.not_gt,
       show turnb false=(1:ℝ) from rfl,one_smul]
 rw [min_eq_right h.le,max_eq_left h.le,decide_eq_true h,
     show turnb true=(-1:ℝ) from rfl,neg_smul,one_smul,
     show square C D=oriented (posDir C) (posDir D) from rfl, swap_walk]


 rfl
lemma bank_bank (a s:Signed)(u v:Site n)(V:Dir G n) :
   bank s v (bank a u V) = bank (a*s) (affine a u v) V := by
 suffices t: Injective (fun W:Dir G n => bound (collect G W)) by
   apply t; beta_reduce
   rw [read_bank,read_bank,read_bank,pull_pull]
 intro W X h; funext p
 rcases p with ⟨x,p⟩
 obtain ⟨i,rfl⟩:=axisEquiv.surjective p
 exact congrArg Multiplicative.toAdd (congr_fun h (x,i))

end YM.CF.Merino.Garter
