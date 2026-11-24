import GaugeFieldConstruction.CloverSymmetryWeyl
/-!
# Select gauge C in Wick costs through the physical frame

It is *not* assumed that the measured finite frame (`LeaseVU`) intertwines continuous
rotations. We will be able to apply this mask argument because the frames commute with
SIGNED movements. One could use improper hypercube elements to prove more; here use just
the proper hypercube. Thus both square and complementary dual-product ink survive the
sign-flip projection. Still entirely inside the Weyl part after `feat`.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 6000
set_option maxRecDepth 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage.CloverSymmetry
open Calibration Calibration.RawBank Floor Cauchy Row Phys Function Set Filter Wide Cell
open Matter (FlavorIndex)
open scoped BigOperators Topology Matrix Matrix.Norms.Frobenius
open Angles Flux One
attribute [local instance] Stage.iA Stage.iG Stage.iX
def move_m: Signed := ⟨⟨![1,0,3,2],![1,0,3,2], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩, (fun _=>false)⟩
def move_n: Signed := ⟨⟨![2,3,0,1],![2,3,0,1], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩, (fun _=>false)⟩
def move_l: Signed := ⟨⟨![0,2,1,3],![0,2,1,3], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩, ![false,true,false,false]⟩
def move_r: Signed := ⟨1, ![true,false,false,true]⟩
def move_s: Signed := ⟨1, ![false,true,false,true]⟩
def move_t: Signed := ⟨1, ![false,false,true,true]⟩

def feat : Module.End ℂ (UV four) :=
    (1-spinFrame four move_l) *(1+spinFrame four move_n)*(1+spinFrame four move_m)*
    (1+spinFrame four move_t)*(1+spinFrame four move_s)*(1+spinFrame four move_r)

lemma commuteFeat (F : UV four →ₗ[ℂ] UV four)
    (u : ∀ g v, F (spinFrame four g v) = spinFrame four g (F v)) (v) :
    feat (F v) = F (feat v) := by
  simp only [feat,Module.End.mul_apply,LinearMap.sub_apply,LinearMap.add_apply,
    Module.End.one_apply,map_add,map_sub,u]
/- mask calculation just on bases -/
macro "clover_movers" : tactic => `(tactic|
   simp only [ show move_m.perm 0 = 1 from rfl,
   show move_m.flip 0 = false from rfl,
   show move_m.perm 1 = 0 from rfl,
   show move_m.flip 1 = false from rfl,
   show move_m.perm 2 = 3 from rfl,
   show move_m.flip 2 = false from rfl,
   show move_m.perm 3 = 2 from rfl,
   show move_m.flip 3 = false from rfl,
   show move_n.perm 0 = 2 from rfl,
   show move_n.flip 0 = false from rfl,
   show move_n.perm 1 = 3 from rfl,
   show move_n.flip 1 = false from rfl,
   show move_n.perm 2 = 0 from rfl,
   show move_n.flip 2 = false from rfl,
   show move_n.perm 3 = 1 from rfl,
   show move_n.flip 3 = false from rfl,
   show move_l.perm 0 = 0 from rfl,
   show move_l.flip 0 = false from rfl,
   show move_l.perm 1 = 2 from rfl,
   show move_l.flip 1 = true from rfl,
   show move_l.perm 2 = 1 from rfl,
   show move_l.flip 2 = false from rfl,
   show move_l.perm 3 = 3 from rfl,
   show move_l.flip 3 = false from rfl,
   show move_r.perm 0 = 0 from rfl,
   show move_r.flip 0 = true from rfl,
   show move_r.perm 1 = 1 from rfl,
   show move_r.flip 1 = false from rfl,
   show move_r.perm 2 = 2 from rfl,
   show move_r.flip 2 = false from rfl,
   show move_r.perm 3 = 3 from rfl,
   show move_r.flip 3 = true from rfl,
   show move_s.perm 0 = 0 from rfl,
   show move_s.flip 0 = false from rfl,
   show move_s.perm 1 = 1 from rfl,
   show move_s.flip 1 = true from rfl,
   show move_s.perm 2 = 2 from rfl,
   show move_s.flip 2 = false from rfl,
   show move_s.perm 3 = 3 from rfl,
   show move_s.flip 3 = true from rfl,
   show move_t.perm 0 = 0 from rfl,
   show move_t.flip 0 = false from rfl,
   show move_t.perm 1 = 1 from rfl,
   show move_t.flip 1 = false from rfl,
   show move_t.perm 2 = 2 from rfl,
   show move_t.flip 2 = true from rfl,
   show move_t.perm 3 = 3 from rfl,
   show move_t.flip 3 = true from rfl,
     show Bool.xor false false=false from rfl, show Bool.xor false true=true from rfl, show Bool.xor true false=true from rfl, show Bool.xor true true=false from rfl, Bool.true_xor, Bool.xor_true, Bool.false_xor, Bool.xor_false, Bool.not_true,Bool.not_false, pay_false,pay_true])
theorem passKill_r (v : UV four)
    (h_r : spinFrame four move_r v = -v) :
    feat v = 0 := by
  rw [feat]; simp only [Module.End.mul_apply,LinearMap.add_apply,Module.End.one_apply,
    h_r,map_zero,map_add,map_neg,
    add_neg_cancel,neg_add_cancel,zero_add,LinearMap.sub_apply,sub_self]
theorem passKill_s (v : UV four)
    (h_r : spinFrame four move_r v = v)
    (h_s : spinFrame four move_s v = -v) :
    feat v = 0 := by
  rw [feat]; simp only [Module.End.mul_apply,LinearMap.add_apply,Module.End.one_apply,
    h_r, h_s,map_zero,map_add,map_neg,
    add_neg_cancel,neg_add_cancel,zero_add,LinearMap.sub_apply,sub_self]
theorem passKill_t (v : UV four)
    (h_r : spinFrame four move_r v = v)
    (h_s : spinFrame four move_s v = v)
    (h_t : spinFrame four move_t v = -v) :
    feat v = 0 := by
  rw [feat]; simp only [Module.End.mul_apply,LinearMap.add_apply,Module.End.one_apply,
    h_r, h_s, h_t,map_zero,map_add,map_neg,
    add_neg_cancel,neg_add_cancel,zero_add,LinearMap.sub_apply,sub_self]
lemma feat0102 : feat (ff 0 1 0 2) = 0 := by
  apply passKill_s <;> (rw [ffMotion]; clover_movers)
lemma feat0103 : feat (ff 0 1 0 3) = 0 := by
  apply passKill_r <;> (rw [ffMotion]; clover_movers)
lemma feat0112 : feat (ff 0 1 1 2) = 0 := by
  apply passKill_r <;> (rw [ffMotion]; clover_movers)
lemma feat0113 : feat (ff 0 1 1 3) = 0 := by
  apply passKill_s <;> (rw [ffMotion]; clover_movers)
lemma feat0203 : feat (ff 0 2 0 3) = 0 := by
  apply passKill_r <;> (rw [ffMotion]; clover_movers)
lemma feat0212 : feat (ff 0 2 1 2) = 0 := by
  apply passKill_r <;> (rw [ffMotion]; clover_movers)
lemma feat0223 : feat (ff 0 2 2 3) = 0 := by
  apply passKill_s <;> (rw [ffMotion]; clover_movers)
lemma feat0313 : feat (ff 0 3 1 3) = 0 := by
  apply passKill_r <;> (rw [ffMotion]; clover_movers)
lemma feat0323 : feat (ff 0 3 2 3) = 0 := by
  apply passKill_r <;> (rw [ffMotion]; clover_movers)
lemma feat1213 : feat (ff 1 2 1 3) = 0 := by
  apply passKill_r <;> (rw [ffMotion]; clover_movers)
lemma feat1223 : feat (ff 1 2 2 3) = 0 := by
  apply passKill_r <;> (rw [ffMotion]; clover_movers)
lemma feat1323 : feat (ff 1 3 2 3) = 0 := by
  apply passKill_s <;> (rw [ffMotion]; clover_movers)
macro "gate_movers" : tactic => `(tactic|(
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,map_add,map_neg,ffMotion,
    pay_false, pay_true, -- simplify pay in each hit to expose signs
    show move_m.perm 0 = 1 from rfl,
    show move_m.flip 0 = false from rfl,
    show move_m.perm 1 = 0 from rfl,
    show move_m.flip 1 = false from rfl,
    show move_m.perm 2 = 3 from rfl,
    show move_m.flip 2 = false from rfl,
    show move_m.perm 3 = 2 from rfl,
    show move_m.flip 3 = false from rfl,
    show move_n.perm 0 = 2 from rfl,
    show move_n.flip 0 = false from rfl,
    show move_n.perm 1 = 3 from rfl,
    show move_n.flip 1 = false from rfl,
    show move_n.perm 2 = 0 from rfl,
    show move_n.flip 2 = false from rfl,
    show move_n.perm 3 = 1 from rfl,
    show move_n.flip 3 = false from rfl,
    show move_l.perm 0 = 0 from rfl,
    show move_l.flip 0 = false from rfl,
    show move_l.perm 1 = 2 from rfl,
    show move_l.flip 1 = true from rfl,
    show move_l.perm 2 = 1 from rfl,
    show move_l.flip 2 = false from rfl,
    show move_l.perm 3 = 3 from rfl,
    show move_l.flip 3 = false from rfl,
    show Bool.xor false false=false from rfl, show Bool.xor false true=true from rfl, show Bool.xor true false=true from rfl, show Bool.xor true true=false from rfl, Bool.true_xor, Bool.xor_true, Bool.false_xor, Bool.xor_false, Bool.not_true,Bool.not_false]
  clovers_norm
))

lemma keep3Gate (v : UV four)
    (p : spinFrame four move_r v = v)
    (q : spinFrame four move_s v = v)
    (r : spinFrame four move_t v = v) :
    feat v = 8 • (((1-spinFrame four move_l) *(1+spinFrame four move_n)*(1+spinFrame four move_m)) v) := by
  rw [feat]; simp only [Module.End.mul_apply,LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.one_apply,map_add,p,q,r]
  abel
lemma feat0101 :
    feat (ff 0 1 0 1) = -(8 • dPlus11) - (8 • dMinus11) := by
  rw [keep3Gate]; rotate_left;
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  gate_movers
  unfold dPlus11 dMinus11
  abel
lemma feat0123 :
    feat (ff 0 1 2 3) = -(8 • dPlus11) + 8 • dMinus11 := by
  rw [keep3Gate]; rotate_left;
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  gate_movers
  unfold dPlus11 dMinus11
  abel
lemma feat0202 :
    feat (ff 0 2 0 2) = 8 • dPlus11 + 8 • dMinus11 := by
  rw [keep3Gate]; rotate_left;
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  gate_movers
  unfold dPlus11 dMinus11
  abel
lemma feat0213 :
    feat (ff 0 2 1 3) = -(8 • dPlus11) + 8 • dMinus11 := by
  rw [keep3Gate]; rotate_left;
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  gate_movers
  unfold dPlus11 dMinus11
  abel
lemma feat0303 :
    feat (ff 0 3 0 3) = 0 := by
  rw [keep3Gate]; rotate_left;
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  gate_movers
  abel
lemma feat0312 :
    feat (ff 0 3 1 2) = 0 := by
  rw [keep3Gate]; rotate_left;
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  gate_movers
  abel
lemma feat1212 :
    feat (ff 1 2 1 2) = 0 := by
  rw [keep3Gate]; rotate_left;
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  gate_movers
  abel
lemma feat1313 :
    feat (ff 1 3 1 3) = 8 • dPlus11 + 8 • dMinus11 := by
  rw [keep3Gate]; rotate_left;
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  gate_movers
  unfold dPlus11 dMinus11
  abel
lemma feat2323 :
    feat (ff 2 3 2 3) = -(8 • dPlus11) - (8 • dMinus11) := by
  rw [keep3Gate]; rotate_left;
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  · rw [ffMotion]; clover_movers
  gate_movers
  unfold dPlus11 dMinus11
  abel

lemma sixPairs (a b:Axis)(x:a<b) :
    (a=0∧b=1) ∨ (a=0∧b=2) ∨ (a=0∧b=3) ∨ (a=1∧b=2) ∨ (a=1∧b=3) ∨ (a=2∧b=3) := by
  fin_cases a <;> fin_cases b <;> first | decide | exact absurd x (by decide)

lemma gaugePass (v : UG four) : feat (gin v) ∈ orbitSpin2 := by
  have ordered (a b c d : Axis) (x:a<b)(y:c<d) : feat (ff a b c d) ∈ orbitSpin2 := by
    have h_dMinus11 : dMinus11 ∈ orbitSpin2 := WeylInk.dMinus11.belong
    have h_dPlus11 : dPlus11 ∈ orbitSpin2 := WeylInk.dPlus11.belong
    clear v
    rcases sixPairs a b x with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      rcases sixPairs c d y with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
        simp only [ord0201, ord0301, ord1201, ord1301, ord2301, ord0302, ord1202, ord1302, ord2302, ord1203, ord1303, ord2303, ord1312, ord2312, ord2313,
          feat0101, feat0102, feat0103, feat0112, feat0113, feat0123, feat0202, feat0203, feat0212, feat0213, feat0223, feat0303, feat0312, feat0313, feat0323, feat1212, feat1213, feat1223, feat1313, feat1323, feat2323] <;>
          repeat' first | assumption | apply orbitSpin2.zero_mem | apply nsmul_mem | apply orbitSpin2.add_mem | apply orbitSpin2.neg_mem | apply orbitSpin2.sub_mem
  have half (a b c d : Axis) (x:a<b): feat (ff a b c d)∈orbitSpin2 := by
    rcases lt_trichotomy c d with u|u|u
    · exact ordered _ _ _ _ x u
    · rw [u,rightDiag,map_zero]; exact orbitSpin2.zero_mem
    rw [rightSkew a b c d,map_neg]; exact orbitSpin2.neg_mem (ordered _ _ _ _ x u)
  have charges (a b c d : Axis): feat (ff a b c d)∈orbitSpin2 := by
    rcases lt_trichotomy a b with u|u|u
    · exact half _ _ _ _ u
    · rw [u,leftDiag,map_zero]; exact orbitSpin2.zero_mem
    rw [leftSkew a b c d,map_neg]; exact orbitSpin2.neg_mem (half _ _ _ _ u)
  obtain ⟨v,rfl⟩:=(DeckG four).supply v
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact orbitSpin2.zero_mem
  | add a b p q => simp only [map_add]; exact orbitSpin2.add_mem p q
  | single i t =>
    rw [show Finsupp.single i t = t • ket i from by simp [ket],map_smul,map_smul,map_smul]
    apply orbitSpin2.smul_mem
    change GE at i; rcases i with ⟨⟨a,b⟩,c,d⟩; exact charges a b c d
#print axioms gaugePass
end YM.GaugeFieldConstruction.Stage.CloverSymmetry
end
