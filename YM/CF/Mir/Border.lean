import YM.CF.Mir.Data
import YM.CF.Phase.Rates

/-! Fermion translations and sign-cut placement. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mir
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset
attribute [local instance] opCStarAlgebra
variable {N : Side}

def edgeF (x c d : Per N) : ℂ := if 0<(x-c).val ∧ (x-c).val≤(d-c).val then -1 else 1
lemma edge_real (x c d : Per N) : star (edgeF x c d)=edgeF x c d := by unfold edgeF; split <;> simp
lemma edge_n (x c d : Per N) : edgeF x c d*edgeF x c d=1 := by unfold edgeF; split <;> simp
lemma edge_spec (x c d : Per N) : edgeF x c d* (if x=c then (-1:ℂ) else 1) = (if x=d then (-1:ℂ) else 1)*edgeF (x+1) c d := by
  let i := (x-c).val; let j := (d-c).val
  have hm : i<N.val := ZMod.val_lt _; have hb : j<N.val := ZMod.val_lt _; have hk : 0<N.val := N.property
  have H : x=c ↔ i=0 := by unfold i; rw [ZMod.val_eq_zero,sub_eq_zero]
  have G : x=d ↔ i=j := by unfold i j; exact ⟨fun h=>by rw [h],fun h=>sub_left_inj.mp (ZMod.val_injective _ h)⟩ -- name
  have hq : (x+1-c).val = if i+1=N.val then 0 else i+1 := by
    rw [add_sub_right_comm,ZMod.val_add,ZMod.val_one_eq_one_mod]; change (i+1%N.val)%_=_
    rw [Nat.add_mod_mod]; split <;> rename_i h
    · rw [h,Nat.mod_self]
    rw [Nat.mod_eq_of_lt (by omega)]
  simp only [edgeF,hq]; change (if 0 < i ∧ i ≤ j then (-1:ℂ) else 1)*(if x=c then -1 else 1)=(if x=d then -1 else 1)*(if 0<(if i+1=N.val then 0 else i+1) ∧ (if i+1=N.val then 0 else i+1) ≤ j then -1 else 1); simp only [H,G]; split_ifs <;> first | omega | simp
def edging (c d x : Site N) : ℂ := ∏ i:Axis, edgeF (x i) (c i) (d i)
lemma edging_r (c d x : Site N) : star (edging c d x)=edging c d x := by unfold edging; rw [star_prod]; simp_rw [edge_real]
lemma edging_n (c d x : Site N) : edging c d x*edging c d x=1 := by rw [edging,←prod_mul_distrib]; exact prod_eq_one fun i _=>edge_n ..
lemma edge_jump (c d x : Site N) (i) : edging c d x * seam c x i= seam d x i * edging c d (x+step i) := by
  let s := univ.erase i
  have e (x : Site N) : edging c d x=(∏ j∈s, edgeF (x j) (c j) (d j))* edgeF (x i) (c i) (d i) := (prod_erase_mul _ _ (mem_univ _)).symm
  rw [e,e,mul_assoc]; unfold seam; rw [edge_spec, show (x+step i : Site N) i=x i+1 by simp, mul_left_comm (if x i=d i then (-1:ℂ) else 1)] -- tune
  congr 1; apply prod_congr rfl; intro j k; have h : j≠i := (mem_erase.mp k).1; simp [h]
def fringe (c d : Site N) : UNI (Model N) := ⟨jump (Equiv.refl _) (fun x=> edging c d x • 1), jump_unitary _ _ fun x=> by
  constructor <;> rw [star_smul, star_one,edging_r,Algebra.smul_mul_assoc, Algebra.mul_smul_comm,smul_smul,edging_n,one_smul,one_mul]⟩
lemma twist_comm {I : Type*} [Fintype I] [DecidableEq I] (U : UNI I) (A B : Op I) (h : U.val*A=B*U.val) : twist U A=B := by rw [twist_formula,h,mul_assoc,show U.val*star _=1 from U.property.2,mul_one]
lemma step_fringe (c d : Site N) (U : Bkg N) (i) : twist (fringe c d) (shift matter U c i)=shift matter U d i := by
  apply twist_comm
  simp only [fringe,shift,jump_mul,Equiv.trans_refl,Equiv.refl_trans, Equiv.refl_apply]
  apply congrArg; funext x; simp only [hop,Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul,mul_one,smul_smul]; rw [mul_comm (seam c x i),edge_jump,mul_comm (seam d x i)]; rfl
lemma view_fringe (c d : Site N) (A : Op SpinIdx) : twist (fringe c d) (spin N Slot A)=spin N Slot A := by
  apply twist_comm; simp only [fringe,spin,jump_mul,Equiv.refl_trans,Equiv.refl_apply, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,one_mul,mul_one]
lemma grade_fringe (c d : Site N) (v : Site N→ Vect) : congrC (fringe c d) (Cfield v)=Cfield v := by
  have he : ccU (fringe c d)=fringe c d := by apply Subtype.ext; simp [fringe,ccU,jump_cc, edging_r] -- tune
  rw [congr_form,he, ←twist_formula]; apply twist_comm; simp only [fringe,Cfield,jump_mul,Equiv.refl_trans,Equiv.refl_apply, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,one_mul,mul_one]
lemma swingFringe (c d : Site N) (U : Bkg N) : twist (fringe c d) (frame matter U c).H = (frame matter U d).H := by
  unfold WilsonFrame.H WilsonFrame.H0 WilsonFrame.inc WilsonFrame.lap WilsonFrame.diff; dsimp only [frame]; simp only [map_mul, map_neg,map_add,map_sum,map_sub,map_star,map_one,map_smul, view_fringe,step_fringe]
lemma rays_same {m B : Side} (c d : Part m B) {U : Skin m B} {e : ℝ} (b : Room B e) (h : Guard U e) {s : ArrayF m} {x y r} (g : Verified m B margin U s r) (u:x∈zone r) (v:y∈zone r) : ray m B c U s x y=ray m B d U s x y := by
  let V := fringe c d
  have hp : lens m B d U=twist V (lens m B c U) := by unfold lens occP; rw [←swingFringe c d,←projector_twist (band _ _ _ (plaq_lens b h))]
  unfold ray; apply sum_congr rfl; intro i hi
  unfold rad; have he := mem_range.mp hi
  rw [hp];
  let F := fun i=> bow m B U s (increment B i x y)
  have hy i : congrC V (F i)=F i := grade_fringe c d _
  have ht := spark_turn (bow_ok c b h g (inc_in u v B he.le)).2 (short c b h g (inc_in u v B he.le) (inc_in u v B he) (inc_gap u v B i)) V; change spark _ (congrC V (F _)) (congrC V (F _))=_ at ht; rw [hy,hy] at ht; exact ht.symm
lemma funding {m B : Side} (c d : Part m B) {U : Skin m B} {e : ℝ} (b : Room B e) (h : Guard U e) {x} (g : ZeroF m B U x) : fund m B c U x=fund m B d U x := by
  let V := fringe c d
  have hp : lens m B d U=twist V (lens m B c U) := by unfold lens occP; rw [←swingFringe c d,←projector_twist (band _ _ _ (plaq_lens b h))]
  have hg : netsal (lens m B d U) (pair m B U x)=netsal (lens m B c U) (pair m B U x) := by
    apply Real.exp_injective; rw [salary d b h g,salary c b h g,hp]
    let C := pair m B U x
    have hk : congrC V C=C := grade_fringe c d _
    unfold C at hk; nth_rw 1 [←hk]; rw [filled_twist,act_unit_norm]
  have he : accord m B c U x=accord m B d U x := by
    apply integral_congr_ae; apply Eventually.of_forall; intro y
    unfold lyre; by_cases l : law m B U y=0; simp [l]
    obtain ⟨z,H⟩ := arches (law_rich m B U y l) g; rw [echoes c b h _ _ z H, echoes d b h _ _ z H,bill,bill]
    have ht x (v : EdgeP m B U x z) : amount m B c U x z=amount m B d U x z := rays_same c d b h (show Verified _ _ margin _ _ _ from v) (stick_in 0 (show (0:Row)∈Knot by simp [Knot])) (stick_in 1 (show (1:Row)∈Knot by simp [Knot]))
    rw [ht x H.2,ht y H.1]
  unfold Phase.fund; rw [he,hg]
end YM.CF.Mir
