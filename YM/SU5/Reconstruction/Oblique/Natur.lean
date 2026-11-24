import YM.SU5.Reconstruction.Oblique.RotorField
/-! # Retain Tilt through ALL regulator step advances. Inclusion costs at arbitrary legs use actual couple
 Adapt `Buffered/Naturality`, `Buffered/RiseReflect` in same issuer. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Tilted
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance
  Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree Py Py.Rate LocalLimit
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin SatinVerification
namespace Ramp
open Pastry Dial Paige Tree Next.SectorChange Branch Vault Fir Drapes Tap
open Reed (Fine think)
variable {N P : Side} (G : Ratio N P) (j : ℕ) (Q : Op SU.Slot) (M : Male) (ho : Odd G.count.val)
variable (T : Ramp)
local notation "U" => T.reel
local notation "Lamp" => pflux T.plan G U inert
lemma plan_broad : T.plan.broad G = T.plan := by simp [Shape.broad, Ramp.plan,incX]
lemma shift_plank : twist (T.vehicle N) (plankP N Q)= -plankP N Q := by
  let A:=Aop-(1/2:ℂ) • 1; let F:= (jump (Equiv.refl (Site N)) (fun _=> A ⊗ₖ Q))
  change twist _ (love N F)= -(love N F); rw [show twist (T.vehicle N) (love N F)= _ from (wingX T.plan U inert F), ←map_neg]; apply congrArg
  let W:=Tofu T.plan N; let v:=sings false (mealU T.plan U inert N) F
  have hg : twist U A= -A := by
    unfold A; rw [map_sub, twist_scalar, map_one, show twist U Aop=1-Aop from angleX (T.jet) true]
    have he : ((1/2:ℂ) + 1/2) • (1:Op SpinIdx)=1 := by norm_num
    rw [add_smul] at he; nth_rw 1 [← he]; abel
  have he(x y:Site N):tap F x y=if x=y then A ⊗ₖ Q else 0:= by ext i j; by_cases p:x=y <;> simp [F,tap,jump_apply,p]
  have hs(x y:Site N): tap v x y= - tap F x y:=by
     unfold v; rw [tap_sg,he,he]; by_cases h:x=y; swap
     · rw [if_neg h, if_neg (W.injective.ne h),win_z,mul_zero,zero_mul,neg_zero]
     subst y; simp only [if_true]; rw [show (milU ..).val *_*_=_ from (twist_formula (milU T.plan U inert x) _).symm]; change sings false _ _= _; rw [wingM,Scroll.wingK]; change twist U A ⊗ₖ twist 1 Q= _; rw [hg, one_des, op_kron_neg]
  ext ⟨i,u⟩ ⟨j,v⟩; exact congr_fun (congr_fun (hs i j) _) _
lemma shift_fee (b : Bool) : twist (T.vehicle N) (feeL b N Q) = feeL (!b) N Q := by
  cases b <;> simp [feeL,breeze_exp,map_neg,Ramp.shift_plank Q T]

include ho
variable (z : Nom N P)
local notation "Z" => stanza G T.plan inert z
lemma commute_mode (v : Ket (Single N)) (b : Bool) :
    byMode G j Q M Z (!b) (acts (T.vehicle N).val v) = acts (T.vehicle P).val (byMode G j Q M z b v) := by
  rw [byMode_eq,byMode_eq,route_foot]
  rw [show foot G (T.vehicle P).val=(Lamp).val from (by rw [puff G ho,T.plan_broad G])]
  rw [←Ramp.shift_fee Q T, ← Fock.swivel, Fock.swivel Lamp (Peaks.cloth j M G (unionP z)), patched_acts]
  rw [show twist Lamp (Peaks.cloth j M G (unionP z)) = _ from clothing G ho T.plan inert U (T.jet) j M z]
local notation "sub" => subF G j Q M ho
theorem sub_natural {S : Finset (Single N)} {A : FC (Single N)} {b : Bool} (h : Fine (Tset N) S b A) : sub Z (Fock.theta (T.vehicle N) A)=Fock.theta (T.vehicle P) (sub z A) := by
  have ht:= T.exchanges N
  let R:=T.vehicle N
  induction h with
  | empty=> rw [theta_zero,map_zero,map_zero,theta_zero]
  | one=> rw [theta_one,sub_one,sub_one,theta_one]
  | seed k v=>
    by_cases p:k∈ Tset N
    · have hg:= (within_basis (Tset N) k p); rw [show (think (Tset N)).term k=put k from if_pos p,← create_put,theta_upV, sub_create G j Q M ho z hg, theta_upV, map_smul]
      have hp:withinM (Tset N)ᶜ (acts R.val (basisKet k)) := by unfold withinM; rw [←Fine.altitude ht,←Fock.swivel,hg]
      rw [sub_remove G j Q M ho Z hp]; congr 2; exact Ramp.commute_mode G j Q M ho T z _ true
    have g := within_basis (Tset N)ᶜ k (mem_compl.mpr p)
    have hp:withinM (Tset N) (acts R.val (basisKet k)) := by unfold withinM; rw [←ht,←Fock.swivel,g]
    rw [show (think (Tset N)).term k= -takeF k from if_neg p, ← remove_take]
    have H {p:Side} (A : FC (Single p)) : Fock.theta (T.vehicle p) (-A)= -Fock.theta (T.vehicle p) A := by simp [Fock.theta]
    rw [H,map_neg,map_neg,H,theta_downV,map_smul,sub_remove G j Q M ho z g,sub_create G j Q M ho Z hp,theta_downV]; congr 3; exact Ramp.commute_mode G j Q M ho T z _ false
  | grow e h ih it=>
    have x {C : FC (Single N)} {b} (p : Fine (Tset N) S b C): Fine (Tset N) (modesIn N (Finset.univ.image (T.plan.anon N))) b (Fock.theta (T.vehicle N) C) := T.sectorCharge _ _ (fine_enlarge (by rw [modes_univ]; exact subset_univ _) p)
    rw [theta_mul, sub_mul G j Q M ho Z (x e) (x h), sub_mul G j Q M ho z e h, theta_mul, ih,it]
  | add _ _ ih it=> rw [theta_add,map_add,map_add,theta_add,ih,it]
  | scale _ _ ih=> rw [theta_smul,map_smul,map_smul,theta_smul,ih]
end Ramp
end YM.CF.Buffered.Afterglow.Tower.Tilted
