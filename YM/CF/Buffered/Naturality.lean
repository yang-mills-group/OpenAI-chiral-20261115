import YM.CF.Buffered.Subst

/-! # Reflection and gaugeM substitution on each forest -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Advance
open Function Fock NormedSpace SU Lat Lattice Finset Cube Spire MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree Vault Fir Peaks Drapes Tap
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P : Side} (G : Ratio N P) (j : ℕ) (Q : Op Slot) (M : Male) (ho : Odd G.count.val)
local notation "φ" => patchQ G
variable (i : Axis) (s : ℤ)
local notation "s₂" => (G.count.val * s : ℤ)
local notation "U" => pinLift i
local notation "V" => pflux (plane i s) G U inert

lemma summit_patch (a : Shape) (L : UNI SpinIdx) (k l : Single N) :
    (pflux a G L inert).val (φ k) (φ l) = (prepU a L inert N).val k l := by
  rcases k with ⟨⟨x,i⟩,u⟩; rcases l with ⟨⟨y,j⟩,v⟩
  change jump (paceU a G) (fun i=>(milU a L inert i.1).val) ((x,0),i,u) ((y,0),j,v)=jump (Tofu a N) (fun i=>(milU a L inert i).val) (x,i,u) (y,j,v)
  rw [jump_apply,jump_apply]; rw [show paceU a G (x,0) = ((Tofu a N x),0) from Prod.ext rfl a.s.act_zero]
  simp only [Prod.mk_inj,and_true]
lemma patched_acts (a : Shape) (L : UNI SpinIdx) (v : Ket (Single N)) :
    acts (pflux a G L inert).val (coat φ v)=coat φ (acts (prepU a L inert N).val v) := by
  let K := pflux a G L inert; let T := prepU a L inert N
  have ht : twist K (cutM (lows φ))= cutM (lows φ) := by
    rw [←level, edgeDesk]; rw [show twist K (endorse G 1)= _ from (clampS G a inert L 1)]; change endorse G (twist T 1)=_; rw [map_one]
  have hw : summit φ K.val=T.val := funext fun i=> funext fun j=> summit_patch G a L i j
  have hr := (coat_ret φ v).symm; calc
    _ = acts (cutM (lows φ)) (acts K.val (coat φ v)) := by rw [←ht,←Fock.swivel,← hr]
    _ = _ := by rw [←stance, ← summit_rule, hw]

lemma shift_plank : twist (carR i s N) (plankP N Q)= -plankP N Q := by
  let A:=Aop-(1/2:ℂ) • 1; let F:= (jump (Equiv.refl (Site N)) (fun _=> A ⊗ₖ Q))
  change twist _ (love N F)= -(love N F); rw [show twist (carR i s N) (love N F)= _ from (wingX (plane i s) U inert F), ←map_neg]; apply congrArg
  let T:=Tofu (plane i s) N; let v:=sings false (mealU (plane i s) U inert N) F
  have hg : twist U A= -A := by
    unfold A; rw [map_sub, twist_scalar, map_one, show twist U Aop=1-Aop from angleX (mirrorX i) true]
    have he : ((1/2:ℂ) + 1/2) • (1:Op SpinIdx)=1 := by norm_num
    rw [add_smul] at he; nth_rw 1 [← he]; abel
  have he(x y:Site N):tap F x y=if x=y then A ⊗ₖ Q else 0:= by ext i j; by_cases p:x=y <;> simp [F,tap,jump_apply,p]
  have hs(x y:Site N): tap v x y= - tap F x y:=by
     unfold v; rw [tap_sg,he,he]; by_cases h:x=y; swap
     · rw [if_neg h, if_neg (T.injective.ne h),win_z,mul_zero,zero_mul,neg_zero]
     subst y; simp only [if_true]; rw [show (milU ..).val *_*_=_ from (twist_formula (milU (plane i s) U inert x) _).symm]; change sings false _ _= _; rw [wingM,Scroll.wingK]; change twist U A ⊗ₖ twist 1 Q= _; rw [hg, one_des, op_kron_neg]
  ext ⟨i,u⟩ ⟨j,v⟩; exact congr_fun (congr_fun (hs i j) _) _
lemma shift_fee (b : Bool) : twist (carR i s N) (feeL b N Q) = feeL (!b) N Q := by
  cases b <;> simp [feeL,breeze_exp,map_neg,shift_plank Q i s]

include ho
variable (z : Nom N P)
local notation "Z" => stanza G (plane i s) inert z
lemma commute_mode (v : Ket (Single N)) (b : Bool) :
    byMode G j Q M Z (!b) (acts (carR i s N).val v) = acts (carR i s₂ P).val (byMode G j Q M z b v) := by
  rw [byMode_eq,byMode_eq,route_foot]
  rw [show foot G (carR i s₂ P).val=(V).val from (by rw [puff G ho,plane_broad]; rfl)]
  rw [←shift_fee Q i s, ← Fock.swivel, Fock.swivel V (Peaks.cloth j M G (unionP z)), patched_acts]
  rw [show twist V (Peaks.cloth j M G (unionP z)) = _ from clothing G ho (plane i s) inert U (mirrorX i) j M z]; rfl
local notation "sub" => subF G j Q M ho
theorem sub_natural {S : Finset (Single N)} {A : FC (Single N)} {b : Bool} (h : Fine (Tset N) S b A) : sub Z (theta (carR i s N) A)=theta (carR i s₂ P) (sub z A) := by
  have ht:= exchanges_halves i s N
  let R:=carR i s N
  induction h with
  | empty=> rw [theta_zero,map_zero,map_zero,theta_zero]
  | one=> rw [theta_one,sub_one,sub_one,theta_one]
  | seed k v=>
    by_cases p:k∈ Tset N
    · have hg:= (within_basis (Tset N) k p); rw [show (think (Tset N)).term k=put k from if_pos p,← create_put,theta_upV, sub_create G j Q M ho z hg, theta_upV, map_smul]
      have hp:withinM (Tset N)ᶜ (acts R.val (basisKet k)) := by unfold withinM; rw [←Fine.altitude ht,←Fock.swivel,hg]
      rw [sub_remove G j Q M ho Z hp]; congr 2; exact commute_mode G j Q M ho i s z _ true
    have g := within_basis (Tset N)ᶜ k (mem_compl.mpr p)
    have hp:withinM (Tset N) (acts R.val (basisKet k)) := by unfold withinM; rw [←ht,←Fock.swivel,g]
    rw [show (think (Tset N)).term k= -takeF k from if_neg p, ← remove_take]
    have H {p:Side} (s : ℤ) (A : FC (Single p)) : theta (carR i s p) (-A)= -theta (carR i s p) A := by simp [theta]
    rw [H,map_neg,map_neg,H,theta_downV,map_smul,sub_remove G j Q M ho z g,sub_create G j Q M ho Z hp,theta_downV]; congr 3; exact commute_mode G j Q M ho i s z _ false
  | grow e h ih it=>
    have x {T : FC (Single N)} {b} (p : Fine (Tset N) S b T): Fine (Tset N) (modesIn N (Finset.univ.image ((plane i s).anon N))) b (theta (carR i s N) T) := refl_fine i s _ _ _ (fine_enlarge (by rw [modes_univ]; exact subset_univ _) p)
    rw [theta_mul, sub_mul G j Q M ho Z (x e) (x h), sub_mul G j Q M ho z e h, theta_mul, ih,it]
  | add _ _ ih it=> rw [theta_add,map_add,map_add,theta_add,ih,it]
  | scale _ _ ih=> rw [theta_smul,map_smul,map_smul,theta_smul,ih]
end YM.CF.Buffered.Advance
