import GaugeFieldConstruction.CloverSymmetryMask
import GaugeFieldConstruction.VectorPV
/-!
# Gauge mask removes matter and unit

Allows an arbitrary Wick-frame *centralizer*, as can arise from registration and transport.
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
open Empire
def derivativeF (left : Bool) (i : FlavorIndex) (a b : Axis) : UV four := FslotPV four i
    ((DeckF four).issue (ket (Sum.inr (a,if left then Sum.inl b else Sum.inr b))))

lemma fWarp (v : UF four) (s : Signed) (h : signBit s = false) (i : FlavorIndex) :
    spinFrame four s (FslotPV four i v) = FslotPV four i ((Calibration.matter four).moves s v) := by
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext (funext fun b=>?_) (funext fun b=>?_)))
  · exact map_zero ((gauge four).moves s)
  · rw [tuneF, show Calibration.rev s b = b from by simp [Calibration.rev,h], riseInPV,riseInPV]
    split_ifs <;> simp
  exact map_zero ((mixed four).moves s)

lemma derivWarp (left : Bool) (s : Signed) (h : signBit s = false) (i : FlavorIndex) (a b) :
    spinFrame four s (derivativeF left i a b) =
      pay ((s.flip a).xor (s.flip b)) (derivativeF left i (s.perm a) (s.perm b)) := by
  simp only [derivativeF,fWarp _ s h]
  let z : BoxF four := Sum.inr (a,if left then Sum.inl b else Sum.inr b)
  let D := DeckF four
  rw [← show D.issue (beacon D.label s (ket z)) = _ from Mint.respect D (matter four).toCarries s _]
  unfold beacon
  rw [on_ket]
  have hc : D.label.cost s z = (s.flip a).xor (s.flip b) := by
    unfold D z
    cases left <;> simp [DeckF,RawBank.Mint.cup,RawBank.F1, Labels.tensorProd,
      Labels.twist, Labels.directSum,Raw.f4Act,h]
  rw [hc]; cases (s.flip a).xor (s.flip b) <;> simp only [pay_true,pay_false,map_neg]
  all_goals cases left <;> rfl

-- left generic Bool
lemma vectorWarp4 (s : Signed) (h : signBit s = false) (i : FlavorIndex) (a) :
    spinFrame four s (SpinSlot4 i a) = pay (s.flip a) (SpinSlot4 i (s.perm a)) := by
  unfold SpinSlot4
  rw [fWarp _ s h]
  let z : BoxF four := Sum.inl a; let D:= DeckF four
  rw [← show D.issue (beacon D.label s (ket z)) = _ from Mint.respect D (matter four).toCarries s _]
  unfold beacon
  rw [on_ket]
  rw [show D.label.cost s z = s.flip a from by change (signBit s).xor _ = s.flip a; rw [h,Bool.false_xor]; try rfl]
  cases s.flip a <;> simp only [pay_true,pay_false,map_neg] <;> rfl

lemma vectorKill (i a): feat (SpinSlot4 i a)=0 := by
  rcases show a=0 ∨ a=1 ∨ a=2 ∨ a=3 from (by fin_cases a <;> decide) with rfl|rfl|rfl|rfl
  · apply passKill_r
    · rw [vectorWarp4 _ (by decide : signBit move_r = false)]; clover_movers
  · apply passKill_s
    · rw [vectorWarp4 _ (by decide : signBit move_r = false)]; clover_movers
    · rw [vectorWarp4 _ (by decide : signBit move_s = false)]; clover_movers
  · apply passKill_t
    · rw [vectorWarp4 _ (by decide : signBit move_r = false)]; clover_movers
    · rw [vectorWarp4 _ (by decide : signBit move_s = false)]; clover_movers
    · rw [vectorWarp4 _ (by decide : signBit move_t = false)]; clover_movers
  · apply passKill_r
    · rw [vectorWarp4 _ (by decide : signBit move_r = false)]; clover_movers
lemma derivativeKill0 (left i b) : feat (derivativeF left i 0 b) = 0 := by
  rcases show b=0 ∨ b=1 ∨ b=2 ∨ b=3 from (by fin_cases b <;> decide) with rfl|rfl|rfl|rfl
  · rw [keep3Gate]; rotate_left;
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
    · rw [derivWarp _ _ (by decide : signBit move_s = false)]; clover_movers
    · rw [derivWarp _ _ (by decide : signBit move_t = false)]; clover_movers
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply,map_add, Bool.xor_self, pay_false, derivWarp left _ (by decide : signBit move_m = false),
      derivWarp left _ (by decide : signBit move_n = false),
      derivWarp left _ (by decide : signBit move_l = false)]
    clover_movers
    abel
  · apply passKill_r
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
  · apply passKill_r
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
  · apply passKill_s
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
    · rw [derivWarp _ _ (by decide : signBit move_s = false)]; clover_movers
lemma derivativeKill1 (left i b) : feat (derivativeF left i 1 b) = 0 := by
  rcases show b=0 ∨ b=1 ∨ b=2 ∨ b=3 from (by fin_cases b <;> decide) with rfl|rfl|rfl|rfl
  · apply passKill_r
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
  · rw [keep3Gate]; rotate_left;
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
    · rw [derivWarp _ _ (by decide : signBit move_s = false)]; clover_movers
    · rw [derivWarp _ _ (by decide : signBit move_t = false)]; clover_movers
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply,map_add, Bool.xor_self, pay_false, derivWarp left _ (by decide : signBit move_m = false),
      derivWarp left _ (by decide : signBit move_n = false),
      derivWarp left _ (by decide : signBit move_l = false)]
    clover_movers
    abel
  · apply passKill_s
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
    · rw [derivWarp _ _ (by decide : signBit move_s = false)]; clover_movers
  · apply passKill_r
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
lemma derivativeKill2 (left i b) : feat (derivativeF left i 2 b) = 0 := by
  rcases show b=0 ∨ b=1 ∨ b=2 ∨ b=3 from (by fin_cases b <;> decide) with rfl|rfl|rfl|rfl
  · apply passKill_r
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
  · apply passKill_s
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
    · rw [derivWarp _ _ (by decide : signBit move_s = false)]; clover_movers
  · rw [keep3Gate]; rotate_left;
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
    · rw [derivWarp _ _ (by decide : signBit move_s = false)]; clover_movers
    · rw [derivWarp _ _ (by decide : signBit move_t = false)]; clover_movers
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply,map_add, Bool.xor_self, pay_false, derivWarp left _ (by decide : signBit move_m = false),
      derivWarp left _ (by decide : signBit move_n = false),
      derivWarp left _ (by decide : signBit move_l = false)]
    clover_movers
    abel
  · apply passKill_r
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
lemma derivativeKill3 (left i b) : feat (derivativeF left i 3 b) = 0 := by
  rcases show b=0 ∨ b=1 ∨ b=2 ∨ b=3 from (by fin_cases b <;> decide) with rfl|rfl|rfl|rfl
  · apply passKill_s
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
    · rw [derivWarp _ _ (by decide : signBit move_s = false)]; clover_movers
  · apply passKill_r
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
  · apply passKill_r
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
  · rw [keep3Gate]; rotate_left;
    · rw [derivWarp _ _ (by decide : signBit move_r = false)]; clover_movers
    · rw [derivWarp _ _ (by decide : signBit move_s = false)]; clover_movers
    · rw [derivWarp _ _ (by decide : signBit move_t = false)]; clover_movers
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply,map_add, Bool.xor_self, pay_false, derivWarp left _ (by decide : signBit move_m = false),
      derivWarp left _ (by decide : signBit move_n = false),
      derivWarp left _ (by decide : signBit move_l = false)]
    clover_movers
    abel
lemma fSlotClears (i : FlavorIndex) (x : UF four) : feat (FslotPV four i x)=0 := by
  have h (z : BoxF four) : feat (FslotPV four i ((DeckF four).issue (ket z))) = 0 := by
    change PH⊕T1 at z
    rcases z with a | ⟨a,b | b⟩
    · exact vectorKill i a
    · fin_cases a
      · exact derivativeKill0 true i b
      · exact derivativeKill1 true i b
      · exact derivativeKill2 true i b
      exact derivativeKill3 true i b
    · fin_cases a
      · exact derivativeKill0 false i b
      · exact derivativeKill1 false i b
      · exact derivativeKill2 false i b
      exact derivativeKill3 false i b
  obtain ⟨x,rfl⟩:=(DeckF four).supply x
  exact LinearMap.congr_fun (ket_ext h : feat ∘ₗ FslotPV four i ∘ₗ (DeckF four).issue = 0) x

lemma unitClears : feat (one four) = 0 := by
  simp only [feat,Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,
    Module.End.one_apply,map_add,sends_1,sub_self,zero_add]

lemma maskCost (v : UV four) : feat v = feat (gin v.2.1) := by
  let F (i : FlavorIndex) := v.2.2.1 i
  have h : v = v.1 • (one four) + gin v.2.1 + ∑ i:FlavorIndex, FslotPV four i (F i) := by
    apply Prod.ext
    · simp only [Prod.fst_add,Prod.fst_smul]; have h : (∑ i:FlavorIndex, FslotPV four i (F i)).1 = 0 := by
        change readOne four (∑ i, FslotPV four i (F i)) = 0; rw [map_sum]; exact Finset.sum_eq_zero (fun _ _=>rfl)
      rw [h]; simp [Empire.one,gin]
    apply Prod.ext
    · have h : (∑ i:FlavorIndex, FslotPV four i (F i)).2.1 = 0 := by
        let Q : UV four →ₗ[ℂ] UG four:= (LinearMap.fst ℂ _ _) ∘ₗ LinearMap.snd ℂ _ _
        change Q (∑ i, FslotPV four i (F i)) = 0
        rw [map_sum]; exact Finset.sum_eq_zero (fun _ _=>rfl)
      simp only [Prod.snd_add,Prod.fst_add,Prod.snd_smul,Prod.fst_smul,h]
      change _ = _ • (0: UG four) + v.2.1 + 0; simp
    refine Prod.ext (funext fun b=>?_) (funext fun b=>?_)
    · let Q : UV four→ₗ[ℂ] UF four:= (LinearMap.proj (R:=ℂ) b) ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _
      change F b=Q (_+_+ ∑ i:FlavorIndex,_)
      rw [map_add,map_add,map_sum,Q.map_smul,show Q (one four)=0 from rfl,show Q (gin v.2.1)=0 from rfl,smul_zero,zero_add,zero_add,Finset.sum_eq_single b]
      · rw [show Q (FslotPV four b (F b)) = _ from riseInPV four b b, if_pos rfl]
      · intro i _ h; rw [show Q (FslotPV four i (F i)) = _ from riseInPV four i b,if_neg h]
      simp
    haveI : Subsingleton (UX four) := inferInstanceAs (Subsingleton ↥(⊥:Submodule ℂ _))
    exact Subsingleton.elim ..
  nth_rw 1 [h]
  simp only [map_add,map_smul,map_sum,unitClears,smul_zero,zero_add,fSlotClears,
    Finset.sum_const_zero,add_zero]

theorem maskPass (v : UV four) : feat v ∈ orbitSpin2 := by rw [maskCost]; exact gaugePass _

end YM.GaugeFieldConstruction.Stage.CloverSymmetry
end
