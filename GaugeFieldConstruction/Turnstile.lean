import GaugeFieldConstruction.Keeping

/-!
# Mirror 3 with c, semiscalar involution, as ordinary jet prescription in W2.
- R1: both matter letters exchange with −i in the *original order*. To
 put the output back in C R order, transpose with a minus sign, and the scalar on that pair becomes +1.
  Verify eg Mixed minus on *T* after reindexing. No signs inserted by hand into payments under Signed action.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Mirror
open Cauchy Row Calibration Conj Function Finset Submodule Phys
open scoped BigOperators
variable {α β : Type*}
local notation "Z" => J FIndex
abbrev mirror := Signed.mirror τ
abbrev clock (k : Axis) := mirror.flip k
@[simp] lemma turn₁ (i : S3) : clock i.castSucc=false := by fin_cases i <;> decide
@[simp] lemma turn₂ : clock τ=true := by decide

def slight : Flip GIndex := comb fun i=> pay (!i.1) (ket i)
lemma s_k (i : GIndex): slight (ket i)=pay (!i.1) (ket i) := onet ..
lemma s_at (t i n) : slight (G t i n)=pay (!t) (G t i n) := by
  unfold G; split_ifs
  · exact s_k _
  rw [map_neg,map_add,s_k,s_k]; cases t <;> dsimp only <;> simp [add_comm]

lemma time_G (k : Axis) (w : GJet) : slight (Gder k w)=pay (clock k) (Gder k (slight w)) := by
  have h : slight ∘ₛₗ Gder k=pay (clock k) (Gder k ∘ₛₗ slight) := by
    apply ksets; intro i
    rw [LinearMap.comp_apply]
    refine Fin.lastCases (i:=k) ?_ fun t=> ?_
    · change slight (Gder τ (ket i))= pay (clock τ) (Gder τ ∘ₛₗ slight) (ket i)
      rw [turn₂,Glast,pay_true,LinearMap.neg_apply,LinearMap.comp_apply,Gtime,on_ket]
      dsimp only; rw [map_sub,s_at,s_at,s_k]; cases he:i.1 <;> simp [he] <;> abel
    rw [Gspace,Gshift,on_ket,s_at,turn₁,pay_false,LinearMap.comp_apply,s_k]
    cases Bool.not i.1 <;> simp
  have ht:= LinearMap.congr_fun h w
  cases p:clock k <;> rw [p] at ht <;> exact ht

/-- row reflects to column. Excludes the −i already explained. -/
lemma time_F (p : J FIndex) (b : Bool) (k) : tr FIndex (Cder b k p)=pay (clock k) (Cder (!b) k (tr FIndex p)) := by
  have H : tr FIndex ∘ₛₗ Cder b k= pay (clock k) (Cder (!b) k ∘ₛₗ tr FIndex) := ksets (fun i=>by
    rw [LinearMap.comp_apply]; refine Fin.lastCases (i:=k) ?_ fun u=>?_
    · change tr _ (Cder _ τ _)=pay (clock τ) (Cder _ τ ∘ₛₗ tr FIndex) (ket i)
      have hp (a c) (k : S3) : bar (coeffCR b k.castSucc a c) = -coeffCR (!b) k.castSucc a c := by
        cases b <;> fin_cases k <;> fin_cases a <;> fin_cases c <;> norm_num [bar,coeffCR,Hij] <;> rfl
      rw [turn₂, pay_true,Clast,Clast, LinearMap.neg_apply,LinearMap.comp_apply,tr_ket,Ctime,on_ket,Ctime,on_ket]
      simp_rw [map_neg,map_sum,LinearMap.map_smulₛₗ,C,tr_ket,hp,neg_smul, sum_neg_distrib]
    rw [turn₁,pay_false,LinearMap.comp_apply,Cspace,Cshift,on_ket,tr_ket,Cspace,Cshift,on_ket]; exact tr_ket _) -- tweak
  have e:=LinearMap.congr_fun H p; cases ht:clock k <;> rw [ht] at e <;> exact e

def flipF : Flip f := Phys.swap _ ∘ₛₗ body (tr _) (tr _)
def flipG := body slight slight
/-- minus on the *T* label since T maps real color to antihermitian. -/
def flipX := -(body flipF slight)
lemma flipPair (p q : J FIndex) : flipF (times' p q)=times' (tr _ q) (tr _ p) := by rw [flipF,LinearMap.comp_apply,portal, Phys.swap_apply]
lemma flipXPair (p q) : flipX (times' p q)= -times' (flipF p) (slight q) := by rw [flipX,LinearMap.neg_apply,portal]

lemma derives {u : Flip α} {v : Flip β} {a : Module.End ℂ (J α)} {b : Module.End ℂ (J β)} (g : Bool)
    (ha :∀ i,u (a i)=pay g (a (u i))) (hb :∀ i,v (b i)=pay g (b (v i))) (p) : body u v (splitD a b p)=pay g (splitD a b (body u v p)) := by
  have he: (body u v) ∘ₛₗ splitD a b=pay g (splitD a b ∘ₛₗ body u v) := ksets (fun i=>by
    rw [← takes i.1 i.2,LinearMap.comp_apply,split_legs,map_add,portal,portal,ha,hb]
    cases g <;> simp only [pay_true,pay_false,LinearMap.neg_apply,LinearMap.comp_apply,portal,split_legs,map_neg,LinearMap.neg_apply, LinearMap.map_smulₛₗ,neg_add])
  have p':= LinearMap.congr_fun he p; cases g <;> exact p'
lemma time_Pg (k) (w) : flipG (P_g k w)=pay (clock k) (P_g k (flipG w)) := derives _ (time_G k) (time_G k) w
lemma time_Pf (k) (p) : flipF (P_f k p)=pay (clock k) (P_f k (flipF p)) := by
  have he: flipF ∘ₛₗ P_f k=pay (clock k) (P_f k ∘ₛₗ flipF) := ksets (fun i=>by
    rw [← takes i.1 i.2,LinearMap.comp_apply,P_f,split_legs,map_add,flipPair,flipPair,time_F,time_F]
    cases hx: clock k <;> simp only [pay_true,pay_false, LinearMap.neg_apply,LinearMap.comp_apply, flipPair,map_neg, LinearMap.neg_apply,split_legs, Bool.not_true,Bool.not_false] <;> abel)
  have p' := LinearMap.congr_fun he p; cases hx:clock k <;> rw [hx] at p' <;> exact p'
lemma time_Px (k) (p) : flipX (P_x k p)=pay (clock k) (P_x k (flipX p)) := by
  rw [flipX,LinearMap.neg_apply]
  rw [P_x,derives (clock k) (time_Pf k) (time_G k)]; cases clock k <;> simp
lemma time_L (k) (p) : flipF (L k p)=pay (!(clock k)) (L k (flipF p)) := by
  have he: flipF ∘ₛₗ L k=pay (!(clock k)) (L k ∘ₛₗ flipF) := ksets (fun i=>by
    rw [← takes i.1 i.2,LinearMap.comp_apply,L,split_legs,map_add,flipPair,flipPair,LinearMap.neg_apply,map_neg,time_F,time_F]
    cases hx: clock k <;> simp only [pay_true,pay_false,LinearMap.neg_apply,LinearMap.comp_apply, flipPair,map_neg, LinearMap.neg_apply,split_legs, Bool.not_true,Bool.not_false] <;> simp <;> abel)
  have p' := LinearMap.congr_fun he p; cases hx:clock k <;> rw [hx] at p' <;> exact p'
open Raw
lemma undeF (i : F4) : f4Act.move mirror i=i := by rcases i with ⟨k,p|q⟩ <;> rfl
lemma undfF (i : F5) : f5Act.move mirror i=i := by
  rcases i with ⟨k,p|q|s⟩ -- syntax
  · change (k,Sum.inl (ordered p.val.1 p.val.2))=_; rw [ordered_same]
  · change (k,Sum.inr (Sum.inl (ordered q.val.1 q.val.2)))=_; rw [ordered_same]
  rfl
lemma undWd (w : Wed) : wedAct.move mirror w=w := blade_same w.toBlade  w.toBlade.property.ne
lemma undeG (i : G4) : g4Act.move mirror i=i := by rw [g4Act,Labels.sym_mv, undWd,undWd,ordered_same]
lemma undfG (i : G5) : g5Act.move mirror i=i := Prod.ext (undWd i.1) (Prod.ext (undWd i.2.1) rfl)
lemma undX (i : X5) : x5Act.move mirror i=i := Prod.ext rfl (undWd i.2)

lemma turnB (i : Axis) : flipF (B i)=pay (!(clock i)) (B i) := by
  rw [B, map_sum]; simp_rw [map_sum,LinearMap.map_smulₛₗ,flipPair,C,tr_ket]
  fin_cases i <;> simp [bar,Hij,clock,τ,Signed.mirror] <;> abel
lemma turnFB (i : Axis) : flipF (B i) = pay (f3Act.cost mirror i) (B (f3Act.move mirror i)) := by
  rw [turnB]; change pay (!(clock i)) _= pay (Bool.xor true (clock i)) _ -- bool notation?
  cases clock i <;> rfl
lemma T_arc (w : Wed) : slight (arc w)=pay (wedAct.cost mirror w) (arc w) := by
  change slight (arc w)=pay (v.exterior.cost _ _) _
  rw [Labels.wed_fee]; change _= pay ((Labels.reverseBit w.toBlade.val.1 w.toBlade.val.2).xor _) _
  rw [show Labels.reverseBit w.toBlade.val.1 w.toBlade.val.2=false from by simp [Labels.reverseBit,not_lt.mpr w.toBlade.property.le],Bool.false_xor]
  have he (i j : Axis) : slight (F i j)=pay ((clock i).xor (clock j)) (F i j) := by
    refine Fin.lastCases (i:=i) ?_ (fun s=>?_) <;> refine Fin.lastCases (i:=j) ?_ (fun a=>?_)
    all_goals simp only [F, Fin.lastCases_last, Fin.lastCases_castSucc, turn₁]
    · rw [map_zero,pay_zero]
    · change slight (G _ _ _)= -(G _ _ _); rw [s_at]; rfl
    · rw [map_neg,s_at]; change - -(G _ _ _)= - - (G _ _ _); rfl -- tweak
    split_ifs <;> simp [s_at]
  exact he ..
lemma Gb (i : G4) : flipG (evalTg i)=pay (g4Act.cost mirror i) (evalTg (g4Act.move mirror i)) := by
  rw [undeG,g4Act,Labels.sym_fee, evalTg,Bose,map_add,flipG,portal,portal]; simp_rw [T_arc]
  cases wedAct.cost mirror i.val.1 <;> cases wedAct.cost mirror i.val.2 <;> simp <;> abel
lemma Gp (i : G5) : flipG (evalG i)=pay (g5Act.cost mirror i) (evalG (g5Act.move mirror i)) := by
  rw [undfG,evalG,Bose,map_add,flipG,portal,portal]; simp_rw [time_G,T_arc]
  change _ = pay ((wedAct.cost mirror i.1).xor ((wedAct.cost mirror i.2.1).xor (clock i.2.2))) _
  cases wedAct.cost mirror i.1 <;> cases wedAct.cost mirror i.2.1 <;> cases clock i.2.2 <;> simp <;> abel
lemma Fb (i : F4) : flipF (evalTf i)=pay (f4Act.cost mirror i) (evalTf (f4Act.move mirror i)) := by
  rw [undeF]; rcases i with ⟨i,g|v⟩
  · change flipF (L g (B i)) = pay ((Bool.xor true (clock i)).xor (Bool.xor true (clock g))) _
    rw [time_L,turnB]; cases clock i <;> cases clock g <;> simp <;> rfl
  change flipF (P_f v (B i)) = pay ((Bool.xor true (clock i)).xor (clock v)) _
  rw [time_Pf,turnB]; cases clock i <;> cases clock v <;> simp <;> rfl
lemma Fp (i : F5) : flipF (evalF i)=pay (f5Act.cost mirror i) (evalF (f5Act.move mirror i)) := by
  rw [undfF]; rcases i with ⟨i,g|v|⟨p,q⟩⟩
  · let p:=g.val.1; let q:=g.val.2
    change flipF (L p (L q (B i)))=pay ((Bool.xor true (clock i)).xor ((Bool.xor true (clock p)).xor (Bool.xor true (clock q)))) _
    rw [time_L,time_L,turnB]; cases clock i <;> cases clock p <;> cases clock q <;> simp <;> rfl
  · let p:=v.val.1; let q:=v.val.2
    change flipF (P_f p (P_f q (B i)))=pay ((Bool.xor true (clock i)).xor ((clock p).xor (clock q))) _
    rw [time_Pf,time_Pf,turnB]; cases clock i <;> cases clock p <;> cases clock q <;> simp <;> rfl
  change flipF (P_f p (L q (B i)))=pay ((Bool.xor true (clock i)).xor ((clock p).xor (Bool.xor true (clock q)))) _
  rw [time_Pf,time_L,turnB]; cases clock i <;> cases clock p <;> cases clock q <;> simp <;> rfl
lemma Xp (i : X5) : flipX (evalX i) = pay (x5Act.cost mirror i) (evalX (x5Act.move mirror i)) := by
  rw [undX,evalX,flipXPair,turnB,T_arc]; change _=pay ((clock i.1).xor (wedAct.cost mirror i.2)) _
  cases clock i.1 <;> cases wedAct.cost mirror i.2 <;> simp
end YM.GaugeFieldConstruction.Mirror
