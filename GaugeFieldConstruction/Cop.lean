import GaugeFieldConstruction.Floats
/-!
# Other numerical facts for exclusion. Relate `H` and active spin from the lemma.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Calibration RawBank Floor Cauchy Row Record Function Set Filter Raw
open scoped Matrix BigOperators
namespace Count

-- proper signed vector relation from Lie criterion.
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def rotates (R : Rotors → Module.End ℂ V) (f : Axis→V) := ∀ s i, R s (f i)=∑ j:Axis,(s.val j i:ℂ) • f j
def passes (H : Signed→*Module.End ℂ V) (v : Raw.VS→V):=∀ s i, H s (v i)=pay (Raw.vsAct.cost s i) (v (Raw.vsAct.move s i))

--
lemma survives [Module.Finite ℂ V] (R : SO→* Module.End ℂ V) (r :Rotors → Module.End ℂ V) {f:Axis→V}
    (H: ∀ u x t,Sends (fun t=>R (Angles.rise u t) x) t (r u (R (Angles.rise u t) x))) (g : rotates r f) (s : Signed) (p:signBit s=false) i : R (signMot s p) (f i)=pay (s.flip i) (f (s.perm i)) := by
  let F:= jet f
  let S := Cell.UnitV.rotate.comp orbit.subtype
  have he R : F ∘ₗ Cell.beta Cell.UnitV R=r R ∘ₗ F:= ket_ext (fun i=> by simp only [LinearMap.comp_apply, Cell.betaV,F, map_sum,map_smul,on_ket,g R i])
  have ht:= follows (R:=S) (r:=Cell.UnitV.beta) (fun u x t=>Cell.UnitV.globe u x t) H F he (signMot s p)
  have hp : S (signMot s p) (ket i)=pay (s.flip i) (ket (s.perm i)) := by
    change Cell.bill s.ortho.val _=_; rw [Cell.axis_l ..]; unfold Cell.beacon; rw [on_ket]; rfl
  have h:= LinearMap.congr_fun ht (ket i)
  dsimp only [F] at h; rw [LinearMap.comp_apply,hp,LinearMap.comp_apply,on_ket] at h
  cases k:s.flip i <;> simpa [k] using h.symm
lemma disabled [Module.Finite ℂ V] (R: SO→* Module.End ℂ V) (r: Rotors→Module.End ℂ V) {v:V}
    (h:∀ u x t,Sends (fun t=>R (Angles.rise u t) x) t (r u (R (Angles.rise u t) x))) (hp:∀ u,r u v=0) (s : SO) : R s v=v := by
  apply SO_compute s (p:=fun s=>R s v=v)
  · intro u t
    let Q:=h u v
    have he: (fun t=> R (Angles.rise u t) v)=(fun _=>v):= captain (r u) _ _ Q (fun t l=>by
      change HasDerivAt (fun _ : ℝ=> l v) (l (r u v)) t; rw [hp,map_zero]; exact hasDerivAt_const ..) (by rw [show Angles.rise u 0=1 from Subtype.ext (YM.Work.A13.oneParameter_zero _),map_one]; rfl)
    exact congr_fun he t
  · rw [map_one]; rfl
  · intro a b h p; rw [map_mul,Module.End.mul_apply,p,h]
  intro s h; nth_rw 1 [←h]; rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one]; rfl

def rotPay (H : Signed →* Module.End ℂ V) (f : Axis→V):=∀ s:Signed,signBit s=false→∀ i,H s (f i)=pay (s.flip i) (f (s.perm i))

def M (i j : Axis) := Signed.mirror i*Signed.mirror j
@[simp] lemma M_perm (i j k:Axis): (M i j).perm k=k:=rfl
@[simp] lemma M_pos (i j): signBit (M i j)=false:=by simp [M,signBit_mul]
@[simp] lemma M_no (i j k:Axis) (p:i≠k) (q:j≠k): (M i j).flip k=false:=by simp [M,Signed.mirror, p,q, Ne.symm p,Ne.symm q]
lemma M_on (i j) (p:i≠j): (M i j).flip i=true := by simp [M, Signed.mirror,p,Ne.symm p]

def sw (i j:Axis):Signed:= if i=j then 1 else Signed.mirror j * unsigned (Equiv.swap i j)
lemma sw_pos (i j) : signBit (sw i j)=false:= by
  unfold sw; split_ifs with h
  · simp
  simp [signBit_mul,signBit_swap _ _ h]
lemma sw_apply (i j): (sw i j).perm i=j:= by unfold sw; split_ifs with h <;> simp [*,unsigned,Signed.mirror] -- tune

def allf: Signed:= diagonalFlip (fun _=>true)
lemma all_yes : signBit allf=false:=by decide
lemma peel (s : Signed) (f : Raw.Sym→ V) (h: ∀ v, f v=pay (symAct.cost s v) (f (symAct.move s v))) (i j):
    f (ordered i j)= pay ((s.flip i).xor (s.flip j)) (f (ordered (s.perm i) (s.perm j))) := by
  have hp:=h (ordered i j); rwa [fee_turn,sym_turn] at hp
lemma badge {H : Signed→*Module.End ℂ V} {v : Raw.VS→V} (u : passes H v) (h : ∀ i,rotPay H (fun k=> v (k,i)))
    (i : Axis) (s : Signed) (p:signBit s=false) (k l) :
    v (i,ordered k l)= pay ((s.flip k).xor (s.flip l)) (v (i,ordered (s.perm k) (s.perm l))) := by
  apply peel s (fun q=>v (i,q))
  intro q
  let j:= s.perm.symm i; have he:=u s (j,q); have hv:s.perm j=i:=by simp [j]
  rw [h q s p j] at he -- maybe change first
  change pay (s.flip j) (v (s.perm j,q))=pay ((s.flip j).xor (symAct.cost s q)) (v (s.perm j,symAct.move s q)) at he
  rw [hv,← pay_comp (α:=V)] at he
  simpa only [pay_pay] using congr_arg (pay (s.flip j) (α:=V)) he
lemma third (i j : Axis): ∃ v:Axis,v≠i∧v≠j := by fin_cases i <;> fin_cases j <;> decide
lemma negate {x : V} (h:x= -x) : x=0 := by
  have ht : (2:ℂ) • x=0:=by rw [two_smul]; nth_rw 1 [h]; simp
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
lemma isotrope {H : Signed→* Module.End ℂ V} {v:Raw.VS→V} (p: passes H v) (h:∀ i, rotPay H fun k=>v (k,i)) (k) (a b:Axis): v (k,ordered a b)= if a=b then v (k,ordered (0:Axis) 0) else 0:= by
  skip
  split_ifs with g
  · subst b; have he:= badge p h k (sw a 0) (sw_pos a 0) a a; simpa only [Bool.xor_self,pay_false,sw_apply] using he
  obtain ⟨c,u,t⟩:= third a b
  have he:= badge p h k (M a c) (M_pos ..) a b
  rw [M_perm,M_perm,M_no _ _ _ g t, M_on _ _ (Ne.symm u)] at he; exact negate he
lemma trace_deletes {H:Signed→*Module.End ℂ V} {v:VS→V} (p : passes H v) (h:∀ i,rotPay H fun k=>v (k,i)) (u:∀ k,∑ b:Axis,v (k,ordered b b)=0): v=0:=by
  ext1 ⟨s,t⟩; rw [← ordered_same t,isotrope p h]; split_ifs
  · have he:=u s; rw [show (∑ b:Axis, v (s,ordered b b))=(∑ _b:Axis,v (s,ordered 0 0)) from Finset.sum_congr rfl (fun b _=> (isotrope p h s b b).trans (if_pos rfl))] at he; apply (show v (s,ordered 0 0)=0 from ?_)
    have ht: (4:ℕ) • v (s,ordered 0 0)=0 := by simpa only [Finset.sum_const, Finset.card_univ,Fintype.card_fin] using he
    have hp: ((↑(4:ℕ)):ℂ) • v (s,ordered 0 0)=0 := by rw [Nat.cast_smul_eq_nsmul]; exact ht
    exact (smul_eq_zero.mp hp).resolve_left (by norm_num)
  rfl
end Count
end YM.GaugeFieldConstruction.Stage
