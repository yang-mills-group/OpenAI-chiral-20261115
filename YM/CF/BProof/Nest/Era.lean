import YM.CF.BProof.Nest.Ener
/-! Extents of native appeals, spatial halo tests and measure-queries. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Nest
open Stave Filter Function Metric Lattice Wilson Finset
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {n:Side}{q s:ℕ}{d u δ:ℝ}{G:Gauge}
local notation "Sκ"=>Site n
local notation "G_"=>SU.group
local notation "L_"=>Nerve.Halo
local notation "K_"=>Nerve.King
lemma reg_pay {x y:Sκ}{r c l:ℕ}(h:separation x y≤ c)(p:c+r≤ l): region n y r ⊆ region n x l:= fun i hi=> (reg_in ..).2 ((separation_triangle x y i).trans ((Nat.add_le_add h (reg_in ..|>.1 hi)).trans p)) -- k unused
lemma reg_arc {x:Sκ}{r k:ℕ}(p:r≤k):region n x r⊆ region n x k := fun i hi=>(reg_in ..).2 (((reg_in ..).1 hi).trans p)
lemma clear_m {U:Config G n} {x y:Sκ}{r b c:ℕ}(h:Clear u r U x)(g:separation x y≤ c)(p:c+b≤ r): Clear u b U y:= h.mono_right (reg_pay g p)
lemma clear_s {U:Config G n}{x:Sκ}{r k:ℕ}(h:Clear u r U x)(p:k ≤ r): Clear u k U x:=h.mono_right (reg_arc p)
lemma clear_borel (u:ℝ)(r:ℕ)(x:Sκ): MeasurableSet {U:Config G n| Clear u r U x}:=by rw [show {U: Config G n| _}={U| RG.Healthy u (region n x r) U} from ?_]; exact (RG.healthy_closed ..).measurableSet; ext; exact disjoint_comm
lemma clear_cost (u:ℝ)(r:ℕ)(x:Sκ): LocalOn (region n x (r+10)) (fun U:Config G n=> Clear u r U x):=by
 intro U V p; unfold Clear; have h:= RG.flags_agree u U V (region n x r) (agrees_mono p ?_) -- goal issue have inferred ?_
 · apply propext; dsimp only; rw [disjoint_comm, Finset.disjoint_iff_inter_eq_empty, h,←Finset.disjoint_iff_inter_eq_empty,disjoint_comm]
 intro i hi; obtain h|h := mem_union.mp (show i∈ RG.inspected (region n x r) from hi); exact reg_arc (Nat.le_add_right ..) h; obtain ⟨v,_,hk⟩:= mem_biUnion.mp h; split at hk; simp at hk; rename_i H; obtain ⟨j,hj,p⟩:= Finset.not_disjoint_iff.mp H; rw [reg_in] at hj; have hp:=Work.E01.sep_touched v i hk; have he:=Work.E01.sep_touched v j p; apply (reg_in ..).2; have ht:=separation_triangle x j i; have ha:=separation_triangle j v.1 i; rw [separation_comm v.1 j] at he; omega
variable {W:Wool n q}(t:W.Rub s d)(O:Vent n)(U:Config SU.group n)
namespace Wool
include t
abbrev saved(s:ℕ):=Nerve.King*s+L_*s
abbrev palm(s:ℕ):=saved s+1
theorem phase (o:0<s)(p:Nerve.SmallN s n)(g:0≤δ)(Q:Law G_ u δ (K_*s))(x:Sκ)(i:Axis) (h:Clear u (saved s) U x): dist (roll (native W O U x) (U (x,i))) (native W O U (x+step i))≤5 * Wool.cash d δ:= Wool.along O U t g o p Q x i (fun j hj=> clear_m h (t.mom x j hj) (Nat.add_comm _ _ ▸ le_rfl))
theorem succV (o:0<s)(p:Nerve.SmallN s n)(g:0≤δ)(Q:Law G_ u δ (K_*s))(x:Sκ)(i:Step)(h: Clear u (palm s) U x): Like (5 * cash d δ) (W.native O U x) (W.native O U (x+i.vec)):=by
 obtain ⟨i,f|f⟩:=i; exact ⟨U (x,i),phase t O U o p g Q _ _ (clear_s h (by unfold palm; omega))⟩
 let y:=x-step i; change Like (5 * cash d δ) _ (W.native O U (x+ -step i)); rw [← sub_eq_add_neg]; have ht : x=y+step i:=(sub_add_cancel x _).symm; apply Like.symm; nth_rw 1 [show x-step i=y from rfl]; nth_rw 1 [ht]; exact ⟨U (y,i),phase t O U o p g Q _ _ (clear_m h (c:=1) (by rw [separation_comm, ht]; exact nearV y (posDir i)) (by unfold palm; omega))⟩
-- any read x to y via unwrapped march. **No** wrap requirement; retain charge through other lemma.
theorem chargeMat (o:0<s)(p:Nerve.SmallN s n)(g:0≤δ)(Q:Law G_ u δ (K_*s))(x y:Sκ){r:ℕ}(u':separation x y≤r)(h: Clear u (palm s+4*r) U x): Like ((5*cash d δ)*(4*r)) (W.native O U x) (W.native O U y):=by
 let F:=native W O U; let A:=5*cash d δ; have hz:0 ≤ A:=by unfold A cash; positivity
 have he(w:Walk)(x:Sκ)(h:Clear u (palm s+w.length) U x): Like (A*w.length) (F x) (F (stop x w)):=by
    induction w generalizing x with
    | nil=> exact ⟨1,by simp [stop]⟩
    | cons d w ih=> exact (Like.trans (succV t O U o p g Q x d (clear_s h (by omega))) (ih _ (clear_m h (nearV x d) (by rw [List.length_cons]; omega)))).weaken (by simp only [List.length_cons,Nat.cast_add, Nat.cast_one]; unfold A; exact le_of_eq (by ring))
 have hk:= Cube.march_len x y 1 ((separation_comm ..).trans_le u'); let Z:= Cube.march x y 1; nth_rw 1 [← Cube.arrive x y 1]; apply (he Z x (clear_s h (Nat.add_le_add_left hk _))).weaken (mul_le_mul_of_nonneg_left _ hz); exact_mod_cast hk
end Wool
end YM.CF.BProof.Mesh.Nest
