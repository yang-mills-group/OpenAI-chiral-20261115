import GaugeFieldConstruction.Cop
/-!
# f has polar vector H-only but none when active: do test on the unique W
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage.Count
open Calibration Calibration.RawBank Cauchy Row Record Phys Function Filter Set Wide Cell Flux One Raw
open U1 hiding VV
open scoped BigOperators Topology Matrix
abbrev Mv:=Axis

abbrev mH := (matter Floor.five).moves
def bills (i : Axis):= foldP (i,Sum.inr (Sum.inr (i,i)))
lemma supplyW (i): bills i∈SF Floor.five:= (show space foldP ≤ SF Floor.five from by rw [pagesF]; exact le_sup_right) (range_sets ..) -- dots
def Ws (i:Axis) : UF Floor.five := ⟨bills i,supplyW i⟩
lemma vectorized (i) (s : Signed): mH s (Ws i)=pay (s.flip i) (Ws (s.perm i)) := by
  apply Subtype.ext; apply ext_jet ph.faith; intro w; obtain ⟨u,h⟩:=ph.permit s w
  rw [← (matter Floor.five).transit h]
  have he:= stem.moving s w u h (i,.inr (.inr (i,i)))
  change ph.tester _ _=pay (((signBit s).xor (s.flip i)).xor ((s.flip i).xor ((signBit s).xor (s.flip i)))) (ph.tester _ (bills (s.perm i))) at he
  cases Q:s.flip i <;> cases P:signBit s <;> simp only [P,Q,Bool.false_xor,Bool.true_xor,Bool.not_false, Bool.not_true,pay_true,pay_false] at he ⊢
  · exact he
  · exact he
  all_goals exact he.trans (map_neg ..).symm
lemma registered : (fun i=> (Ws i).val)∈WW ph fFive:= ⟨((matter Floor.five).toCarries.turn_field Raw.v _).mpr (fun s i=>vectorized i s),fun i _=>supplyW i⟩

open Vouchers Camera Bill
def w₂ := Ortho.plane 1 0
lemma rotate₀ :
    (YF Floor.five w₂ (Ws 0)).val= foldP (1,Sum.inr (Sum.inr (0,0))) + (foldP (0,Sum.inr (Sum.inr (1,0))) + foldP (0,Sum.inr (Sum.inr (0,1)))) := by
  let i:T2:=(0,Sum.inr (Sum.inr (0,0)))
  let j : BoxF Floor.five:= Sum.inr i
  have He : (Ws 0)= (DeckF _).issue (ket j):= Subtype.ext (Eq.symm ((DeckF _).paid_at j))
  rw [He,visitF]
  change jet ( (FB.cup F1|>.cup F2).q) ((Cell.sum (Cell.sum UnitV PT1) PT2).beta _ (ket (.inr i)))=_
  rw [input2,monopol]; change jet foldP (PT2.beta w₂ (ket i))=_; dsimp only [i]; rw [PT2,fork_cost,input2,monopol,input2,monopol,Theta,fork_cost]; simp only [motion]
  have hv {A : Type} [AddCommGroup A] [Module ℂ A] (f : Axis → A) : ∑ j:Axis,(w₂.val j 0:ℂ) • f j=f 1:=by
    rw [Finset.sum_eq_single 1]; simp [w₂,Ortho.plane]
    intro b _ p; simp [w₂,Ortho.plane,p,Ne.symm p] 
    simp
  rw [hv,hv,hv]

lemma distinct_tick : (YF Floor.five w₂ (Ws 0))≠ Ws 1 := by
  intro h; have He := congr_arg Subtype.val h; rw [rotate₀] at He
  -- decide pay matrix click using Vouchers at row location
  let S (i j k:Axis) := (Camera.f5Cost (i,Sum.inr (Sum.inr (j,k))))
  have H (i j k) : foldP (i,Sum.inr (Sum.inr (j,k)))=total (S i j k):= (face5 (i,Sum.inr (Sum.inr (j,k)))).symm
  change _= foldP (1,Sum.inr (Sum.inr (1,1))) at He; simp_rw [H] at He
  have hv : total ((S 1 0 0)++((S 0 1 0)++(S 0 0 1))++spend (-1) (S 1 1 1))=0 := by
    rw [total_append,total_append,total_append, Bill.cost]; simp only [Credit.opposite, Credit.one_c, neg_smul,one_smul,He]; simp
  -- use explicit key from Python
  let t: Row.f:=((0, (2,0,0)),(1,0,0,0))
  have hq:= congr_arg (fun w : J Row.f=>w t) hv
  rw [← spendable] at hq
  apply Credit.nonzero _|>.mpr ?_ hq; unfold S t; decide +kernel

lemma resists : (fun i=> (Ws i).val)≠0 := by
  intro h
  have c i :Ws i=0:=Subtype.ext (congr_fun h i)
  apply distinct_tick; rw [c,c,map_zero]

local instance iA : AddCommGroup (UF Floor.five):= @Submodule.addCommGroup ℂ (J f) _ _ _ _
lemma fred (V : Axis→ UF Floor.five) (p : ∀ s i,mH s (V i)=pay (s.flip i) (V (s.perm i))) (v : rotates (YF Floor.five) V) : V=0 := by
  let U:=WW ph fFive
  letI iV:AddCommGroup ↥U:=@Submodule.addCommGroup ℂ (Axis→J f) _ _ _ _
  haveI := Module.Free.of_divisionRing ℂ ↥U
  haveI k : Module.Finite ℂ U := Module.finite_of_finrank_pos (R:=ℂ) (by change 0<Module.finrank ℂ U; rw [show Module.finrank ℂ U=1 from f_ranks.2.2.1]; norm_num)
  have H: U=Submodule.span ℂ {(fun i=> (Ws i).val)}:= Eq.symm (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem ..).mpr registered) (by rw [finrank_span_singleton resists]; exact f_ranks.2.2.1.symm)) -- qualify
  have hv :(fun i=>(V i).val)∈U:= ⟨((matter Floor.five).toCarries.turn_field Raw.v _).mpr p, fun i _=> (V i).property⟩
  rw [H] at hv; obtain ⟨c,hc⟩:= Submodule.mem_span_singleton.mp hv
  have ht i : V i=c • Ws i:=Subtype.ext (congr_fun hc.symm i)
  suffices c=0 by ext1 i; rw [ht,this,zero_smul]; rfl
  have he := v w₂ 0; rw [Finset.sum_eq_single 1] at he; swap
  · intro b _ p; simp [w₂,Ortho.plane,p,Ne.symm p]
  rotate_left 1
  · simp
  have e : w₂.val 1 0=1:=by simp [w₂,Ortho.plane]
  rw [e] at he; norm_num [one_smul] at he
  rw [ht 0, ht 1,map_smul] at he
  by_contra l; exact distinct_tick (smul_right_injective (UF Floor.five) l he) -- module
end YM.GaugeFieldConstruction.Stage.Count
