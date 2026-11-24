import GaugeFieldConstruction.RankClasses

/-!
# U1. Exactness and the derivatives at the free grades
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.U1
open Vouchers Cauchy Row Raw Record Submodule Module Function
open scoped BigOperators
variable {α β γ : Type*} (R : Record α β)

-- Injection. Use raising in spatial coordinate 0, and rotations on Θ arrays
private lemma raises (f : α → α) (u : β → β) (d : α → ℕ) (he : Injective f)
    (ht : ∀ i,d (f i)=d i+1) (F : J (α × β) →ₗ[ℂ] J (α × β))
    (h : ∀ (i : α×β),F (ket i)=ket (f i.1,i.2)+ket (i.1,u i.2)) : Injective F := by
  classical
  rw [← LinearMap.ker_eq_bot]; apply eq_bot_iff.mpr
  intro a hv; rw [LinearMap.mem_ker] at hv; rw [Submodule.mem_bot]
  by_contra H
  obtain ⟨⟨i,j⟩,k,e⟩ := Finset.exists_max_image a.support (fun x => d x.1) (Finsupp.support_nonempty_iff.mpr H)
  let p := (i,j)
  have hz : ∑ j ∈ a.support,a j • (ket j)=a := by
    ext1 x; rw [Finset.sum_apply'] -- check
    rw [Finset.sum_eq_single x]
    · simp [ket]
    · intro z _ m; simp [ket,m]
    simp [ket]
  have hs : F a (f i,j)=a p := by
    -- LH
    conv_lhs => rw [← hz,map_sum]
    simp only [map_smul,h, smul_add, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single_of_mem p k]; swap
    · rintro ⟨r,l⟩ W M
      have hm : r ≠ f i := fun t=> by have hr : d r ≤ d i := e _ W; rw [t,ht i] at hr; omega
      have h1 : (f r,l)≠(f i,j) := fun h=> M (Prod.ext (he (Prod.mk.inj h).1) (Prod.mk.inj h).2)
      simp only [Finsupp.add_apply, Finsupp.smul_apply, ket]; simp [hm, Finsupp.single_apply]
      intro h u; exact (h1 (Prod.ext h u)).elim
    have hu : i≠f i := fun p=> by have ht' := ht i; rw [← p] at ht'; omega
    simp [ket,Finsupp.single_apply,hu,p]
  rw [hv] at hs; exact Finsupp.mem_support_iff.mp k hs.symm

def gf (i : GIndex) : GIndex := (i.1,⟨(i.2.val.1, bump 0 i.2.val.2),i.2.property⟩)
def ff (i : FIndex) : FIndex := (i.1,bump 0 i.2)

lemma grow (i : GIndex) : Gder 0 (ket i)=ket (gf i) := by
  rw [← Chart.cast0, Gspace,Gshift,on_ket]; exact picked_G (gf i)
lemma fly (i : FIndex) (b : Bool) : Cder b 0 (ket i)=ket (ff i) := by
  rw [← Chart.cast0, Cspace,Cshift,on_ket]; rfl
lemma go_up : Injective (bump 0) := by intro i j he; simp [bump] at he; exact Prod.ext he.1 he.2
lemma driveG : Injective (recG.P 0) := raises gf gf (fun i => i.2.val.2.1) (by
    rintro ⟨i,a,ha⟩ ⟨j,b,hb⟩ h
    rcases Prod.mk.inj h with ⟨p,r⟩; exact Prod.ext p (Subtype.ext (Prod.ext (Prod.mk.inj (Subtype.mk.inj r)).1 (go_up (Prod.mk.inj (Subtype.mk.inj r)).2))))
  (fun _=>rfl) _ (fun i=> by change P_g _ _=_; rw [← takes i.1 i.2,P_g,split_legs,grow,grow,takes,takes])
lemma driveF : Injective (ph.P 0) := raises ff (fun i=> ff i) (fun i => i.2.1) (fun i j h=>
  Prod.ext (Prod.mk.inj h).1 (go_up (Prod.mk.inj h).2)) (fun _=>rfl) _ (fun i=>by
  change P_f _ _=_; rw [← takes i.1 i.2,P_f,split_legs,fly,fly,takes,takes])

-- For X codomain can still use this (outer last gauge raises). Not needed at grade four.
lemma release (A : Labels γ) (j : γ → J α) (h : j∈R.tensors A) (b : Axis)
    (walk : Injective (R.P 0)) (n : ℕ) (u : ∀ i,(R.P b)^[n] (j i)=0) : j=0 := by
  let g := unsigned (Equiv.swap b 0)
  have ht : g.perm b=0 := Equiv.swap_apply_left ..
  have he (i) : R.heatP γ j (0,i) = R.P 0 (j i) := rfl
  funext i
  obtain ⟨v,rfl⟩ := (A.equivMove g).surjective i; change j (A.move g v)=0
  apply walk.iterate n
  suffices ((R.P 0)^[n] (j (A.move g v)))=0 by
    rw [this]; exact (Function.IsFixedPt.iterate (map_zero _) _).symm
  apply R.faith
  intro w; obtain ⟨y,H⟩ := R.permit g w
  have p (k : ℕ) : R.tester y ((R.P b)^[k] (j v))=
      pay (A.cost g v) (R.tester w ((R.P 0)^[k] (j (A.move g v)))) := by
    induction k with
    | zero => exact fare h H v
    | succ k ih=>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have he := R.atP b _ _ g w y H _ ih
      rw [ht,show g.flip b=false from rfl, Bool.xor_false] at he
      exact he
  have v' := p n; rw [u v,map_zero] at v'
  rw [LinearMap.mem_ker]; simpa using congr_arg (pay (A.cost g v)) v'.symm

/-- Arrows -/
lemma dG (i : Axis) : gFour≤comap (recG.P i) gFive := by
  change space evalTg ≤ _
  rw [space,Fintype.range_linearCombination]; apply span_le.mpr
  rintro t ⟨u,rfl⟩
  change P_g i (evalTg u) ∈ gFive
  apply (show space evalG≤gFive from le_sup_right)
  rw [space,Fintype.range_linearCombination]
  have h (x y) : P_g i (Bose x y)=Bose x (Gder i y)+Bose y (Gder i x) := by
    unfold P_g Bose; simp only [map_add,split_legs]; abel
  rw [evalTg,h]; refine Submodule.add_mem _ (subset_span ?_) (subset_span ?_); exact ⟨(_,_,i), rfl⟩; exact ⟨(_,_,i),rfl⟩
lemma dF (i : Axis) : fFour≤comap (ph.P i) fFive := by
  refine sup_le ?_ ?_
  · rw [fThree,space,Fintype.range_linearCombination]; apply span_le.mpr
    rintro t ⟨j,rfl⟩
    change P_f i (B j)∈fFive
    apply (show space evalTf≤fFive from le_trans (show space evalTf ≤fFour from le_sup_right) le_sup_left)
    rw [space,Fintype.range_linearCombination]; exact subset_span ⟨(j,.inr i),rfl⟩
  rw [space,Fintype.range_linearCombination]; apply span_le.mpr
  rintro t ⟨j,rfl⟩
  change P_f i (evalTf j)∈fFive
  apply (show space evalF ≤ fFive from le_sup_right); rw [space,Fintype.range_linearCombination]
  apply subset_span
  rcases j with ⟨a,k|k⟩; exact ⟨_,eval_SL a i k⟩; exact ⟨_,eval_SS a i k⟩

variable (four five : Submodule ℂ (J α)) (H : ∀ i,four ≤ comap (R.P i) five)
include H
-- from T to (W,V). Include membership assertions
lemma earns {f} (ht : f∈TT R four) : (R.divP f,R.heatP Raw.Sym f)∈ (WW R five).prod (VV R five) :=
  ⟨⟨R.paid_div _ ht.1, fun i _ => by
    change R.divP f i∈five; rw [divT]; exact Submodule.sum_mem _ (fun j _=> H j (ht.2 _ (Set.mem_univ _)))⟩,
    ⟨R.chargeP symAct _ ht.1,fun i _=>H i.1 (ht.2 _ (Set.mem_univ _))⟩⟩

def arr (H : ∀ i,four ≤ comap (R.P i) five) : TT R four →ₗ[ℂ] ↥((WW R five).prod (VV R five)) := LinearMap.codRestrict _
  ((LinearMap.prod R.divP (R.heatP Raw.Sym)) ∘ₗ (TT R four).subtype) (fun c=> earns R _ _ H c.property) -- explicit
lemma economy (h : Injective (R.P 0)) : Injective (arr R four five H) := by
  intro x y e
  have hp := congr_arg (fun z : ↥((WW R five).prod (VV R five)) => Prod.snd (z.val : (Axis→J α) × (VS→ J α))) e
  apply Subtype.ext; ext1 i
  exact h (congr_fun hp (0,i))

def div_check := codiff R ∘ₗ ((WW R five).prod (VV R five)).subtype
lemma contained : LinearMap.range (arr R four five H) ≤ LinearMap.ker (div_check R five) := by
  rintro _ ⟨v,rfl⟩
  rw [LinearMap.mem_ker]
  change R.divA (R.heatP Raw.Sym v.val) - R.heatP Axis (R.divP v.val)=0
  rw [sub_eq_zero]
  ext1 a
  cases a with
  | mk i j=>
    rw [divV]
    change ∑ k : Axis,R.P k (R.P i _) = R.P i (R.divP _ _)
    rw [divT,map_sum]; apply Finset.sum_congr rfl
    intro k _; exact commuting R.faith _ _ (fun w=>R.bond w k) (fun w=>R.bond w i) _

-- finite rank exactness
omit H in
def gear : ((WW R five).prod (VV R five)) ≃ₗ[ℂ] ((WW R five) × (VV R five)) where
  toFun x := (⟨_,x.property.1⟩,⟨_,x.property.2⟩)
  invFun x:=⟨(x.1.val,x.2.val),⟨x.1.property,x.2.property⟩⟩
  left_inv _:=rfl; right_inv _:=rfl; map_add' _ _:=rfl; map_smul' _ _:=rfl
set_option synthInstance.maxSize 4000 in
lemma keyed (h : Injective (arr R four five H)) (p : FiniteDimensional ℂ (WW R five))
    (u : FiniteDimensional ℂ (VV R five)) (w :
    finrank ℂ (WW R five)+finrank ℂ (VV R five)=finrank ℂ (map (codiff R) ((WW R five).prod (VV R five)))+
      finrank ℂ (TT R four)) : LinearMap.range (arr R four five H) = LinearMap.ker (div_check R five) := by
  have ev := (gear R five).finrank_eq
  haveI := Module.Finite.equiv (gear R five).symm
  have hd : (arr R four five H).range ≤ (div_check R five).ker := contained R four five H
  refine @Submodule.eq_of_le_of_finrank_eq ℂ ↥((WW R five).prod (VV R five)) _ _ _ ((arr R four five H).range) ((div_check R five).ker) (@FiniteDimensional.finiteDimensional_submodule ℂ ↥((WW R five).prod (VV R five)) _ _ _ _ ((div_check R five).ker)) hd ?_
  rw [LinearMap.finrank_range_of_inj h]
  have he := @LinearMap.finrank_range_add_finrank_ker ℂ ↥((WW R five).prod (VV R five)) _ _ _ (Axis×Axis → J α) _ _ _ (div_check R five)
  have hr : (div_check R five).range = map (codiff R) ((WW R five).prod (VV R five)) := by rw [div_check,LinearMap.range_comp,range_subtype]
  rw [hr] at he
  haveI : Free ℂ ↥(WW R five) := Free.of_divisionRing ℂ ↥(WW R five)
  haveI : Free ℂ ↥(VV R five) := Free.of_divisionRing ℂ ↥(VV R five)
  rw [ev,Module.finrank_prod,w] at he
  exact (Nat.add_left_cancel he).symm

omit H in
lemma exact_g : LinearMap.range (arr recG gFour gFive dG)=LinearMap.ker (div_check recG gFive) := by
  refine keyed _ _ _ _ (economy _ _ _ _ driveG) ?_ ?_ ?_
  · rw [w_classG]; apply finite_line
  · rw [v_classG]; apply finite_line
  simp only [g_ranks]
omit H in
lemma exact_f : LinearMap.range (arr ph fFour fFive dF)= LinearMap.ker (div_check ph fFive) := by
  refine keyed _ _ _ _ (economy _ _ _ _ driveF) ?_ ?_ ?_
  · rw [w_classF]; apply finite_line
  · rw [v_classF]; apply finite_line
  simp only [f_ranks]
omit H in
lemma exact_x : LinearMap.range (arr recX xFour xFive (fun _=>bot_le))=LinearMap.ker (div_check recX xFive) := by
  refine keyed _ _ _ _ ?_ ?_ ?_ ?_
  · have hp : Subsingleton ↥(TT recX xFour) := by rw [t_classX]; infer_instance
    exact fun _ _ _=> Subsingleton.elim ..
  · rw [w_classX]; apply finite_line
  · rw [v_classX]; apply finite_line
  simp only [x_ranks]
end YM.GaugeFieldConstruction.U1
