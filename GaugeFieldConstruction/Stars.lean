import GaugeFieldConstruction.Identity97
/-!
# Complex vs c-real generators: checks on the free supply
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.GaugeFieldConstruction.Calibration
open Function Cauchy Calibration Floor Conj Row U1 Raw Module Submodule
open scoped BigOperators
abbrev Conserved := LinearMap.ker divergence
-- provide instances, compatible via reducible defeq
local instance iA : AddCommGroup ↥SymT := @Submodule.addCommGroup ℂ (Raw.Sym → UV four) _ _ _ _
local instance iB : AddCommGroup ↥OneW := @Submodule.addCommGroup ℂ (Axis → UV five) _ _ _ _
local instance iC : AddCommGroup ↥Conserved := @Submodule.addCommGroup ℂ (SymT) _ _ _ _

abbrev Bundle := ℂ × (Bool→ℂ)
-- linear bundle of packages
private def packets : Bundle →ₗ[ℂ] Trio four symAct where
  toFun p:= (p.1 • bead,fun i=>p.2 i • strand,0)
  map_add' x y:=by
    apply Prod.ext
    · apply Subtype.ext; change (x.1+y.1) • bead.val=x.1 • bead.val+y.1 • bead.val; exact add_smul _ _ bead.val
    refine Prod.ext (funext fun i=> Subtype.ext ?_) ?_
    · change (x.2 i+y.2 i) • strand.val=x.2 i • strand.val+y.2 i • strand.val; exact add_smul _ _ strand.val
    exact (add_zero _).symm
  map_smul' x y:=by
    apply Prod.ext
    · apply Subtype.ext; change (x*y.1) • bead.val=x • y.1 • bead.val; rw [smul_smul]
    refine Prod.ext (funext fun i=> Subtype.ext ?_) ?_
    · change (x*y.2 i) • strand.val=x • y.2 i • strand.val; rw [smul_smul]
    exact (smul_zero _).symm

def totalIx : Bundle →ₗ[ℂ] Conserved := ((package four symAct).symm.toLinearMap.comp packets).codRestrict Conserved
  (fun i=> (pure_supply (stress i.1 i.2)).mpr ⟨_,_,rfl⟩)

def supply : Bundle ≃ₗ[ℂ] Conserved := LinearEquiv.ofBijective totalIx
  ⟨fun a b h=>by obtain ⟨x,y⟩:= solitary (show stress a.1 a.2=stress b.1 b.2 from congr_arg Subtype.val h); exact Prod.ext x y,
    fun p => by
      obtain ⟨c,a,h⟩:=(pure_supply p.val).mp p.property; exact ⟨(c,a),Subtype.ext h.symm⟩⟩

theorem supply_dimension : finrank ℂ Conserved=3 := by
  rw [← supply.finrank_eq]; unfold Bundle
  rw [Module.finrank_prod,Module.finrank_self, Module.finrank_pi]; decide

theorem div_dimension : finrank ℂ (LinearMap.range divergence)=4 := by
  haveI : Module.Finite ℂ SymT := finiteInvariant ..
  have he := @LinearMap.finrank_range_add_finrank_ker ℂ SymT _ _ _ OneW _ _ _ divergence
  rw [show finrank ℂ (LinearMap.ker divergence)=3 from supply_dimension,sym_count] at he; omega
-- c compatibility
lemma bead_real (x : Raw.Sym) : cG (bead.val x) = bead.val x := by
  have ht (i j: Axis) : cG (Bose (F i j) (F i j))=Bose (F i j) (F i j) := by
    simp only [Bose,map_add,cG,portal]; by_cases he:i=j
    · rw [he,Gauge97.zero_angle]; simp
    rcases lt_or_gt_of_ne he with h|h
    · rw [show F i j=arc (Wed.mk _ _ h) from rfl, realistic]
    rw [Gauge97.turnover i j,show F j i=arc (Wed.mk _ _ h) from rfl,map_neg,realistic]
  have hu (i j:Axis) : tr GIndex (F i j)=F i j := by
    rcases lt_trichotomy i j with h|h|h
    · exact realistic (Wed.mk _ _ h)
    · rw [h,Gauge97.zero_angle,map_zero]
    rw [Gauge97.turnover i j,show F j i=arc (Wed.mk _ _ h) from rfl,map_neg,realistic]
  have he i j : cG (Gauge97.bill i j)=Gauge97.bill i j := by
    unfold Gauge97.bill; rw [map_sum]; exact Finset.sum_congr rfl fun k _=>by simp [Gauge97.bill.P_pair,Bose,cG,portal,hu]
  change cG ((1/4:ℂ) • Gauge97.Root x)=(1/4:ℂ) • _
  simp only [Gauge97.Root,Gauge97.recorded,LinearMap.map_smulₛₗ,map_sub]; split_ifs <;> simp [map_sum,he,bar,map_ofNat]
lemma strand_real (x : Raw.Sym) : cF (strand.val x)=strand.val x := by
  change cF ((-1/64:ℂ) • Spin97.Root x)=(-1/64:ℂ) • _
  rw [LinearMap.map_smulₛₗ, show bar (-1/64) = -1/64 by norm_num [bar,map_ofNat]]
  simp [Spin97.Root,Spin97.element,cL,f3_tr]
lemma shades (a : Bundle) (i) : shade four ((totalIx a).val.val i)= (totalIx (star a.1,fun k=>star (a.2 k))).val.val i := by
  apply Prod.ext; exact map_zero bar
  apply Prod.ext
  · apply Subtype.ext
    change cG (a.1 • bead.val i) = star a.1 • bead.val i; rw [LinearMap.map_smulₛₗ,bead_real]; rfl
  refine Prod.ext (funext fun x=>?_) (funext fun x=>?_)
  · -- bundle reads
    apply Subtype.ext
    change cF (((totalIx a).val.val i).2.2.1 x).val = _
    by_cases h:x.2.1=x.2.2
    · have he (b : Bundle) : (((totalIx b).val.val i).2.2.1 x).val=b.2 x.1 • strand.val i := by
        change ((((backward four symAct (packets b)).val i).2.2.1 x):UF four).val = _ -- edit
        simp only [backward, Flavor.bundle_, h,↓reduceIte]; rfl
      rw [he,he,LinearMap.map_smulₛₗ,strand_real]; rfl
    have he (b : Bundle) : (((totalIx b).val.val i).2.2.1 x).val=0 := by
      change (((backward four symAct (packets b)).val i).2.2.1 x).val=0
      simp only [backward,Flavor.bundle_, if_neg h]; rfl
    rw [he, he,map_zero]
  have h : Subsingleton (UX four) := by change Subsingleton ↥(⊥:Submodule ℂ _); infer_instance
  apply Subsingleton.elim
end YM.GaugeFieldConstruction.Calibration
