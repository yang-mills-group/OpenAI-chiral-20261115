import GaugeFieldConstruction.StressTest
/-!
# The free conserved multiplets with the (97) scalings

Uniqueness as shell data, no receipts approximating these yet.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6000
noncomputable section
namespace YM.GaugeFieldConstruction.Calibration
open U1 Function Cauchy Row Record Vouchers Submodule Raw Module Floor
open scoped BigOperators

private def passed {α β} (R : Record α β) (U : Submodule ℂ (J α)) := R.divP ∘ₗ (TT R U).subtype

private lemma payment {α β n k} (R : Record α β) (U : Submodule ℂ (J α))
    (hU : Module.Finite ℂ (TT R U))
    (h : finrank ℂ (TT R U)=n) (u : finrank ℂ (map R.divP (TT R U))=k) :
    finrank ℂ (LinearMap.ker (passed R U))=n-k := by
  have he:= @LinearMap.finrank_range_add_finrank_ker ℂ (TT R U) _ _ _ (Axis → J α) _ _ _ (passed R U)
  have ht : LinearMap.range (passed R U)=map R.divP (TT R U) := by rw [passed,LinearMap.range_comp,range_subtype]
  rw [ht,h,u] at he; omega

private lemma spins {A : Type*} [AddCommGroup A] [Module ℂ A] {U : Submodule ℂ A} [Module.Finite ℂ U]
    (i : A) (p : i∈U) (h : i≠0) (k : finrank ℂ U=1) (t : A) (w : t∈U) :∃ c:ℂ,t=c • i := by
  have q := eq_of_le_of_finrank_eq ((span_singleton_le_iff_mem _ _).mpr p) (by rw [finrank_span_singleton h,k])
  rw [← q] at w; obtain ⟨c,hc⟩ := mem_span_singleton.mp w
  exact ⟨c,hc.symm⟩

def bead : TT recG gFour:=⟨(1/4:ℂ) • Gauge97.Root, smul_mem _ _ Gauge97.root_ok⟩
def strand : TT ph fFour:=⟨(-1/64:ℂ) • Spin97.Root, smul_mem _ _ Spin97.root_ok⟩
private lemma paid_B : recG.divP bead.val=0 := by simp [bead, Gauge97.div_true]
private lemma paid_T : ph.divP strand.val=0 := by simp [strand, Spin97.div_true]
private lemma bn : bead ≠ 0 := by
  intro H; have ht: (1/4:ℂ) • Gauge97.Root=0:= congr_arg Subtype.val H
  exact Gauge97.awake ((smul_eq_zero.mp ht).resolve_left (by norm_num))
private lemma tn : strand≠0 := by
  intro H; have ht: (-1/64:ℂ) • Spin97.Root=0:= congr_arg Subtype.val H
  exact Spin97.awake ((smul_eq_zero.mp ht).resolve_left (by norm_num))

private lemma strand_B (Y : TT recG gFour) (h : recG.divP Y.val=0):∃ c:ℂ,Y=c • bead := by
  haveI Q : Module.Finite ℂ (TT recG gFour) := by rw [t_classG]; exact finite_line _
  let S:=LinearMap.ker (passed recG gFour)
  have hp : finrank ℂ S=1 := payment recG gFour Q g_ranks.1 g_ranks.2.1
  letI : AddCommGroup ↥(TT recG gFour) := @Submodule.addCommGroup ℂ (Raw.Sym → J Row.g) _ _ _ _
  haveI : Module.Finite ℂ S:= Module.finite_of_finrank_pos (R:=ℂ) (by rw [hp]; norm_num)
  exact @spins ↥(TT recG gFour) _ _ S _ bead paid_B bn hp Y h
private lemma strand_T (Y : TT ph fFour) (h : ph.divP Y.val=0):∃ c:ℂ,Y=c • strand := by
  haveI Q : Module.Finite ℂ (TT ph fFour) := by rw [t_classF]; exact finite_line _
  let S:=LinearMap.ker (passed ph fFour)
  have hp : finrank ℂ S=1 := payment ph fFour Q f_ranks.1 f_ranks.2.1
  letI : AddCommGroup ↥(TT ph fFour) := @Submodule.addCommGroup ℂ (Raw.Sym → J Row.f) _ _ _ _
  haveI : Module.Finite ℂ S := Module.finite_of_finrank_pos (R:=ℂ) (by rw [hp]; norm_num)
  exact @spins ↥(TT ph fFour) _ _ S _ strand paid_T tn hp Y h

/-- Unit pigment: unit of local free cost will require the asserted Q2 actions in U3. -/
def Trine:= ℂ × (Bool→ℂ) -- coordinates; abbrev

def stress (a : ℂ) (u : Bool → ℂ): SymT := (package four symAct).symm (a • bead,fun i=>u i • strand,0)

lemma wireG (v) : (package five Raw.v (divergence v)).1.val = recG.divP (liftG v).val := by
  have ht: (reportG (previous v)).val=(arr recG gFour gFive dG (liftG v)).val:= congr_arg Subtype.val (levelG v)
  exact congr_arg Prod.fst ht
lemma wireF (v b) : ((package five Raw.v (divergence v)).2.1 b).val=ph.divP (liftF v b).val := by
  have ht:= congr_arg Subtype.val (levelF v b); exact congr_arg Prod.fst ht
lemma wireX (v b) : ((package five Raw.v (divergence v)).2.2 b).val=recX.divP (liftX v b).val := by
  have ht:=congr_arg Subtype.val (levelX v b); exact congr_arg Prod.fst ht
lemma lift1 (a b): liftG (stress a b)=a • bead := congr_arg Prod.fst ((package four symAct).apply_symm_apply (a • bead,fun i=> b i • strand,0)) -- tweak
lemma lift2 (a b c): liftF (stress a b) c=b c • strand := by
  unfold liftF stress; rw [LinearEquiv.apply_symm_apply]
lemma lift3 (t : SymT) (c) : liftX t c=0 := by
  have h : Subsingleton ↥(TT recX xFour) := by rw [t_classX]; infer_instance
  exact Subsingleton.elim ..

theorem pure_supply (v : SymT) : divergence v=0 ↔ ∃ a m, v=stress a m := by
  constructor
  · intro h
    have y (d) (A : Labels Raw.Sym):= (package d A).map_zero
    obtain ⟨c,p⟩:=strand_B (liftG v) (by rw [← wireG,h,map_zero]; rfl)
    choose a f using fun i=> strand_T (liftF v i) (by rw [← wireF,h,map_zero]; rfl)
    refine ⟨c,a,?_⟩; apply (package four symAct).injective
    refine Prod.ext (show liftG _=liftG _ from p.trans (lift1 c a).symm) (Prod.ext ?_ ?_)
    exact funext fun i=> (f i).trans (lift2 c a i).symm
    exact funext fun i=> Eq.trans (lift3 v i) (lift3 (stress c a) i).symm
  rintro ⟨c,a,rfl⟩; apply (package five Raw.v).injective; rw [map_zero]
  apply Prod.ext
  · apply Subtype.ext; rw [wireG,lift1]; change recG.divP (c • bead.val)=0; rw [map_smul, paid_B,smul_zero]
  refine Prod.ext (funext fun j=> Subtype.ext ?_) (funext fun j=> Subtype.ext ?_)
  · rw [wireF,lift2]; change ph.divP (a j • strand.val)=0; rw [map_smul,paid_T,smul_zero]
  rw [wireX,lift3]; change recX.divP 0=0; rw [map_zero]
lemma solitary {a b p q} (h : stress a p=stress b q) : a=b ∧ p=q := by
  have e := congr_arg liftG h; rw [lift1,lift1] at e
  refine ⟨?_,funext fun i=>?_⟩
  · have he : bead.val≠0 := fun h => bn (Subtype.ext h); exact smul_left_injective ℂ he (congr_arg Subtype.val e)
  have ht := congr_arg (liftF · i) h; rw [lift2,lift2] at ht
  have he : strand.val≠0 := fun h => tn (Subtype.ext h)
  exact smul_left_injective ℂ he (congr_arg Subtype.val ht)
end YM.GaugeFieldConstruction.Calibration
