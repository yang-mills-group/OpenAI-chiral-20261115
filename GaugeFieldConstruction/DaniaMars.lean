import GaugeFieldConstruction.PewMars
import GaugeFieldConstruction.StyriaRel.YM.Euclid.Pairing
/-!
 # complete formal derivative rows. Keep c and monomial prices explicit
# Extending RP values to tie configurations
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
-- directed reference masks paired without casts along append in downstream kernels
open NSF.Table.Pairing FirstPackMars
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C)(Y:AreaQc S)
local notation "T"=> BellTableMars p Y
abbrev LedgerMars {d:NSF.Caps n}(w:LabelsMars d):= (τGuideMars w).map guideDirMars
abbrev LeftArmMars (d:NSF.Caps (n+m))(w:LabelsMars d): LabelsMars (d∘ Fin.castAdd m):= fun i=> w (Fin.castAdd m i)
abbrev RightArmMars (d:NSF.Caps (n+m))(w:LabelsMars d):LabelsMars (d∘Fin.natAdd n):= fun i=>w (Fin.natAdd n i)
section cut
variable (d:NSF.Caps (n+m))
local notation "i_α"=> Fin.castAdd m (n:=n)
local notation "j_α"=> (Fin.natAdd n: Fin m→Fin (n+m))
abbrev SpanLMars (m n)(d:NSF.Caps (n+m)):=LabelsMars (d ∘ Fin.castAdd m)
abbrev SpanRMars (m n)(d:NSF.Caps (n+m)):=LabelsMars (d ∘ Fin.natAdd n)
def SliceTieMars : LabelsMars d ≃ (SpanLMars m n d × SpanRMars m n d) where
 toFun v := (LeftArmMars d v, RightArmMars d v)
 invFun V:= Fin.addCases (motive:=fun i=>LabelMars (d i)) V.1 V.2
 left_inv v:=by
    ext1 j; change Fin.addCases (motive:=fun i=>LabelMars (d i)) (LeftArmMars d v) (RightArmMars d v) j= _; refine Fin.addCases (fun k=>?_) (fun k=>?_) j <;> simp only [Fin.addCases_left, Fin.addCases_right]; all_goals rfl -- tune args
 right_inv v:=by
    apply Prod.ext
    · ext1 i; change Fin.addCases (motive:=fun i=>LabelMars (d i)) v.1 v.2 (Fin.castAdd m i)=_; rw [Fin.addCases_left]
    ext1 i; change Fin.addCases (motive:=fun i=>LabelMars (d i)) v.1 v.2 (Fin.natAdd n i)=_; rw [Fin.addCases_right]
lemma AppendixLMars (A:LabelsMars d) : Fin.append (TiesMars (d∘i_α) (LeftArmMars d A)) (TiesMars (d∘j_α) (RightArmMars d A))= TiesMars d A:=by ext1 j; refine Fin.addCases (fun i=>?_) (fun i=>?_) j <;> simp only [Fin.append_left,Fin.append_right] <;> rfl
lemma AppendixUMars (A:LabelsMars d): Fin.append (τCoreMars (LeftArmMars d A)) (τCoreMars (RightArmMars d A))=τCoreMars A:=by ext1 j; refine Fin.addCases (fun i=>?_) (fun i=>?_) j <;> simp only [Fin.append_left,Fin.append_right] <;> rfl
lemma CutsΦMars (w: ChartVuMars d)(A:LabelsMars d): ChartTaxMars w A=ChartTaxMars (d:=d∘i_α) (fun i=>w (i_α i)) (LeftArmMars d A)* ChartTaxMars (d:=d∘j_α) (fun i=>w (j_α i)) (RightArmMars d A):=Fin.prod_univ_add ..
end cut
abbrev FeedTaxMars (A:Fin n→ΡeaderMars.Token)(I:LabelsMars (ArrangeT n A)):= ChartTaxMars (d:=ArrangeT n A) (fun i=>(A i).2) I
-- Expand without needing bundled permutation arguments. And single axis left charge p.Spin.Mirror
lemma TurnCensusMars (A:Fin n→ΡeaderMars.Token) (B: Fin m→ΡeaderMars.Token)(x:Points (n+m)): (T).read x (Fin.append A B)= ∑ z: LabelsMars (ArrangeT n A) × LabelsMars (ArrangeT m B), FeedTaxMars A z.1 * FeedTaxMars B z.2 *(T).read x (Fin.append (TiesMars _ z.1) (TiesMars _ z.2)) :=by
 suffices h:∀ (W:Fin (n+m)→ΡeaderMars.Token)(A:Fin n→ΡeaderMars.Token)(B:Fin m→ΡeaderMars.Token), W ∘ Fin.castAdd m =A → W ∘ Fin.natAdd n=B → (T).read x W=∑ z:LabelsMars (ArrangeT n A) × LabelsMars (ArrangeT m B), FeedTaxMars A z.1 * FeedTaxMars B z.2 * (T).read x (Fin.append (TiesMars _ z.1) (TiesMars _ z.2)) by
    exact h (Fin.append A B) _ _ (funext (fun i=> Fin.append_left ..)) (funext fun i=> Fin.append_right ..)
 rintro W A B rfl rfl; let d:=ArrangeT (n+m) W; let V(i:Fin (n+m)):=(W i).2
 rw[FullQtyMars]; exact Fintype.sum_equiv (SliceTieMars d) _ _ (fun i=> congrArg₂ _ (CutsΦMars d V i) (congrArg ((T).read x) (AppendixLMars d i).symm)) -- tune
section
variable (j:Axis)
local notation "s_α"=> Signed.mirror j
abbrev EmberRevMars (A:Fin n→ΡeaderMars.Token)(j:Axis):=ΡeaderMars.reflectedToken j ∘ A
variable (A:Fin n→ΡeaderMars.Token)(V:Fin m→ΡeaderMars.Token)
lemma FeetMirrorMars (w:LabelsMars (ArrangeT n A)) : FeedTaxMars (EmberRevMars A j) (wispsMars (s_α) w)= star (FeedTaxMars A w):=by
 unfold FeedTaxMars ChartTaxMars; rw [star_prod]; apply prod_congr rfl; intro k _; change star ((A k).2 (arcActsMars _ (Signed.mirror j)⁻¹ (arcActsMars _ (Signed.mirror j) (w k))))= star _; rw[ArcPairMars]
lemma RibsMirrorMars (d:NSF.Caps n)(w:LabelsMars d): TiesMars d (wispsMars (s_α) w)= ΡeaderMars.reflectedToken j ∘ TiesMars d w:=by
 ext1 k; unfold TiesMars coneMaskMars; refine congrArg (Sigma.mk (d k)) ?_; have he: star (coneOneMars (d k) (w k))= coneOneMars (d k) (w k):=by ext1 i; by_cases v:i=w k <;> simp[v,coneOneMars] -- lhs? cast motive.
 change coneOneMars _ _=writeArcMars (d k) (Signed.mirror j) (star (coneOneMars (d k) (w k))); rw[he]; exact (writeArcOneMars ..).symm
local notation "νσ"=> ArrangeT n A
local notation "ντ"=> ArrangeT m V
lemma ebanPrMars (x:Points (n+m)):(T).read x (tied A V j)=∑ i:LabelsMars (νσ),∑ k:LabelsMars (ντ), star (FeedTaxMars A i) * FeedTaxMars V k * (T).read x (tied (TiesMars _ i) (TiesMars _ k) j):=by
 let h:= EmberRevMars A j
 let E: LabelsMars (νσ)≃ LabelsMars (ArrangeT n h):= Equiv.piCongrRight fun i=> SunArcMars _ (Signed.mirror j)
 refine (TurnCensusMars p Y h V x).trans ?_; rw [Fintype.sum_prod_type]; symm; refine Fintype.sum_equiv E _ _ (fun i=>sum_congr rfl (fun k _=>?_))
 refine congrArg₂ HMul.hMul (congrArg₂ HMul.hMul (FeetMirrorMars j A i).symm rfl) (congrArg ((T).read x) (congrArg (fun h=> Fin.append h (TiesMars _ k)) (RibsMirrorMars j _ i).symm))
end
#print axioms ebanPrMars
end YM.GaugeFieldConstruction.Ember.Volumetric
