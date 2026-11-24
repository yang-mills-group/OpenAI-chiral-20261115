import GaugeFieldConstruction.FinStarMars
import Mathlib.LinearAlgebra.Multilinear.Curry
/-!
 # factoring reference bill. head evaluation and derivative trails
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C)(Y:AreaQc S)
local notation "T"=> BellTableMars p Y
local notation "M"=> TerraMars p Y
namespace FirstPackMars
-- labels cast head
abbrev RaiseCapMars (a:ℕ)(d:NSF.Caps n):NSF.Caps (n+1):=Fin.cons a d
def AffixMars {a:ℕ}{d:NSF.Caps n}(i:LabelMars a)(s:LabelsMars d): LabelsMars (RaiseCapMars a d):=Fin.cons (α:=fun i=> LabelMars (RaiseCapMars a d i)) i s
abbrev PostMars (a:ℕ)(v:FlyerMars a): ΡeaderMars.Token:=⟨a,v⟩
abbrev WriteMars (d:NSF.Caps n)(v:ChartVuMars d):Fin n→ ΡeaderMars.Token:= fun i=>PostMars (d i) (v i)
abbrev ArrangeT MarsN (w:Fin MarsN→ ΡeaderMars.Token): NSF.Caps MarsN := fun i=>(w i).1
lemma TailQtyMars (d:NSF.Caps n)(w: ChartVuMars d) (a:ℕ)(A: FlyerMars a)(x:Points (n+1)): (T).read x (Fin.cons (PostMars a A) (WriteMars d w))=∑ ρ: LabelsMars d, ChartTaxMars w ρ * (T).read x (Fin.cons (PostMars a A) (TiesMars d ρ)):=by
 -- have H : MultilinearMap ℂ (fun i=>FlyerMars (d i)) ℂ := (((T).value (RaiseCapMars a d) x).curryLeft A) -- opaque have bad let
 let Z : MultilinearMap ℂ (fun i=>FlyerMars (d i)) ℂ := ((T).value (RaiseCapMars a d) x).curryLeft A
 have he(v:ChartVuMars d): (T).read x (Fin.cons (PostMars a A) (WriteMars d v))=Z v:= NSF.Table.front_eq _ _ _ _ -- defeq?
 rw[he,QtyApplyMars Z w]; apply sum_congr rfl; exact fun i _=> congrArg (ChartTaxMars w i*·) ((he (HitsMars i)).symm)
lemma FullTailQtyMars (w:Fin n→ΡeaderMars.Token)(W:ΡeaderMars.Token)(x:Points (n+1)): (T).read x (Fin.cons W w)=∑ ρ:LabelsMars (ArrangeT n w), ChartTaxMars (d:=ArrangeT n w) (fun i=>(w i).2) ρ * (T).read x (Fin.cons W (TiesMars _ ρ)):= TailQtyMars p Y (ArrangeT n w) (fun i=>(w i).2) W.1 W.2 x
lemma FullQtyMars (w:Fin n→ΡeaderMars.Token)(x:Points n): (T).read x w=∑ ρ: LabelsMars (ArrangeT n w),ChartTaxMars (d:=ArrangeT n w) (fun i=>(w i).2) ρ * (T).read x (TiesMars _ ρ):=QtyApplyMars (d:=ArrangeT n w) ((T).value _ x) (fun i=>(w i).2)
def CloverHMars (x:GuideMars n) : GuideMars (n+1):= (x.1.succ,x.2)
lemma Mask0Mars (a:ℕ){d:NSF.Caps n}(i)(s:LabelsMars d): maskMars (d:=RaiseCapMars a d) (AffixMars i s) 0=(IndexMars a).symm i:=rfl
lemma MaskSMars (a:ℕ){d:NSF.Caps n}(i)(s:LabelsMars d)(j:Fin n): maskMars (d:=RaiseCapMars a d) (AffixMars i s) j.succ=maskMars s j:=rfl
lemma CoreCutMars (a:ℕ){d:NSF.Caps n}(i)(s:LabelsMars d): τCoreMars (d:=RaiseCapMars a d) (AffixMars i s)=Fin.cons (MCoreMars (ChaseMars _ i).1) (τCoreMars s):=by ext1 j; refine Fin.cases rfl (fun i=>rfl) j
lemma LinesHMars (a:ℕ){d:NSF.Caps n}(i)(s:LabelsMars d): τGuideMars (d:=RaiseCapMars a d) (AffixMars i s)=railMars 0 (ChaseMars _ i).2 ++ ((τGuideMars s).map CloverHMars):=by
 unfold τGuideMars LineMars; rw[List.ofFn_succ,List.flatten_cons,List.map_flatten,List.map_ofFn]; apply congrArg₂ (· ++ ·) rfl; congr! 2; unfold railMars Function.comp; ext1 j; dsimp only; rw[List.map_ofFn]; rfl -- tune
lemma TiesCutMars (a:ℕ){d:NSF.Caps n}(i)(s:LabelsMars d): TiesMars (RaiseCapMars a d) (AffixMars i s)= Fin.cons (coneMaskMars a i) (TiesMars d s):=by ext1 j; refine Fin.cases rfl (fun i=>rfl) j
def unfoldTrailsMars {d:ℕ}(i:TrailsMars d):List CompassMars:=List.ofFn i.2
abbrev TearMarksMars (w:LabelsMars (n:=n) (fun _=>m)):=τGuideMars w
-- natural plane action
lemma CorePlaneMars (u:GuideMars n): guideDirMars (CloverHMars u)= Points.cons 0 (guideDirMars u):=by
 rcases u with ⟨i,j,x|x⟩ --:=u -- tune
 all_goals
    apply PiLp.ext; intro v; refine Fin.cases ?_ (fun t=>?_) v <;> simp [Points.cons,guideDirMars,CloverHMars,direction,PiLp.single_apply,Pi.single_apply]
noncomputable abbrev BillHeadMoon {d:NSF.Caps n}(w:LabelsMars d) (l:List CompassMars)(A:ΧiMars)(x:Points (n+1)):=ΓPriceMars (TerraMars p Y (Fin.cons A (τCoreMars w))) ((l.map (fun i=>(0,i))) ++ ((τGuideMars w).map CloverHMars)) x
lemma ArcBillMoon (d:NSF.Caps n)(w:LabelsMars d) (a:ℕ)(i:LabelMars a)(x:Points (n+1)): (T).read x (Fin.cons (coneMaskMars a i) (TiesMars d w)) = BillHeadMoon p Y w (unfoldTrailsMars (ChaseMars _ i).2) (MCoreMars (ChaseMars _ i).1) x :=by rw[← TiesCutMars,TiesPriceMars,ChartPriceMars,CoreCutMars,LinesHMars]; unfold BillHeadMoon unfoldTrailsMars; rw[List.map_ofFn]; rfl
noncomputable def BrakeMars : Points (n+1) →L[ℝ] Points n:= LinearMap.toContinuousLinearMap { toFun:= YM.Points.tail,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
lemma Brake0Mars (w:GuideMars n): BrakeMars (guideDirMars (CloverHMars w))=guideDirMars w:=by rw [CorePlaneMars]; ext1 i; rfl
lemma BrakeSpinMars (l:List (GuideMars n)) : (((l.map CloverHMars).map guideDirMars).map BrakeMars)=l.map guideDirMars:=by
 induction l with
 | nil=>rfl
 | cons i s hs=>simp only[List.map_cons,Brake0Mars,hs]
variable {p Y} (H:FirstPackMars p Y)
include H
lemma TorqueMars (a:ℕ)(d:NSF.Caps n)(w:LabelsMars d)(x:Points (n+1))(h:x∈conf (n+1)): (T).read x (Fin.cons (ΡeaderMars.one a) (TiesMars d w))=(T).read (YM.Points.tail x) (TiesMars d w):=by
 rw [show ΡeaderMars.one a=coneMaskMars a (arcBlankMars a) from rfl, ArcBillMoon p Y, TiesPriceMars p Y]; rw [show ChaseMars a (arcBlankMars a)= (_,_) from (IndexMars a).symm_apply_apply _]
 let L:=(τGuideMars w).map CloverHMars; let F:=τCoreMars w
 change PoolDMars (L.map guideDirMars) (TerraMars p Y (Fin.cons (Empire.one four) F)) x=_
 have he := MirrorPoolMars (TerraMars p Y (Fin.cons (Empire.one four) F)) (TerraMars p Y F) BrakeMars BrakeMars (TerraSm p Y F) (fun x e=> NSF.Points.tail_in e) (fun x e=> H.coin F x e) (fun x=>BrakeMars.hasFDerivAt) (L.map guideDirMars) x h
 unfold L at he; rw [BrakeSpinMars] at he; exact he
lemma BellCommonMars : (BellTableMars p Y).Basic where
    __:=H.SymHallMars
    trivial w x:=by
       rw [FullQtyMars]; let ρ: LabelsMars (ArrangeT 0 w):= fun i=> Fin.elim0 i
       rw[Finset.sum_eq_single ρ]
       · rw [TiesPriceMars]; unfold ChartTaxMars; rw [prod_of_isEmpty]; rw [one_mul]; exact H.clean _ _
       · intro i hi hr; exact (hr (Subsingleton.elim ..)).elim
       exact fun h=>(h (Finset.mem_univ _)).elim
    unital h d v:=by rw[FullTailQtyMars, FullQtyMars _ _ v]; apply sum_congr rfl; intro i _; rw [TorqueMars H _ _ _ _ h]
#check MultilinearMap.curryLeft
#print axioms BellCommonMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
