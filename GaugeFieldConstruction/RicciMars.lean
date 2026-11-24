import GaugeFieldConstruction.ValdezMars
import Mathlib.LinearAlgebra.Multilinear.Pi
/-!
 # reference row sums and Table growth
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C) (Y:AreaQc S)
-- convert direction list
abbrev GuideMars(n:ℕ):= Fin n× CompassMars
def guideDirMars (x:GuideMars n): Points n:= if x.2.2 then -(direction x.1 x.2.1) else direction x.1 x.2.1
abbrev BDirMars (x:CompassMars): E4:= if x.2 then - YM.basis x.1 else YM.basis x.1
def railMars {d:ℕ} (i:Fin n)(x:TrailsMars d):List (GuideMars n) :=List.ofFn fun (j: Fin x.1.val)=> ((i,x.2 j) : GuideMars n)
abbrev LineMars (τ:Fin n→ List (GuideMars n)):= (List.ofFn τ).flatten
abbrev LabelsMars (d:NSF.Caps n):=∀ i, LabelMars (d i)
abbrev maskMars {d:NSF.Caps n} (ρ:LabelsMars d) (i:Fin n): ΦCodexMars (d i):= (IndexMars _).symm (ρ i)
abbrev τCoreMars {d:NSF.Caps n}(ρ:LabelsMars d):Fin n→ΧiMars:= fun i=> MCoreMars (maskMars ρ i).1
abbrev τGuideMars {d:NSF.Caps n}(ρ:LabelsMars d):=LineMars fun i=>railMars i (maskMars ρ i).2
def ΓPriceMars (F: Points n→ℂ)(l:List (GuideMars n)) (x:Points n):= PoolDMars (l.map guideDirMars) F x
abbrev ChartPriceMars {d:NSF.Caps n} (ρ:LabelsMars d) := ΓPriceMars (TerraMars p Y (τCoreMars ρ)) (τGuideMars ρ)
-- row table
abbrev BuildPriceMars (d:NSF.Caps n) (x: Points n): MultilinearMap ℂ (fun i=> FlyerMars (d i)) (LabelsMars d→ ℂ):= MultilinearMap.piFamily fun ρ : LabelsMars d => MultilinearMap.mkPiRing ℂ (Fin n) (ChartPriceMars p Y ρ x)
noncomputable def BellTableMars : NSF.Table ΡeaderMars where
    value {n} d x:= (∑ ρ: LabelsMars d,(LinearMap.proj (R:=ℂ) (φ:=fun _ : LabelsMars d=> ℂ) ρ)).compMultilinearMap (BuildPriceMars p Y d x)
local notation "T"=> BellTableMars p Y
abbrev coneOneMars (d:ℕ)(i:LabelMars d): FlyerMars d:= Pi.single i 1
abbrev coneMaskMars (d:ℕ)(i:LabelMars d): ΡeaderMars.Token:= Sigma.mk d (coneOneMars d i)
abbrev HitsMars {d:NSF.Caps n}(ρ:LabelsMars d) (i:Fin n):FlyerMars (d i):= coneOneMars _ (ρ i)
abbrev TiesMars (d:NSF.Caps n) (ρ:LabelsMars d): Fin n→ ΡeaderMars.Token := fun i=> coneMaskMars (d i) (ρ i)
lemma BellPriceMars (d:NSF.Caps n)(ρ:LabelsMars d) (x:Points n) : (T).value d x (HitsMars ρ)=ChartPriceMars p Y ρ x:=by
 change (∑ ρ:LabelsMars d, LinearMap.proj (R:=ℂ) (φ:=fun _=>ℂ) ρ) (BuildPriceMars p Y d x (HitsMars ρ))=_
 rw [LinearMap.sum_apply]; simp only [LinearMap.proj_apply]
 unfold BuildPriceMars HitsMars coneOneMars; rw [MultilinearMap.piFamily_single]; simp
lemma TiesPriceMars (d:NSF.Caps n)(ρ:LabelsMars d) (x:Points n) : (T).read x (TiesMars d ρ)= ChartPriceMars p Y ρ x := BellPriceMars ..
abbrev ChartVuMars (d:NSF.Caps n) : Type:= (i:Fin n)→ FlyerMars (d i)
abbrev ChartTaxMars {d:NSF.Caps n} (v:ChartVuMars d)(ρ:LabelsMars d): ℂ:=∏ i,v i (ρ i)
def ChaseMars (d :ℕ)(i:LabelMars d):=(IndexMars d).symm i
lemma TaxApplyMars (d:NSF.Caps n)(v:ChartVuMars d)(x:Points n): (T).value d x v=∑ ρ:LabelsMars d,ChartTaxMars v ρ*ChartPriceMars p Y ρ x:=by
 change (∑ ρ:LabelsMars d, LinearMap.proj (R:=ℂ) (φ:=fun _=>ℂ) ρ) (BuildPriceMars p Y d x v)=_
 rw[LinearMap.sum_apply]; rfl
lemma QtyApplyMars {d:NSF.Caps n}{E: Type*}[AddCommGroup E][Module ℂ E] (f:MultilinearMap ℂ (fun i=> FlyerMars (d i)) E)(v:ChartVuMars d): f v=∑ ρ:LabelsMars d,ChartTaxMars v ρ • f (HitsMars ρ):=by
 have h : ∀ x:ChartVuMars d,x=(fun i=>∑ j: LabelMars (d i),x i j • (Pi.single j 1: FlyerMars (d i))) :=by
    intro x; ext1 i; have he:∀ j, x i j • coneOneMars _ j=Pi.single j (x i j):=by
        intro j; ext a; by_cases p:a=j <;> simp [coneOneMars,p]
    rw [show (∑ j: LabelMars (d i),x i j • (Pi.single j 1 : FlyerMars (d i)))=(∑ j: LabelMars (d i),Pi.single j (x i j): FlyerMars (d i)) from sum_congr rfl (fun j _=> he j), Finset.univ_sum_single]
 conv_lhs=> rw [h v]
 rw [f.map_sum]; apply Finset.sum_congr rfl; exact fun j _=> f.map_smul_univ ..
-- smooth and capped
lemma ΓSmMars (F: Points n→ℂ)(h: ContDiffOn ℝ ∞ F (conf n))(l:List (GuideMars n)): ContDiffOn ℝ ∞ (ΓPriceMars F l) (conf n):=fun i e=> (poolSmMars _ _ _ ((h i e).contDiffAt ((conf_open _).mem_nhds e))).contDiffWithinAt
lemma BellSmMars : (T).Smooth where
 on_conf d v:=by simp_rw [TaxApplyMars]; exact ContDiffOn.sum (fun ρ _=>contDiffOn_const.mul (ΓSmMars _ (TerraSm p Y _) _))
-- Caps lemmas
lemma CapMergeMars {I:Type*}{W:Type*}[NormedAddCommGroup W](s:Finset I)(F:I→Points n→ W)(G:Points n→ W)(h:∀ i∈s,CaporMars (F i))(e: EqOn G (fun x=> ∑ i∈s,F i x) (conf n)):CaporMars G:=by
 obtain ⟨A,m,ha,H⟩:=aggDMars s F h; refine ⟨A,m,ha,fun r hr u x hx=>?_⟩; rw [e (spaced_conf hr hx)]; exact (norm_sum_le ..).trans (H r hr u x hx)
lemma capNormMars {W Z:Type*}[NormedAddCommGroup W][NormedAddCommGroup Z](G:Points n→W)(F:Points n→ Z)(h: CaporMars F)(C:ℝ)(p:0≤C)(e:∀ x∈conf n,‖G x‖≤ C*‖F x‖): CaporMars G:=by
 obtain ⟨A,m,ht,H⟩:=h; refine ⟨C*A,m,mul_nonneg p ht,fun r hx u x v=> (e x (spaced_conf hx v)).trans ?_⟩; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (H r hx u x v) p
lemma poolConvertMars {α β:Type*}[NormedAddCommGroup α][NormedAddCommGroup β][NormedSpace ℝ α][NormedSpace ℝ β](a:β →L[ℝ]β)(F:α→β)(U:Set α)(u:IsOpen U)(h:ContDiffOn ℝ ∞ F U)(l:List α)(x:α)(hx:x∈U): PoolDMars l (a ∘ F) x=a (PoolDMars l F x):=by
 induction l generalizing x with
 | nil=>rfl
 | cons i l hl=>
    have he:PoolDMars l (a ∘ F)=ᶠ[𝓝 x] a ∘ (PoolDMars l F):=(u.eventually_mem hx).mono hl -- ok
    rw [poolHeadMars,GermD i he,D,fderiv_comp x a.differentiableAt ((poolSmMars _ _ _ ((h _ hx).contDiffAt (u.mem_nhds hx))).differentiableAt (by simp)),a.fderiv]; rfl
lemma poolPayMoonMars (F:Points n→ℂ)(h: ContDiffOn ℝ ∞ F (conf n))(l : List (GuideMars n)):∃ a:ℝ,EqOn (ΓPriceMars F l) (fun x=> a • PoolDMars (PaceMars (l.map (fun i=>(i.1,i.2.1)))) F x) (conf n):=by
 induction l with
 | nil=> exact ⟨1,fun x _=> by dsimp [ΓPriceMars,PaceMars,PoolDMars]; rw[one_mul] ⟩
 | cons i s hs=>
    obtain ⟨a,e⟩:=hs; let P':= PaceMars (s.map (fun i=>(i.1,i.2.1))); let U:=a • ContinuousLinearMap.id ℝ ℂ; let G:=PoolDMars P' F
    refine ⟨if i.2.2 then -a else a, fun x hx=>?_⟩
    have he : ΓPriceMars F s=ᶠ[𝓝 x] U ∘ G:= e.eventuallyEq_of_mem ((conf_open _).mem_nhds hx) -- tune
    change D (guideDirMars i) (ΓPriceMars F s) x=(if i.2.2 then (-a) else a) • PoolDMars (PaceMars _) F x
    rw [GermD (guideDirMars i) he,D,fderiv_comp x U.differentiableAt ((poolSmMars _ _ _ ((h x hx).contDiffAt ((conf_open _).mem_nhds hx))).differentiableAt (by simp)),U.fderiv]
    unfold guideDirMars; split
    · change U (fderiv ℝ G x (- (direction i.1 i.2.1)))= -a • (fderiv ℝ G x _); rw [map_neg, map_neg, neg_smul]; rfl
    rfl
variable (hCap:∀ (n:ℕ)(F:Fin n→ΧiMars),CaporMars (WallMars Y F))
include hCap
lemma payMoonMars (F:Fin n→ΧiMars)(l v : List (GuideMars n)): CaporMars (fun x=> PoolDMars (v.map guideDirMars) (ΓPriceMars (TerraMars p Y F) l) x):=by
 let f:= TerraMars p Y F
 rw [show (fun x=>PoolDMars (v.map guideDirMars) (ΓPriceMars (TerraMars p Y F) l) x)= ΓPriceMars f (v++l) from by unfold ΓPriceMars; rw[List.map_append,pool_appendMars]]
 obtain ⟨a,e⟩:= poolPayMoonMars f (TerraSm p Y _) (v++l); refine capNormMars _ _ (CeilingCapsMars p Y F hCap _ ((v++l).map (fun i=>(i.1,i.2.1))) rfl) ‖a‖ (norm_nonneg _) (fun x h=>?_)
 rw [e h, norm_smul] -- tune read implicit list
lemma TableLengthMars: (BellTableMars p Y).Capped:=by
 intro n d v j
 let G:= fun x: Points n=> (BellTableMars p Y).value d x v
 suffices t:CaporMars (iteratedFDeriv ℝ j G) by obtain ⟨x,i,f,g⟩:= t; exact ⟨i,x,f,g⟩
 refine frameCapMars _ (fun i=>?_) -- requires list moves
 let l:= List.ofFn (FingerMars ∘ i); let g:=fun (ρ:LabelsMars d) => (fun x:Points n=>ChartTaxMars v ρ * ChartPriceMars p Y ρ x)
 have h (ρ:LabelsMars d):ContDiffOn ℝ ∞ (ChartPriceMars p Y ρ) (conf n):=ΓSmMars _ (TerraSm p Y _) _
 have hx:G=(fun x=>∑ ρ:LabelsMars d,g ρ x):=funext (fun x=>TaxApplyMars ..)
 apply CapMergeMars univ (fun ρ=> PoolDMars l (g ρ)) _ ?_ ?_
 · intro ρ _; let A:= (ChartTaxMars v ρ) • ContinuousLinearMap.id ℝ ℂ
   let k:=List.ofFn (fun j=> ((i j).1,(i j).2,false))
   have ht:k.map guideDirMars=l:=by rw[List.map_ofFn]; rfl -- syntactic let
   refine capNormMars _ _ (payMoonMars p Y hCap (τCoreMars ρ) (τGuideMars ρ) k) ‖ChartTaxMars v ρ‖ (norm_nonneg _) (fun x e=>?_); rw[ht]
   change ‖PoolDMars l (A ∘ ChartPriceMars p Y ρ) x‖≤ _; rw [poolConvertMars A _ _ (conf_open n) (h _) l x e]; exact Eq.le (norm_mul ..)
 intro x hV; change iteratedFDeriv ℝ j G x (FingerMars ∘ i)=_; rw [← pool_payMars _ _ _ (conf_open n) ((BellSmMars _ _).on_conf _ v) _ hV]; change PoolDMars l G x=_; rw[hx]; exact pool_sumMars l univ g _ (conf_open n) (fun ρ _=>contDiffOn_const.mul (h _)) _ hV
#print axioms TableLengthMars
end YM.GaugeFieldConstruction.Ember.Volumetric
