import GaugeFieldConstruction.DaniaMars
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
variable (a:Axis)
-- maps of direction list
abbrev BoreLMars (j:Axis)(m:ℕ)(x:Points n):= closedUp j x (0:Points m)
abbrev BoreRMars (j:Axis)(n:ℕ)(x:Points m):= closedUp j (0:Points n) x
lemma BoreFinLMars (i:Fin n)(m:ℕ)(c:CompassMars): guideDirMars (Fin.castAdd m i,c)= BoreLMars a m (windLMars (Signed.mirror a) (guideDirMars (i,c))):=by
    apply PiLp.ext; intro j; refine Fin.addCases (fun k=>?_) (fun k=>?_) j
    · rw [BoreLMars,enter]
      have he(x:Points n):ride a (windLMars (Signed.mirror a) x k) = x k:=riding a _
      rw [he]; have ht(i j:Fin n): Fin.castAdd m i=Fin.castAdd m j ↔ i=j:=⟨fun h=>Fin.ext (show _=_ from (show i.val=j.val from by have p:=congrArg Fin.val h; exact p)),fun h=>h ▸ rfl⟩
      simp [guideDirMars,direction]; split <;> simp [PiLp.single_apply,ht] -- tune
    rw [BoreLMars,leave]; have he: Fin.natAdd n k≠ Fin.castAdd m i:=ne_of_gt (show i.val<n+k.val from by omega)
    unfold guideDirMars; split<;> simp [direction,he,PiLp.single_apply] -- orientation
lemma BoreFinRMars (i:Fin m)(n:ℕ)(c:CompassMars): guideDirMars (Fin.natAdd n i,c)= BoreRMars a n (guideDirMars (i,c)):=by
    apply PiLp.ext; intro j; refine Fin.addCases (fun k=>?_) (fun k=>?_) j
    · rw [BoreRMars,enter]; have he: Fin.natAdd n i≠ Fin.castAdd m k:=ne_of_gt (show k.val<n+i.val from by omega); unfold guideDirMars; split <;> simp [direction,he, ride, PiLp.single_apply, Ne.symm he] <;> exact (Signed.reflect a).motion.map_zero.symm -- tune
    rw [BoreRMars,leave]; simp [guideDirMars,direction]; split<;> simp [PiLp.single_apply]
variable (d:NSF.Caps (n+m))
lemma tearMars (w:LabelsMars d): LedgerMars w=(LedgerMars (LeftArmMars d w)).map (fun x=>BoreLMars a m (windLMars (Signed.mirror a) x)) ++ (LedgerMars (RightArmMars d w)).map (fun x=>BoreRMars a n x):=by
 unfold LedgerMars; rw [payGuideMars, List.ofFn_add,List.flatten_append,payGuideMars,payGuideMars, List.map_flatten,List.map_flatten,List.map_ofFn,List.map_ofFn]; congr 3
 · funext i; dsimp only [Function.comp_apply]; rw [payRailsMars,payRailsMars,List.map_ofFn]; congr 1; funext k; exact BoreFinLMars .. -- tune
 · funext i; dsimp only [Function.comp_apply]; rw [payRailsMars,payRailsMars,List.map_ofFn]; congr 1; funext k; exact BoreFinRMars ..
variable (i: LabelsMars (d ∘ Fin.castAdd m)) (j:LabelsMars (d ∘ Fin.natAdd n))
local notation "R_ε"=> Signed.mirror a
local notation "R_α"=> windLMars (n:=n) (Signed.mirror a)
lemma turnCoreMars (d:NSF.Caps n)(w:LabelsMars d): τCoreMars (wispsMars (R_ε) w)=TurnupMars a ∘ τCoreMars w:=by rw [WispCoreMars]; ext1 k; change _=spinFrame _ _ _; exact congrArg _ (MFixedMars _).symm
lemma TurnLedgerMars (w:LabelsMars (d∘Fin.castAdd m)): (LedgerMars (wispsMars (R_ε) w)).map (fun x=>BoreLMars a m (R_α x))=(LedgerMars w).map (BoreLMars a m):=by
 unfold LedgerMars; rw[WispSchedMars,List.map_map]; congr 1; ext1 k; change _=_; unfold Function.comp; dsimp only; rw [show (R_α) (windLMars (Signed.mirror a) k)= k from PiLp.ext (fun i=>riding a (k i))] -- parse x
lemma ChessΤMars (x:Points (n+m)): (T).read x (tied (TiesMars _ i) (TiesMars _ j) a) = PoolDMars ((LedgerMars i).map (BoreLMars a m)++(LedgerMars j).map (BoreRMars a n)) (TerraMars p Y (Fin.append (TurnupMars a ∘ τCoreMars i) (τCoreMars j))) x:=by
 let u:= wispsMars (R_ε) i; let w:LabelsMars d:= (SliceTieMars d).symm (u,j)
 have e: LeftArmMars d w=u:= congrArg Prod.fst ((SliceTieMars d).apply_symm_apply (u,j)); have h: RightArmMars d w=j:=congrArg Prod.snd ((SliceTieMars d).apply_symm_apply (u,j)); unfold tied; rw [←RibsMirrorMars]; rw [show Fin.append (TiesMars _ u) (TiesMars _ j)=TiesMars d w from ?_, TiesPriceMars]; swap; · rw [←e,←h, AppendixLMars]
 change PoolDMars (LedgerMars w) _ x= _; rw [tearMars a d w, ← AppendixUMars, e,h,(show u=_ from rfl)]; rw [show τCoreMars (d:=d∘Fin.castAdd m) u=_ from turnCoreMars a _ i,show List.map _ (LedgerMars u)= _ from TurnLedgerMars a d i] -- tune
lemma TopsPayMars (d:NSF.Caps n)(e:NSF.Caps m)(b: LabelsMars d)(k: LabelsMars e)(x:Points (n+m)) : (T).read x (tied (TiesMars _ b) (TiesMars _ k) a) = PoolDMars ((LedgerMars b).map (BoreLMars a m) ++ (LedgerMars k).map (BoreRMars a n)) (TerraMars p Y (Fin.append (TurnupMars a ∘ τCoreMars b) (τCoreMars k))) x:=by
 obtain ⟨Δ,h,v⟩ : ∃ D:NSF.Caps (n+m),D ∘ Fin.castAdd m=d∧ D ∘ Fin.natAdd n=e:=⟨Fin.append d e,funext (fun i=>Fin.append_left ..),funext (fun i=> Fin.append_right ..)⟩
 subst d; subst e; exact ChessΤMars p Y a Δ b k x
#print axioms TopsPayMars
end YM.GaugeFieldConstruction.Ember.Volumetric
