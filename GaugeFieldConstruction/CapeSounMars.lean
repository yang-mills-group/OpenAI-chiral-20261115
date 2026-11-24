import GaugeFieldConstruction.CasimirMars
/-!
 # quotient stress and coalescence.Ei zero derivative. 
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
-- classes. generators through-4.Change Rise equals each formal derivative in class etc.
noncomputable def mintClassMars (d:ℕ)(l:TrailsMars d): ΧiMars→ₗ[ℂ] (T).Field d:= ((T).project d).comp (mintUnoMars d l)
abbrev BegMars (a:ℕ):= mintClassMars p Y a (TrailBlankMars a)
-- class eval linear. head law orientation via generating by cone.
variable {p Y}(H:FirstPackMars p Y)
include H
lemma extConeMars {a:ℕ}(B C: FlyerMars a)(h:∀ (n:ℕ)(x:Points (n+1))(D:NSF.Caps n)(v:LabelsMars D),x∈conf _→ (T).read x (Fin.cons (PostMars a B) (TiesMars D v))=(T).read x (Fin.cons (PostMars a C) (TiesMars D v))) : (T).project a B=(T).project a C:=by
 apply (T).field_ext (SymHallMars H); intro n q x hx; obtain ⟨w,rfl⟩:= LiftQtyMars q; rw [AcostMoon H hx,AcostMoon H hx,FullTailQtyMars,FullTailQtyMars]; apply sum_congr rfl; intro i _; rw [h n x _ _ hx]
lemma MonetArcMars (d:ℕ)(l:TrailsMars d)(i:MariaMars): mintClassMars p Y d l (MCoreMars i)=(T).project d (coneOneMars d (IndexMars d (i,l))):=by
 apply extConeMars H; intro n x D v hx
 change (T).read x (Fin.cons (PostMars d (mintUnoMars d l (MCoreMars i))) (TiesMars D v)) = (T).read x (Fin.cons (coneMaskMars d _) _)
 rw[mintCoinMars _ _ _ hx, ArcBillMoon _ _,show ChaseMars d (IndexMars d (i,l))=(i,l) from (IndexMars d).symm_apply_apply _]
lemma mintStarMars (d)(l:TrailsMars d)(x:ΧiMars): (T).conj (BellSpinMars H) d (mintClassMars p Y d l x)=mintClassMars p Y d l (Calibration.shade four x):=by
 let F:=mintClassMars p Y d l
 conv_lhs=> rw [← valueUnoAtMars x,UniAtMars,_root_.map_sum,_root_.map_sum]
 conv_rhs=> rw [← valueUnoAtMars x,UniAtMars,map_sum,map_sum]
 apply sum_congr rfl; intro i hi; let v:=(valueUnoMars x) i
 rw [map_smul, (Calibration.shade four).map_smulₛₗ,MFixedMars, MonetArcMars H, ((T).conj (BellSpinMars H) d).map_smulₛₗ, map_smul,MonetArcMars H,NSF.Table.conj_project]
 refine congrArg (((starRingEnd ℂ) v) • ·) (congrArg ((T).project _) (show star (coneOneMars d (IndexMars d (i,l)))= (_ : FlyerMars d) from ?_))
 ext1 j; change star (coneOneMars d _ j)=_; by_cases g:j=IndexMars d (i,l) <;>simp [coneOneMars,g] -- tune
omit H in
lemma orbitVoidMars (s:Signed)(d:ℕ)(i:MariaMars): arcActsMars d s (IndexMars d (i,TrailBlankMars _))= IndexMars d (MActsMars s i, TrailBlankMars d):=by
 simp only [arcActsMars,Function.comp_apply,Equiv.symm_apply_apply]; congr 1; refine Prod.ext rfl ?_; exact congrArg (fun v=> ((⟨0,v⟩:TrailsMars d))) (funext (fun i=>Fin.elim0 i))
lemma mintWindMars (s:Signed)(d)(x:ΧiMars): (T).mirror (BellSpinMars H) d s (BegMars p Y d x)=BegMars p Y d (spinFrame _ s x):=by
 conv_lhs=>rw[←valueUnoAtMars x,UniAtMars,map_sum,map_sum]
 conv_rhs=>rw[←valueUnoAtMars x,UniAtMars,map_sum,map_sum]; unfold BegMars
 apply sum_congr rfl; intro i _; rw [map_smul,map_smul,map_smul,map_smul, ←MActsAtMars]; congr 1; rw [MonetArcMars H, NSF.Table.mirror_project]; change (T).project d (writeArcMars _ _ (Pi.single _ 1))=_; rw[writeArcOneMars, orbitVoidMars]; exact (MonetArcMars H d (TrailBlankMars d) _).symm
omit H in
lemma stressTurnMars (p:Ticket u C)(s:Signed) (i j) : spinFrame four s (p.J i j)=pay ((s.flip i).xor (s.flip j)) (p.J (s.perm i) (s.perm j)):=by unfold Ticket.J pens; rw [p.dawn.tect.val.property.2]; simp only [Cauchy.Row.Record.sym_turn, Cauchy.Row.Record.fee_turn]
noncomputable def CStressMars (p:Ticket u C) (Y:AreaQc S): NSF.Table.Stress (BellTableMars p Y):=fun i j=> - BegMars p Y 4 (p.J i j)
lemma DrawRawMars: NSF.Table.RawTensor (BellSpinMars H) (CStressMars p Y):=by
 intro s i j; unfold CStressMars; rw [map_neg,mintWindMars H,stressTurnMars, sum_eq_single (s.perm i)]
 · rw[sum_eq_single (s.perm j)] -- not NSC self
   · simp only [Signed.matrix_at,↓reduceIte]; cases s.flip i <;>cases s.flip j<;>simp -- tune
   · intro b _ u; simp[Signed.matrix_at, Ne.symm u]
   simp
 · intro a _ u; simp [Signed.matrix_at,Ne.symm u]
 simp
-- divergence at raw with tail via pool sums
lemma cloakMintZeroMars (x:Points (n+1))(h:x∈conf _)(d:NSF.Caps n)(v:LabelsMars d)(a:ℕ)(B:ΧiMars)(i:Axis):
    (T).read x (Fin.cons (PostMars (a+1) (ΛSlopeMars a (i,false) (mintUnoMars a (TrailBlankMars a) B))) (TiesMars d v))= D (direction 0 i) (BillHeadMoon p Y v [] B) x:=by
 rw [guidePriceMars _ _ _ _ _ h]; exact GermD _ (((conf_open _).eventually_mem h).mono (fun y t=>mintCoinMars p Y y t d v a (TrailBlankMars a) B))
lemma PoolRotateMars {m:ℕ}(p: Points m)(h:p∈conf _)(i:Fin m)(l:List (Points m))(a:Axis) (F:Points m→ℂ)(H': ContDiffOn ℝ ∞ F (conf m)): Analysis.D (direction i a) (PoolDMars l F) p= PoolDMars l (Analysis.D (direction i a) F) p:=by
    rw [←poolHeadMars,show Analysis.D _ F= PoolDMars [direction i a] F from rfl,← pool_appendMars]; exact turnPoolMars (conf_open _) F H' p h _ _ (by simpa using (show List.Perm (direction i a :: (l++[])) (l++[direction i a]) from List.perm_middle.symm)) -- tune
lemma poolSumsMars (x:Points (n+1))(h:x∈conf (n+1))(d:NSF.Caps n)(v:LabelsMars d)(j:Axis):
    ∑ a:Axis, D (direction 0 a) (BillHeadMoon p Y v [] (p.J a j)) x=0:=by
 let L:= ((τGuideMars v).map CloverHMars).map guideDirMars; let k(a:Axis):= Fin.cons (α:=fun _:Fin (n+1)=>ΧiMars) (p.J a j) (τCoreMars v)
 let F(a:Axis):= D (direction 0 a) (M (k a)); have he(a):ContDiffOn ℝ ∞ (F a) (conf _):=fun s hs=> (dSmooth (m:=∞) (TerraAt p Y _ _ hs) _ (by simp)).contDiffWithinAt
 rw [show (∑ a:Axis, D (direction 0 a) (BillHeadMoon p Y v [] (p.J a j)) x)=(∑ a:Axis,PoolDMars L (F a) x) from ?_, ← pool_sumMars L Finset.univ F _ (conf_open _) (fun i _=>he i) x h]
 · have ht : (fun s=>∑ a:Axis,F a s)=ᶠ[𝓝 x] (fun _=>0):= ((conf_open _).eventually_mem h).mono (fun y t=>by
       let u:=Fin.cons (α:=fun _:Fin (n+1)=>ΧiMars) 0 (τCoreMars v)
       have hu:= divMars p Y 0 u j y t; simp_rw [u, Fin.update_cons_zero] at hu; exact hu)
   rw [show PoolDMars _ _ x= PoolDMars L (fun _:Points (n+1)=> (0:ℂ)) x from ((pool_germMars x L _ _ ht).self_of_nhds)]; apply congrFun (show PoolDMars L (fun _:Points (n+1)=> (0:ℂ))=(fun _=>0) from ?_) -- tune
   induction L with
   | nil=> rfl
   | cons a l hs=> rw[poolHeadMars,hs]; funext i; simp [D]
 exact sum_congr rfl fun i _=> PoolRotateMars (p:=p) (Y:=Y) H x h 0 L i (TerraMars p Y (k i)) (TerraSm p Y _)
lemma CNetMars : NSF.Table.Conserved (DictumMars p Y) (BellSpinMars H) (CStressMars p Y) where
 symmetric a b:=by simp only[CStressMars, p.strict a b]
 real a b:= by unfold CStressMars; rw [map_neg,mintStarMars H,p.real_form]
 divergence b:=by
    let F(i:Axis): FlyerMars 5:= ΛSlopeMars 4 (i,false) (mintUnoMars 4 (TrailBlankMars 4) (p.J i b))
    unfold CStressMars; simp_rw [map_neg,sum_neg_distrib,neg_eq_zero]; change (∑ i:Axis, (T).project 5 (F i))=(T).project 5 0 -- map_zero not defeq! fix
    rw [← map_sum]; apply extConeMars H; intro n x D v hx
    change ((T).injectFront (TiesMars D v) x 5) (∑ i:Axis,F i)= ((T).injectFront _ _ _) 0; rw [map_zero,map_sum]; exact Eq.trans (sum_congr rfl (fun i _=> cloakMintZeroMars H x hx D v 4 (p.J i b) i)) (poolSumsMars H x hx D v b)
#print axioms CNetMars
#print axioms DrawRawMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
