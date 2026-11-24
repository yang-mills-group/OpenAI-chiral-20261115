import GaugeFieldConstruction.PentagucMars
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
open NSF.Table (PastTest)
structure PatMars (a:Axis)(n:ℕ) where
 test : Test n
 east : tsupport test⊆ SimArchMars a n
abbrev PstMars {a:Axis}(Q:PastTest ΡeaderMars a):PatMars a Q.n:=⟨Q.f,fun x hx=>stays Q hx⟩
abbrev WrapPtMars (a:Axis)(p:PatMars a n):PastTest ΡeaderMars a:= ⟨n,fun _=> ΡeaderMars.one 0,p.test,fun x h=> (p.east h).2⟩
variable {a}
noncomputable def ReloadMars (A:PatMars a n)(p:Points n):PatMars a n:= ⟨-(tilt p A.test),by
    -- values
    rw [show tsupport ((-(tilt p A.test):Test n) :Points n→ℂ)=tsupport (tilt p A.test) from ?_]; · exact (dband p A.test).trans A.east
    unfold tsupport; congr 1; ext i; change - (_ : ℂ)≠0↔_; simp -- tune
  ⟩
lemma ReloadHeightMars (A:PatMars a n)(p x:Points n): (ReloadMars A p).test x= -(D p A.test x):=by change - tilt p A.test x=_; rw[tilt_pays]
noncomputable def ChainBookMars (A: PatMars a n)(L: List (Points n)):PatMars a n:=match L with
 | []=>A
 | gxx::bxz=> ChainBookMars (ReloadMars A gxx) bxz
abbrev PatentMars (p: PatMars a n)(q : PatMars a m):Test (n+m):= withOther (WrapPtMars a p) (WrapPtMars a q)
lemma PatchHMars (p:PatMars a n)(q:PatMars a m)(x:Points n)(y:Points m): PatentMars p q (closedUp a x y)= Star.star (p.test x)*q.test y:=by
 change Star.star (p.test ((pairIso a) _).1)* q.test ((pairIso a (n:=n) (m:=m)) _).2=_; rw [show (pairIso a) (closedUp a x y)=(x,y) from ContinuousLinearEquiv.apply_symm_apply ..]; -- tune pairIso argument a syntax
variable (A:PatMars a n)(B:PatMars a m)
local notation "v66"=> pairIso (n:=n) (m:=m) a
abbrev AsphaltMars (n m:ℕ)(a:Axis):Points (n+m)→L[ℝ]Points n:= (ContinuousLinearMap.fst ..).comp ((pairIso (n:=n) (m:=m) a).toContinuousLinearMap) -- syntax tune
abbrev AlkaliMars (n m:ℕ)(a:Axis):Points (n+m)→L[ℝ]Points m:= (ContinuousLinearMap.snd ..).comp ((pairIso (n:=n) (m:=m) a).toContinuousLinearMap)
local notation "E_x"=> AsphaltMars n m a
local notation "E_y"=> AlkaliMars n m a
lemma dfHandleMars (X:Type*)[NormedAddCommGroup X][NormedSpace ℝ X](F G:X→ℂ)(x v:X)(M K: X→L[ℝ]ℂ)(hf: HasFDerivAt F M x)(hg:HasFDerivAt G K x): fderiv ℝ (fun x=> F x * G x) x v= F x*K v+ M v*G x:= by
 rw [fderiv_fun_mul hf.differentiableAt hg.differentiableAt,hf.fderiv,hg.fderiv]; simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]; ring
lemma PillageMars (x v:Points (n+m)): tilt v (PatentMars A B) x= Star.star (A.test (E_x x))* D (E_y v) B.test (E_y x)+ Star.star (D (E_x v) A.test (E_x x))* B.test (E_y x):=by
 let C':= Complex.conjCLE.toContinuousLinearMap; let F:=C' ∘ A.test ∘ E_x; let G:=B.test ∘ E_y
 have he:Differentiable ℝ (A.test ∘ E_x):= (diffT _).comp (E_x).differentiable
 have hp: Differentiable ℝ F:= C'.differentiable.comp he; have hv:Differentiable ℝ G:= (diffT _).comp (E_y).differentiable
 let i:= (fderiv ℝ A.test ((AsphaltMars n m a) x)); let j:=fderiv ℝ B.test ((AlkaliMars n m a) x)
 let c:=AsphaltMars n m a; let d:=AlkaliMars n m a
 have HI: HasFDerivAt F (C'.comp (i.comp c)) x:= C'.hasFDerivAt.comp x ((diffT A.test (c x)).hasFDerivAt.comp x c.hasFDerivAt); have H:HasFDerivAt G (j.comp d) x:= (diffT B.test _).hasFDerivAt.comp x d.hasFDerivAt
 rw [tilt_pays,show (PatentMars A B : Points (n+m)→ℂ)=fun x=>F x*G x from rfl]
 change fderiv ℝ (fun x=> F x*G x) x v = F x* (j (d v)) + C' (i (c v))*G x
 exact dfHandleMars (Points (n+m)) F G x v _ _ HI H
lemma PillsLMars (v: Points n): - tilt (BoreLMars a m v) (PatentMars A B)= PatentMars (ReloadMars A v) B:=by
 ext1 x; let U:= BoreLMars a m v; have he: (pairIso a) U=(v,(0:Points m)):= ContinuousLinearEquiv.apply_symm_apply ..
 change - tilt U _ x= Star.star ((ReloadMars A v).test ((AsphaltMars n m a) x))* B.test ((AlkaliMars n m a) x); rw[PillageMars, ReloadHeightMars, show E_x U=v from congrArg Prod.fst he,show E_y U=0 from congrArg Prod.snd he,D,map_zero]; simp -- tune syntax
lemma PillsRMars (v:Points m) : - tilt (BoreRMars a n v) (PatentMars A B)= PatentMars A (ReloadMars B v):=by
 ext1 x; let U:=BoreRMars a n v; have he: (pairIso a) U=((0:Points n),v):= ContinuousLinearEquiv.apply_symm_apply ..
 change - tilt U _ x= Star.star (A.test ((AsphaltMars n m a) x))* (ReloadMars B v).test ((AlkaliMars n m a) x); rw [PillageMars,ReloadHeightMars, show E_x U=0 from congrArg Prod.fst he,show E_y U=v from congrArg Prod.snd he]; simp [D]
lemma CarryPayMars (t: Test n)(v:Points n)(F:Points n→ℂ)(h:ContDiffOn ℝ ∞ F (conf n)) : t.applyTo (D v F)=(- tilt v t : Test n).applyTo F:=by
 have H(x) (q:x∈conf n):ContDiffAt ℝ ∞ F x:= (h _ q).contDiffAt ((conf_open n).mem_nhds q); have ht:ContinuousOn (D v F) (conf n):=fun x hx=> (dSmooth (m:=∞) (H _ hx) v (by simp)).continuousAt.continuousWithinAt
 unfold YM.Test.applyTo; rw [show (fun x:Points n=>(-tilt v t:Test n) x*F x)= -(fun x=>(tilt v t) x*F x) from funext (fun i=>neg_mul ..)]; change _=∫ x:Points n,- ((tilt v t) x*F x); rw [integral_neg]; simp_rw [tilt_pays]; have e:= (tilt v t).smearing h.continuousOn; simp_rw [tilt_pays] at e; exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable e (t.smearing ht) (t.smearing h.continuousOn) (fun i _=>diffT t i) (fun i j=> (H i (t.tsupport_subset j)).differentiableAt (by simp))
variable (F:Fin (n+m)→ΧiMars)
local notation "F_U"=> TerraMars p Y F
lemma chainCutMars (L:List (Points n))(S:List (Points m)): (PatentMars A B).applyTo (PoolDMars ((L.map (BoreLMars a m))++ (S.map (BoreRMars a n))) (TerraMars p Y F))=(PatentMars (ChainBookMars A L) (ChainBookMars B S)).applyTo (TerraMars p Y F):=by
 have h(l:List (Points (n+m))): ContDiffOn ℝ ∞ (PoolDMars l F_U) (conf _):= fun i j=> (poolSmMars _ _ _ (TerraAt p Y F i j)).contDiffWithinAt
 induction L generalizing A with
 | nil=>
    simp only[List.map_nil,List.nil_append]; induction S generalizing B with
    | nil=>rfl
    | cons i b ih=> simp only [List.map_cons]; rw [poolHeadMars,CarryPayMars _ _ _ (h _),PillsRMars]; exact ih _
 | cons i b ih=> simp only[List.map_cons,List.cons_append]; rw[poolHeadMars,CarryPayMars _ _ _ (h _),PillsLMars]; exact ih _
#print axioms chainCutMars
end YM.GaugeFieldConstruction.Ember.Volumetric
