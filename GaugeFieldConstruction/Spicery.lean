import GaugeFieldConstruction.Equerry
import YM.CF.Roots.Seat
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open HushP ModuleB Pastry
-- entries in PH houses: both endpoints. not represented yet as Mark physical.
open Housing
variable (o:Skye.Seat n)
-- A1 frame: g star transport from root at x. B_F paid using transported O.
-- algebra of insertion indices (complex linear in G). prove on paid subspace.
open Flot
set_option maxRecDepth 2800
variable (M:Tulip.Male)
open scoped YM.CF.Mew
variable {T U V:InkD n}{F W:Waves}{a b:ℝ}(h)
-- Assembly on puncture label (separate from unit).
variable {h}
-- proof complex linearity at large n. Pal Norm issue use postF, ηZ support.
private abbrev skyO (x:ℂ)(P:PalOne):PalOne:= postF P (pawnC x)
private lemma sky_sub (x:ℂ)(A B: PalOne):oSub (skyO x A) (skyO x B)=skyO x (oSub A B):=by
 apply Prod.ext _ (Prod.ext (ContinuousLinearMap.ext fun i=>?_) (dual_uni _ _ fun i=>?_)) <;> (
  first| exact (map_sub (pawnC x) A.1 B.1).symm | exact (map_sub (pawnC x) (A.2.1 _) (B.2.1 _)).symm| exact (map_sub (pawnC x) (A.2.2.val _ _) (B.2.2.val _ _)).symm)
lemma seed_scale (x y:Site n)(A:Pal)(z:ℂ) : seed_k x y (z • A)= z • seed_k x y A:=by ext a b; simp only [seed_k,Matrix.of_apply,Matrix.smul_apply]; split <;> simp
lemma seat_sum_t(x y:Site n)(A B:Pal): seed_k x y (A+B)=seed_k x y A+seed_k x y B:=by ext a b; simp only [seed_k,Matrix.of_apply,Matrix.add_apply]; split <;> simp
lemma pulse_U (F:Op (Single n))(x:ℂ) : pulseH (x • F)=x • pulseH F:=Subtype.ext (pulse_src ..)
lemma view_Z (k:lotV)(A:Pane n→Pal)(z:ℂ)(h:ℝ): viewW o k (z • A) h= z • viewW o k A h:=by
 funext i; unfold viewW beamer modelK; simp only [Function.comp_apply,Pi.smul_apply]; unfold carryU; rw [Matrix.mul_smul,Matrix.smul_mul,smul_comm (saleCoeff ..) z,seed_scale,pulse_U] -- tune pi
lemma view_plus(k:lotV)(A B:Pane n→Pal)(h:ℝ) : viewW o k (A+B) h=viewW o k A h+viewW o k B h:=by
 funext i; unfold viewW beamer modelK; simp only [Function.comp_apply,Pi.add_apply]; unfold carryU; rw [mul_add, add_mul,smul_add,seat_sum_t,pulse_add]
lemma mallet_Z(k:GateI)(A:ComG→L[ℝ]Pal)(z:ℂ): mallet o (z • A) p k = z • mallet o A p k:=rfl
lemma mallet_H(k:GateI)(A B:ComG→L[ℝ]Pal):mallet o (A+B) p k=mallet o A p k+mallet o B p k:=rfl
private lemma mkD_mult (f:yardLot)(x:ℂ): mkD o M (x • f)=skyO x (mkD o M f):=by
 let p:= notesK o f 1; let P:= winJ o M 1 p; have hp:notesK o (x • f) 1=x • p:=by
    unfold notesK p; unfold notesK; rw [Finset.smul_sum]; apply sum_congr rfl; intro i _; unfold modelK; rw [Pi.smul_apply,smul_comm (saleCoeff ..) x,seed_scale]
 rw [←billMore o M (x • f) (h:=1) one_ne_zero,←billMore o M f (h:=1) one_ne_zero,hp]
 symm; refine ((AptK.geomF (tab (o:=o) (h:=1) M p) _).equal (Eventually.of_forall fun i=>?_)).unique (tab (o:=o) (h:=1) M _)
 unfold TabX; rw [stream_c 1 o M p x i, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul]; rfl
private lemma grain_run (x:ℂ)(P:PalOne): grainD (M:=M) o (skyO x P)=skyO x (grainD (M:=M) o P):=by
 unfold grainD; rw [show Ωlane (skyO x P)= x • Ωlane P from ?_, mkD_mult,sky_sub]
 funext i; change ηZ (x • P.1) neutralK i=x • ηZ P.1 neutralK i; simp [ηZ,Pi.single_apply,apply_ite]; split <;> simp_all
omit o M in
private lemma step_Ξ (x:ℂ)(i:lotV)(A: Pal): ηZ (x • A) i=x • ηZ A i:=by funext j; simp [ηZ,Pi.single_apply,apply_ite]; split <;> simp_all
private lemma gain_run (x:ℂ)(P:PalOne): gainT (M:=M) o (skyO x P)= skyO x (gainT (M:=M) o P):=by
 have he(P:PalOne)(i:slice): pinD i ((-Complex.I) • (skyO x P).2.1 (voltS i))= x • pinD i ((-Complex.I) • P.2.1 (voltS i)):=by
    change pinD i ((-Complex.I) • x • _) = _; rw [smul_comm (-Complex.I)]; unfold pinD; simp only [step_Ξ x, smul_sub]; try rfl
 have hp(P:PalOne): Ωleg (skyO x P)=x • Ωleg P:=by unfold Ωleg; rw [smul_sum]; exact sum_congr rfl fun i _=>he P i
 unfold gainT; rw [grain_run,hp,mkD_mult, sky_sub]
private lemma gain_Ξ (f:PalOne)(x:ℂ): Ωleg (skyO x f)=x • Ωleg f:=by
 unfold Ωleg; rw [smul_sum]; apply sum_congr rfl; intro i _; change pinD i ((-Complex.I) • x • _) = _; rw [smul_comm (-Complex.I)]; unfold pinD; simp only [step_Ξ x, smul_sub]; try rfl
set_option maxHeartbeats 75000 in
private lemma field_Ξ (T:PalOne)(x:ℂ):fieldX M o (skyO x T)= x • fieldX M o T:=by
 have he(i:PalOne): Ωray (skyO x i)= x • Ωray i:=by
    unfold Ωray; rw [smul_sum]; apply sum_congr rfl; intro k _; change spinD _ _ ((-1/2:ℂ) • x • _) = _; rw [smul_comm (-1/2:ℂ)]; unfold spinD; simp only [step_Ξ x,smul_sub]; try rfl
 unfold fieldX; rw [show Ωlane (skyO x T)= x • Ωlane T from step_Ξ x neutralK _,grain_run,gain_Ξ, gain_run,he,smul_add,smul_add]
private lemma field_add_t(T U:PalOne):fieldX M o (oAdd T U)=fieldX M o T+fieldX M o U:=by
 have ht(x y z w:PalOne): oSub (oAdd x y) (oAdd z w)=oAdd (oSub x z) (oSub y w):=by exact (show ∀ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](x y z w:Ole E F), (x+y)-(z+w)=(x-z)+(y-w) from by intro _ _ _ _ _ _ x y z w; abel) x y z w
 have hf(k:lotV)(A B:Pal): ηZ (A+B) k=ηZ A k+ηZ B k:= Pi.single_add .. -- tune
 have hg(V W:PalOne): grainD (M:=M) o (oAdd V W)=oAdd (grainD (M:=M) o V) (grainD (M:=M) o W):=by unfold grainD; rw [show Ωlane (oAdd V W)=Ωlane V+Ωlane W from hf neutralK _ _,mkD_plus,ht]
 have he(V W:PalOne) : Ωleg (oAdd V W)= Ωleg V + Ωleg W:=by
    unfold Ωleg; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _; change pinD i ((-Complex.I) • (V.2.1 _+W.2.1 _)) =_; rw [smul_add]; unfold pinD; rw [hf,hf]; abel
 have hs(V W:PalOne): Ωray (oAdd V W)= Ωray V+Ωray W:=by
    unfold Ωray; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _; change spinD i.1 i.2 ((-1/2:ℂ) • (V.2.2.val _ _ + W.2.2.val _ _))=_; rw [smul_add]; unfold spinD; simp_rw [hf]; abel
 have hh(V W:PalOne): gainT (M:=M) o (oAdd V W)=oAdd (gainT (M:=M) o V) (gainT (M:=M) o W):=by unfold gainT; rw [hg,he,mkD_plus,ht]
 unfold fieldX; rw [show Ωlane (oAdd T U)= Ωlane T+Ωlane U from hf neutralK _ _,hg, hh, he,hs]; abel
lemma Pure_add (x y:Waves): αPure o M p (x+y) h=αPure o M p x h+αPure o M p y h:=by
 have he: αPureX o M p (x+y) = αPureX o M p x+αPureX o M p y:= field_add_t o M (chartF x) (chartF y); unfold αPure blurred; rw [he,←sum_add_distrib]; exact sum_congr rfl fun i _=>view_plus o i (fun _=> αPureX o M p x i) (fun _=> αPureX o M p y i) h -- tune
lemma Pure_se(x:Waves)(c:ℂ): αPure o M p (c • x) h= c • αPure o M p x h:=by
 have he: αPureX o M p (c • x)=c • αPureX o M p x:= field_Ξ o M (chartF x) c; unfold αPure blurred; rw [he,smul_sum]; exact sum_congr rfl fun i _=>view_Z o i (fun _=> αPureX o M p x i) c h
lemma Guide_a (P:0<h)(v:p.power≤3)(w:p.order ≤6)(t:20<n.val)(x y:Waves):αGuide o M p (x+y) h= αGuide o M p x h+ αGuide o M p y h:=by
 unfold αGuide; rw [Pure_add,landPlus M (suit_P o M P x v w t) (suit_P o M P y v w t)]
 exact (show ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](x y z w:ComG→L[ℝ]E), x+y-(z+w)=(x-z)+(y-w) from by intro _ _ _ x y z w; abel) (bm5 x).val (bm5 y).val (landA M o (αPure o M p x h) p h) (landA M o (αPure o M p y h) p h)
set_option maxHeartbeats 150000 in
lemma Guide_K (P:0<h)(v:p.power≤3)(w:p.order ≤6)(t:20<n.val)(x: Waves)(a:ℂ): αGuide o M p (a • x) h=a • αGuide o M p x h:=by
 let Y:= αPure o M p x h; have hp:= suit_P o M P x v w t; have he:=export_full o M hp P.le rfl; let L:= landA M o Y p h; let c:= a;
 have ht: a • L = landA M o (a • Y) p h:= Eq.trans (congrArg (fun i:ComG→L[ℝ]Pal=> a • i) he.mixed.symm) (linearHE o M he hp a P.le).mixed
 unfold αGuide; rw [Pure_se]; change a • (bm5 x).val-_= _; rw [← (show a • L=_ from ht)] -- tune Y unfold
 apply ContinuousLinearMap.ext; intro i; change a • _- (a • L i) =_; exact Eq.symm (smul_sub a ((bm5 x).val i) (L i))
lemma Mix_a(P:0<h)(v:p.power≤3)(w:p.order ≤6)(t:20<n.val)(x y:Waves): αMixed o M p (x+y) h=αMixed o M p x h+αMixed o M p y h:=by
 unfold αMixed; rw [Guide_a o M P v w t]; unfold capT; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _; rw [mallet_H,view_plus]
lemma Mix_p (P:0<h)(v:p.power≤3)(w:p.order ≤6)(t:20<n.val)(x:Waves)(a:ℂ): αMixed o M p (a • x) h= a • αMixed o M p x h:=by
 unfold αMixed; rw [Guide_K o M P v w t]; unfold capT; rw [smul_sum]; apply sum_congr rfl; intro i _; rw [mallet_Z,view_Z]
set_option maxHeartbeats 150000 in
lemma Gauge_A (x y:Waves)(p:BudgetPoint): αGauge o p (x+y)=αGauge o p x+αGauge o p y:=by
 funext i; let e(x: Waves):= bloomT (bF4 x).val (bF5 x); let Tc(w:Waves):= terrace o p (e w) i; change hollow (Tc (x+y))=_
 have he:Tc (x+y)=Tc x+Tc y:=by
    unfold Tc terrace; rw [←sum_add_distrib]; apply sum_congr rfl; intro j _; simp only [νt,ψTile,mono_apply]
    rw [show e (x+y) (ζedge j.1) (ζedge j.2)=e x (ζedge j.1) (ζedge j.2)+e y (ζedge j.1) (ζedge j.2) from ?_,mul_add,add_mul]
    unfold e; rw [bloom_apply,bloom_apply,bloom_apply]; let L:=ζedge j.1; let Q:=ζedge j.2; change ((bF4 x).val L.1 Q.1+(bF4 y).val L.1 Q.1)+( (bF5 x L.1 Q.2+bF5 y L.1 Q.2)+(bF5 x Q.1 L.2+bF5 y Q.1 L.2)) = _; abel -- tune
 rw [he]; apply Subtype.ext; exact add_smul ..
set_option maxHeartbeats 150000 in
lemma Gauge_B(x:Waves)(a:ℂ)(p:BudgetPoint): αGauge o p (a • x)=a • αGauge o p x:=by
 funext i; let e(x: Waves):= bloomT (bF4 x).val (bF5 x); let Tc(w:Waves):= terrace o p (e w) i; change hollow (Tc (a • x))=_
 have he:Tc (a • x)= a*Tc x:=by
    unfold Tc terrace; rw [mul_sum]; apply sum_congr rfl; intro j _; simp only [νt,ψTile,mono_apply]; rw [show e (a • x) (ζedge j.1) (ζedge j.2)= a* e x (ζedge j.1) (ζedge j.2) from ?_]; ring
    unfold e; rw [bloom_apply,bloom_apply]; change a*((bF4 x).val _ _)+(a* (bF5 x _ _)+ a*(bF5 x _ _))= _; rw [mul_add,mul_add] -- tune
 rw [he]; apply Subtype.ext; exact mul_smul ..
variable (P:0<h)(v:p.power≤3)(w:p.order ≤6)(t:20<n.val)
set_option maxHeartbeats 150000 in
def hatchP : Waves→ₗ[ℂ] InkD n where
 toFun x:= αPress o M p x h
 map_add' x y := by unfold αPress; rw [Gauge_A, Mix_a o M P v w t, Pure_add]; abel -- v,w,t in sec proof may omitted by lean auto; tune
 map_smul' a x:=by unfold αPress; rw [Gauge_B,Pure_se,Mix_p o M P v w t,RingHom.id_apply,smul_add,smul_add]
set_option maxHeartbeats 150000 in
lemma hatch_v (x:Waves): hatchP o M P v w t x=αPress o M p x h:=rfl
end Layout
end Lenten
end YM.CF.TableF
end
