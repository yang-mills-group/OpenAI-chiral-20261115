import GaugeFieldConstruction.Henbit
import YM.CF.Moto.Road
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
variable {M:Tulip.Male}
open scoped ComplexConjugate
-- Upon direct moment jet
variable (o:Skye.Seat n)
def Ωlane (V:PalOne):yardLot:= ηZ V.1 neutralK
def Ωleg (V:PalOne):yardLot:= ∑ i:slice, pinD i ((-Complex.I) • V.2.1 (voltS i))
def Ωray (V:PalOne):yardLot:= ∑ i:slice ×slice,spinD i.1 i.2 ((-1/2:ℂ) • (V.2.2.val (voltS i.1) (voltS i.2)))
def grainD (V:PalOne):= (show PalOne from oSub V (mkD o M (Ωlane V))) -- implicit M not bound need binder
def gainT (V:PalOne):= (show PalOne from oSub (grainD (M:=M) o V) (mkD o M (Ωleg (grainD (M:=M) o V))))
omit o in
lemma lane_f (V:PalOne)(u:JetX V): coD (Ωlane V):=Dnotes _ _ u.1
omit o in
lemma legs_f (V:PalOne)(u:JetX V): coD (Ωleg V):=by unfold Ωleg; apply Dsum; intro i _; have ht:= SheetQ.step (u.2.1 (voltS i)) (-Complex.I); unfold pinD; exact Dmi (Dnotes _ _ ht) (Dnotes _ _ ht)
omit o in
lemma rays_f(V:PalOne)(u:JetX V): coD (Ωray V):=by unfold Ωray; apply Dsum; intro i _; have ht:= SheetQ.step (u.2.2 (voltS i.1) (voltS i.2)) (-1/2:ℂ); exact Dmi (Dmi (Dnotes _ _ ht) (Dnotes _ _ ht)) (Dmi (Dnotes _ _ ht) (Dnotes _ _ ht))
variable {o} (M)
lemma tail_g (V:PalOne)(u:JetX V): JetX (grainD (M:=M) o V):= Layout.JetX.diff u (padsV _ M _ (lane_f V u)) -- tune
lemma tail_T (V:PalOne)(u:JetX V): JetX (gainT (M:=M) o V):= Layout.JetX.diff (tail_g _ _ u) (padsV _ M _ (legs_f _ (tail_g _ _ u)))
lemma tail_s (V:PalOne)(u:JetX V): (grainD (M:=M) o V).1=0:=by change V.1-(mkD o M (Ωlane V)).1=0; rw [show (mkD o M (Ωlane V)).1=V.1 from ore_basis o neutralK _ u.1,sub_self]
omit M
private lemma sumC {I:Type}(T:Finset I)(W:I→yardLot): comV o (∑ i∈T,W i)= oleSum T (comV o ∘ W):=by
 classical
 induction T using Finset.induction_on with
 | empty=>simp only [sum_empty,oleSum]; apply Prod.ext _ (Prod.ext (ContinuousLinearMap.ext fun k=>?_) (dual_uni _ _ fun i=>?_)); · rw [stamp_f0]; simp -- tune
          · rw [stamp_f1]; simp; try rfl
          rw [stamp_f2]; simp; try rfl
 | @insert i T p ih=> unfold oleSum; rw [sum_insert p,sum_insert p, comV_add, ih]; rfl
lemma pledge₀(V:PalOne)(u:20<n.val): (comV o (Ωleg V)).1=0∧(comV o (Ωray V)).1=0:=by
 unfold Ωleg Ωray; rw [sumC,sumC]; simp only [oleSum,Prod.fst_sum]; exact ⟨sum_eq_zero fun i _=> (ξPoneT o _ _ (0:Views) u).1,sum_eq_zero fun i _=> (ξSpino o _ _ _ (0:Views) u).1⟩ -- tune
omit o in
lemma smQ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{I:Type}(T:Finset I)(f:I→Ole E F)(v:E): (oleSum T f).2.1 v= ∑ i∈T,(f i).2.1 v:=by simp only [oleSum,Prod.snd_sum,Prod.fst_sum,_root_.sum_apply]
omit o in
lemma smZ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{I:Type}(T:Finset I)(f:I→Ole E F)(v:E): (oleSum T f).2.2.val v v= ∑ i∈T,(f i).2.2.val v v:=by simp only [oleSum,Prod.snd_sum,Submodule.coe_sum,_root_.sum_apply]
private lemma lo_S {I:Type}(T:Finset I)(W:I→yardLot)(v:Views) : (comV o (∑ i∈T,W i)).2.1 v= ∑ i∈T,(comV o (W i)).2.1 v:= (congrArg (fun i: PalOne=>i.2.1 v) (sumC T W)).trans (smQ ..) -- TC
private lemma to_S {I:Type}(T:Finset I)(W:I→yardLot)(v:Views) : (comV o (∑ i∈T,W i)).2.2.val v v= ∑ i∈T,(comV o (W i)).2.2.val v v:= (congrArg (fun i: PalOne=>i.2.2.val v v) (sumC T W)).trans (smZ ..) -- tune
set_option maxHeartbeats 35000 in
set_option maxRecDepth 5000 in
lemma pledge₁(V:PalOne)(u:20<n.val)(x:Views): (comV o (Ωleg V)).2.1 x=V.2.1 x∧(comV o (Ωray V)).2.1 x=0:=by
 let X(i:slice):= pinD i ((-Complex.I) • V.2.1 (voltS i)); let L(i:slice):=comV o (X i); let S(i:slice×slice):=spinD i.1 i.2 ((-1/2:ℂ) • V.2.2.val (voltS i.1) (voltS i.2)); let W(i):=comV o (S i)
 have hv(i:slice): (L i).2.1 x=tips i x • V.2.1 (voltS i):=(ξPoneT o i _ _ u).2; have hw(i): (W i).2.1 x=0:= (ξSpino o i.1 i.2 (V.2.2.val (voltS i.1) (voltS i.2)) x u).2.1
 have he : ∑ i:slice,tips i x • V.2.1 (voltS i)= V.2.1 x:=by simp_rw [← map_smul]; rw [← map_sum, lays]
 have h1 : (∑ i:slice,(L i).2.1 x)=V.2.1 x:= (sum_congr rfl (fun i _=> hv i)).trans he; have h0 : ∑ i:slice×slice,(W i).2.1 x=0:=sum_eq_zero fun i _=>hw i
 exact ⟨(lo_S (o:=o) univ X x).trans h1,(lo_S (o:=o) univ S x).trans h0⟩
set_option maxRecDepth 5000 in
lemma pledge₂(V: PalOne)(u:20<n.val)(x:Views): (comV o (Ωray V)).2.2.val x x=V.2.2.val x x:=by
 let A:=V.2.2.val; let b(i:slice):= tips i x • voltS i; let S(i:slice×slice):=spinD i.1 i.2 ((-1/2:ℂ) • A (voltS i.1) (voltS i.2)); let W(i):=comV o (S i); let X:=(∑ i:slice×slice,(W i).2.2.val x x)
 have he : ∑ i:slice ×slice,A (b i.1) (b i.2)= A x x:=by
    rw [Fintype.sum_prod_type]; simp_rw [← map_sum]; rw [show ∑ i:slice,b i=x from lays _]; change ∑ i:slice,A.flip x (b i)=_; rw [←map_sum,show ∑ i:slice,b i=x from lays _]; rfl
 have hb(i j:slice): A (b i) (b j)=(tips i x*tips j x) • A (voltS i) (voltS j):=by change A.flip (b j) (tips i x • voltS i)=_; rw [map_smul]; change (tips i x) • (A (voltS i) (b j))=_; unfold b; rw [map_smul,mul_smul] -- tune first map
 have hw(i) : (W i).2.2.val x x= A (b i.1) (b i.2):=(ξSpino o i.1 i.2 (A (voltS i.1) (voltS i.2)) x u).2.2.trans (hb i.1 i.2).symm
 have h0:X=A x x:= (sum_congr rfl (fun i _=> hw i)).trans he
 exact (to_S (o:=o) univ S x).trans h0
include M
lemma pay_leg(V:PalOne)(u:20<n.val)(f:JetX V): (mkD o M (Ωleg V)).1=0∧(mkD o M (Ωleg V)).2.1=V.2.1:=by
 obtain ⟨p,h⟩:=pledge₀ (o:=o) V u
 refine ⟨(palm₀ o _ (p.symm ▸ SheetQ.blank)).trans p,ContinuousLinearMap.ext fun x=>?_⟩
 let e:= (pledge₁ (o:=o) V u x).1; exact (palm₁ _ _ _ p (e.symm ▸ f.2.1 x)).trans e
lemma pay_rays(V:PalOne)(u:20<n.val)(f:JetX V): (mkD o M (Ωray V)).1=0 ∧(mkD o M (Ωray V)).2.1=0 ∧ (mkD o M (Ωray V)).2.2=V.2.2:=by
 obtain ⟨p,h⟩:=pledge₀ (o:=o) V u
 refine ⟨(palm₀ o _ (h.symm ▸ SheetQ.blank)).trans h,ContinuousLinearMap.ext fun i=> ?_,dual_uni _ _ fun i=>?_⟩
 · let e:=(pledge₁ (o:=o) V u i).2; exact (palm₁ _ _ _ h (e.symm ▸ SheetQ.blank)).trans e
 let g:= pledge₂ (o:=o) V u i; have he:=(pledge₁ (o:=o) V u i).2; exact (palm₂ _ _ _ _ h he he (g.symm ▸ f.2.2 i i)).trans g
omit o M in
private lemma tailL (A B:PalOne)(h:A.2.1=B.2.1): (oSub A B).2.1=0:=by exact (show ∀ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](x y:Ole E F), x.2.1=y.2.1→(x-y).2.1=0 from by intro _ _ _ _ _ _ x y h; change x.2.1-y.2.1=0; rw [h]; exact sub_self (y.2.1)) A B h
set_option maxRecDepth 5000 in
lemma top_tail (V:PalOne)(u:20<n.val)(f:JetX V) : let K:= gainT (M:=M) o V; K.1=0 ∧ K.2.1=0:=by
 intro K; let T:=grainD (M:=M) o V; let F:=Ωleg T; have hV:=tail_s (o:=o) M V f; obtain ⟨p,h⟩:=pay_leg (o:=o) M T u (tail_g M V f); refine ⟨?_,?_⟩
 · change T.1-_ = _; rw [show T.1 =0 from hV,p]; exact sub_self _ -- tune
 exact tailL T (mkD o M F) h.symm
variable (o)
def fieldX (V:PalOne): yardLot:= Ωlane V+Ωleg (grainD (M:=M) o V)+Ωray (gainT (M:=M) o V)
lemma field_u(V:PalOne)(u:JetX V): coD (fieldX M o V):= Dpl (Dpl (lane_f V u) (legs_f _ (tail_g _ _ u))) (rays_f _ (tail_T _ _ u))
omit M o in
lemma oath_Z(A B C:PalOne): oAdd (oAdd A B) (oSub (oSub C A) B)=C:=by exact (show ∀ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](x y z:Ole E F), x+y+(z-x-y)=z from by intro _ _ _ _ _ _ x y z; abel) A B C
lemma field_s(V:PalOne)(u:20<n.val)(f:JetX V): mkD o M (fieldX M o V)=V:=by
 obtain ⟨p,v⟩:=top_tail (o:=o) M V u f; unfold fieldX; let T:=gainT (M:=M) o V; let Y:= mkD o M (Ωray T); rw [mkD_plus,mkD_plus]; obtain ⟨q,h,k⟩:=pay_rays (o:=o) M T u (tail_T _ _ f);
 change oAdd _ Y =_; rw [show Y=T from Prod.ext (q.trans p.symm) (Prod.ext (h.trans v.symm) k)]; exact oath_Z (mkD o M (Ωlane V)) (mkD o M (Ωleg (grainD (M:=M) o V))) V -- tune
lemma spline(V:PalOne)(u:20<n.val)(w: h≠0)(f:JetX V): winJ o M h (notesK o (fieldX M o V) h)=V:=by rw [billMore _ _ _ w,field_s _ _ _ u f]
end Layout
end Lenten
end YM.CF.TableF
end
