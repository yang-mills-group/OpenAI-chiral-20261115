import GaugeFieldConstruction.Helico
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
-- abbreviations to avoid scope drift of instances
lemma SheetQ.plus {A B:Pal}(p:SheetQ A)(h:SheetQ B):SheetQ (A+B):= ⟨by rw [mul_add,add_mul,p.bin,h.bin],fun i=> (p.tax i).add_left (h.tax i)⟩
lemma SheetQ.minus {A B:Pal}(p:SheetQ A)(h:SheetQ B):SheetQ (A-B):=⟨by rw [mul_sub,sub_mul,p.bin,h.bin],fun i=> (p.tax i).sub_left (h.tax i)⟩
lemma SheetQ.step {A:Pal}(u:SheetQ A)(b:ℂ):SheetQ (b • A):= ⟨by rw [Matrix.mul_smul,Matrix.smul_mul,u.bin],fun i=> (u.tax i).smul_left b⟩
lemma SheetQ.blank : SheetQ 0:=⟨by rw [mul_zero,zero_mul],fun i=>Commute.zero_left _⟩
lemma SheetQ.binL {A:Pal}(u:SheetQ A): baseF false*A=A:=by nth_rw 1 [←u.bin]; rw [←mul_assoc,←mul_assoc,(bladeSeal false).1.eq,u.bin]
lemma SheetQ.binR {A:Pal}(u:SheetQ A): A * baseF true=A:=by nth_rw 1 [←u.bin]; rw [mul_assoc,(bladeSeal true).1.eq,u.bin]
def oSub (P V: PalOne): PalOne:= P-V
def oAdd(P V: PalOne): PalOne:= P+V
lemma JetX.diff {A B:PalOne}(p:JetX A)(v:JetX B):JetX (oSub A B):=⟨SheetQ.minus p.1 v.1,fun i=> (SheetQ.minus (p.2.1 i) (v.2.1 i)),fun i j=> SheetQ.minus (p.2.2 i j) (v.2.2 i j)⟩
abbrev coD(f:yardLot):Prop :=∀ i,SheetQ (f i)
lemma Dnotes(i:lotV)(x:Pal)(p:SheetQ x):coD (Pi.single i x):=by intro j; rw [Pi.single_apply]; split; exact p; exact SheetQ.blank
lemma Dmi{f g:yardLot}(p:coD f)(v:coD g):coD (f-g):=fun i=> SheetQ.minus (p i) (v i)
lemma Dpl{f g:yardLot}(p:coD f)(v:coD g):coD (f+g):=fun i=> SheetQ.plus (p i) (v i)
lemma Dsum {I:Type}(S:Finset I)(p:I→yardLot)(h:∀ i∈S, coD (p i)):coD (∑ i∈S,p i):=by
 classical
 induction S using Finset.induction_on with | empty=>rw [sum_empty]; exact fun i=> SheetQ.blank| @insert i S p ih=>rw [sum_insert p]; exact Dpl (h i (mem_insert_self ..)) (ih fun i h'=>h i (mem_insert_of_mem h'))
variable (o:Skye.Seat n)
def mkD (M:Tulip.Male)(f:yardLot):PalOne:= palCart (bladeL false) (palCart (wheelP M false) (palCart (comV o f) (palCart (wheelP M true) (bladeL true))))
lemma billMore(M:Tulip.Male)(f:yardLot)(u:h ≠0): winJ o M h (notesK o f h)=mkD o M f:=by unfold winJ; rw [stamps o f u]; rfl
lemma padsV(M:Tulip.Male)(f:yardLot)(u:coD f):JetX (mkD o M f):=by rw [←billMore o M f one_ne_zero]; exact year_n o M _ (notes_mark o f u)
-- proof components once and use polarization
lemma mkD_plus (M:Tulip.Male)(f k:yardLot): mkD o M (f+k)=oAdd (mkD o M f) (mkD o M k):=by
 let X(g):=notesK o g 1; let Y(g):= TabX o M 1 (X g)
 have he(g):AptK (Y g) (mkD o M g):= billMore o M g (h:=1) one_ne_zero ▸ tab M (X g)
 have hv(x):Y (f+k) x= Y f x+ Y k x:=by
    have ht: streamF o (X (f+k)) 1 x= streamF o (X f) 1 x+ streamF o (X k) 1 x:=by unfold X; simp only [notes_fee o _ one_ne_zero,Pi.add_apply,smul_add,sum_add_distrib]
    unfold Y TabX; rw [ht,add_mul,mul_add,mul_add]
 exact ((he (f+k)).equal (Eventually.of_forall hv)).unique ((he f).joinK (he k))
lemma palm₀ (f:yardLot)(u:SheetQ (comV o f).1) : (mkD o M f).1=(comV o f).1 :=by
 let T:= (comV o f); unfold mkD; change baseF false*((wheelP M false).1*(T.1*((wheelP M true).1* baseF true)))=_; rw [plan_o,plan_o,(bladeSeal true).1.eq,show T.1*baseF true=_ from SheetQ.binR u,show baseF false*T.1=_ from SheetQ.binL u]; exact SheetQ.binL u
lemma palm₁ (f:yardLot)(v:Views)(q:(comV o f).1=0)(u:SheetQ ((comV o f).2.1 v)) : (mkD o M f).2.1 v=(comV o f).2.1 v:=by
 unfold mkD palCart; simp only [cart_0,cart_1, plan_o,q]; change 0* _+baseF false* ( _*(0*_) + baseF false*( _*(baseF true*baseF true)+ (0:Pal)*_)) = _; rw [(bladeSeal true).1.eq]; simp only [zero_mul,mul_zero,add_zero,zero_add]; rw [SheetQ.binR u,SheetQ.binL u,SheetQ.binL u]
set_option maxHeartbeats 60000 in
lemma palm₂ (f:yardLot)(v w:Views)(q:(comV o f).1=0)(e:(comV o f).2.1 v=0)(g:(comV o f).2.1 w=0)(u:SheetQ ((comV o f).2.2.val v w)): (mkD o M f).2.2.val v w=(comV o f).2.2.val v w:=by
 unfold mkD palCart; simp only [cart_0,cart_1, cart_2,q,e,g,plan_o,zero_mul,mul_zero,add_zero,zero_add]
 rw [(bladeSeal true).1.eq]; rw [SheetQ.binR u, SheetQ.binL u]; exact SheetQ.binL u -- tune
-- exact Taylor on our generator
abbrev ηZ (k: Pal) (i:lotV): yardLot:= Pi.single i k
abbrev pinD (i:slice) (k:Pal):yardLot:= ηZ k (some i,none)-ηZ k neutralK
abbrev spinD(i j:slice) (k:Pal):yardLot:= ηZ k (some i,some j)-ηZ k (some i,none)-(ηZ k (none,some j)-ηZ k neutralK)
private lemma money₀ (i:lotV)(X:Pal): (comV o (ηZ X i)).1=X:=by rw [stamp_f0]; simp [ηZ,Pi.single_apply]
private lemma money₁ (i:lotV)(X:Pal)(x:Views): (comV o (ηZ X i)).2.1 x= Zring o i x • X:=by rw [stamp_f1]; simp [ηZ,Pi.single_apply]
private lemma money₂ (i:lotV)(X:Pal)(x y:Views): (comV o (ηZ X i)).2.2.val x y= (Zring o i x*Zring o i y) • X:=by rw [stamp_f2]; simp [ηZ,Pi.single_apply]
lemma comV_add (i j:yardLot): comV o (i+j)= oAdd (comV o i) (comV o j):=by
 apply Prod.ext _ (Prod.ext (ContinuousLinearMap.ext fun x=>?_) (dual_uni _ _ fun x=>?_)); -- adapt
 · change _=(comV o i).1+(comV o j).1; simp only [stamp_f0,Pi.add_apply,sum_add_distrib]
 · change _=(comV o i).2.1 x+(comV o j).2.1 x; simp only [stamp_f1,Pi.add_apply,smul_add,sum_add_distrib]
 change _=(comV o i).2.2.val x x+(comV o j).2.2.val x x; simp only [stamp_f2,Pi.add_apply,smul_add,sum_add_distrib]
lemma comV_m (i j:yardLot): comV o (i-j) =oSub (comV o i) (comV o j):=by
 unfold oSub; exact (show ∀ {A E:Type}[NormedAddCommGroup A][NormedSpace ℝ A][NormedAddCommGroup E][NormedSpace ℝ E](x y z:Ole E A), x+y=z → x=z-y from (fun {A E} _ _ _ _ x y z h=> eq_sub_of_add_eq (a:=x) (c:=y) h)) (comV o (i-j)) (comV o j) (comV o i) ((comV_add o (i-j) j).symm.trans (congrArg (comV o) (sub_add_cancel i j)))
omit o in
lemma polV_sub (A B:PalOne): CostOle (oSub A B) ≤ CostOle A+CostOle B:= by exact (show ∀ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](x y:Ole E F), CostOle (x-y) ≤ CostOle x+CostOle y from (fun {_ _} _ _ _ _ x y=> norm_sub_le x y)) A B
lemma ore_basis (i:lotV)(P:Pal)(u:SheetQ P): (mkD o M (ηZ P i)).1=P:= (palm₀ o (ηZ P i) ((money₀ o i P).symm ▸ u)).trans (money₀ o i P)
omit o in
lemma lenT(_x:slice)(v:ℝ)(W:Pal): (Complex.I* (v:ℂ)) • ((-Complex.I) • W)= v • W:=by rw [smul_smul,mul_right_comm, mul_neg, Complex.I_mul_I,neg_neg,one_mul,Complex.coe_smul]
lemma ξPoneT (i:slice)(W:Pal)(x:Views)(q:20<n.val): let A:= (-Complex.I) • W
 (comV o (pinD i A)).1=0∧ (comV o (pinD i A)).2.1 x= tips i x • W :=by
 intro A; unfold pinD; rw [comV_m]; change (comV _ _).1-(comV _ _).1=0∧ (comV _ _).2.1 x-(comV _ _).2.1 x=_; rw [money₀,money₀,sub_self,money₁,money₁]
 refine ⟨rfl,?_⟩; simp only [Zring,ξspot_E o (some i,none) q x]; rw [show coinOr none _ =(0:ℝ) from rfl, add_zero, Complex.ofReal_add, mul_add,add_smul]; rw [add_sub_cancel_left]; exact lenT i _ W -- tune
lemma marchD (i j:slice)(x: Views)(p:20<n.val): let f(l):=Zring o l x; let v:=f neutralK; let z:=Complex.I*(tips i x:ℂ); let u:=Complex.I*(tips j x:ℂ)
 f (some i,none)=v+z ∧ f (none,some j)=v+u ∧ f (some i,some j)=v+z+u:=by
 intro f v z u; refine ⟨?_,?_,?_⟩
 · change Complex.I* (ξK o _ x:ℂ)= _; rw [ξspot_E o (some i,none) p x]; simp only [show coinOr none x=(0:ℝ) from rfl, add_zero, Complex.ofReal_add, mul_add]; try rfl
 · change Complex.I* (ξK o _ x:ℂ)= _; rw [ξspot_E o (none,some j) p x]; simp only [show coinOr none x=(0:ℝ) from rfl, add_zero, Complex.ofReal_add,mul_add]; try rfl
 change Complex.I* (ξK o _ x:ℂ)= _; rw [ξspot_E o (some i,some j) p x]; simp only [Complex.ofReal_add,mul_add]; try rfl
set_option maxHeartbeats 65000 in
lemma ξSpino (i j:slice)(W:Pal)(x:Views)(q:20<n.val): let v:= (-1/2:ℂ) • W
 (comV o (spinD i j v)).1=0 ∧ (comV o (spinD i j v)).2.1 x=0 ∧ (comV o (spinD i j v)).2.2.val x x= (tips i x*tips j x) • W:=by
 intro v; obtain ⟨g,l,m⟩:=marchD o i j x q; let Y:lotV→PalOne:=fun j=> comV o (ηZ v j);
 let a:=Y (some i,some j); let b:=Y (some i,none); let c:=Y (none,some j); let d:= Y neutralK
 unfold spinD; rw [comV_m, comV_m,comV_m]; change (a.1-b.1)-(c.1-d.1)=0∧(a.2.1 x-b.2.1 x)-(c.2.1 x-d.2.1 x)=0∧(a.2.2.val x x-b.2.2.val x x)-(c.2.2.val x x-d.2.2.val x x)= _; unfold a b c d Y
 simp only [money₀,money₁,money₂,sub_self]; dsimp only at m g l; rw [m,g,l]; refine ⟨True.intro,?_ ,?_⟩
 · simp only [add_smul]; abel
 rw [← sub_smul,← sub_smul,←sub_smul, show v=(-1/2:ℂ) • W from rfl, smul_smul,← Complex.coe_smul (tips i x*tips j x)]; push_cast; congr 1 -- tune
 let a:ℂ:=↑(tips i x); let b:ℂ:=↑(tips j x); let I:=Complex.I; let c:=Zring o neutralK x
 have he: (c+I*a+I*b)*(c+I*a+I*b)-(c+I*a)*(c+I*a)-((c+I*b)*(c+I*b)-c*c)= (I*I)*(2*a*b):=by ring
 rw [he,show I*I= -1 from Complex.I_mul_I]; unfold a b; ring
end Layout
end Lenten
end YM.CF.TableF
end
