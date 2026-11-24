import GaugeFieldConstruction.Larwood
import YM.CF.Moto.Road
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 260000
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
namespace Loden
open Layout HushP ModuleB
variable (M:Tulip.Male)(b:Bool)(h:ℝ)(o:Skye.Seat n)(A:Pal)(L:Op (Single n))
structure Soot(A:Pal)(b:Bool):Prop where
 l:baseF b*A=A
 r:A*baseF b=A
def Mott:Prop:=∀ i j:Site n, Soot (matPH L i j) b
variable {A b L h}
lemma snuff(t:Mott b L)(i:Views): Soot (streamF o L h i) b:=by rw [streamS]; constructor <;> simp only [Matrix.sum_mul,Matrix.mul_sum, Matrix.smul_mul,Matrix.mul_smul,(t _ _).l,(t _ _).r]
lemma soot_K {f:Views→Pal}{P:PalOne}(p:AptK f P)(u:∀ i,Soot (f i) b)(q:∀ i,∀ g:SU.E, Commute (f i) (KinX g)): Soot P.1 b ∧(∀ g:SU.E, Commute P.1 (KinX g))∧∀ i:Views,Soot (P.2.1 i) b∧∀ g:SU.E, Commute (P.2.1 i) (KinX g):=by
 rw [← p.point]; refine ⟨u _,q _,fun x=>?_⟩; let l:=ContinuousLinearMap.mul ℝ Pal; let W:=P.2.1 x
 have hv(L:Pal→L[ℝ] Pal)(w:∀ i:Views,L (f i)=f i):L W=W:=congrArg (fun k:PalOne=> k.2.1 x) (fromJ p L w)
 refine ⟨⟨hv (l _) (fun i=>(u i).l), hv (l.flip _) (fun i=>(u i).r)⟩,fun g=> sub_eq_zero.mp ?_⟩
 let L:=l.flip (KinX g)-l (KinX g); exact congrArg (fun k:PalOne=> k.2.1 x) (fromZ p L (fun i=> sub_eq_zero.mpr (q i g).eq))
abbrev liner(x y w:Bool)(M: Male):PalOne:= palCart (bladeL y) (palCart (wheelP M x) (bladeL w))
lemma lines_0(x y z:Bool): (liner x y z M).1= baseF y * baseF x*baseF z:=by change _*((wheelP M x).1* _)=_; rw [plan_o,←mul_assoc]
lemma lines_1(x y z:Bool)(i:Views): (liner x y z M).2.1 i=baseF y* (wheelP M x).2.1 i*baseF z:=by change 0* _+baseF y*(_*baseF z+(wheelP M x).1*0)=_; rw [zero_mul,zero_add,mul_zero,add_zero,←mul_assoc]; rfl
lemma lines_2(x y z:Bool)(i j:Views): (liner x y z M).2.2.val i j=baseF y*(wheelP M x).2.2.val i j*baseF z:=by unfold liner palCart; rw [cart_2,cart_2]; change 0* _+baseF y*(_*baseF z+ _*0 + (_* 0+_*0))+(0*_+0*_)=_; simp only [mul_zero,zero_mul, add_zero,zero_add,mul_assoc]
lemma wshape(t:Mott b L): winJ o M h L=palCart (liner false false b M) (palCart (markJet o L h) (liner true b true M)):=by
 let X(a b c: Bool)(v:Views):= baseF b*(fellP M a v*baseF c); have hx(a b c): AptK (X a b c) (liner a b c M):=cart_K (AptK.const _) (cart_K (plankK ..) (AptK.const _))
 let f(v):= streamF o L h v; have hv:AptK (fun i=> X false false b i* (f i* X true b true i)) (palCart (liner false false b M) (palCart (markJet o L h) (liner true b true M))):= cart_K (hx ..) (cart_K (K_pays o L h) (hx ..)); symm; apply (hv.equal ?_).unique (tab M L)
 refine Eventually.of_forall fun i=>?_ ; unfold TabX; let B:=baseF b; let a:=baseF false; let c:=baseF true; let x:=fellP M false i; let y:=fellP M true i; let H:=snuff (h:=h) o t i; change a*(x*B)*(f i*(B*(y*c)))=a*(x*(f i*(y*c))); rw [←mul_assoc (f i),show f i*B=f i from H.r,mul_assoc,mul_assoc, ←mul_assoc B,show B*f i=f i from H.l]
abbrev LtV(M:Male):= liner false false true M
abbrev LtU(M:Male):= liner false false false M
abbrev RtV(M:Male):= liner true false true M
abbrev RtU(M:Male):= liner true true true M
lemma linerL(t:Mott true L)(v:Views):let U:=winJ o M h L; let Z:=markJet o L h; let C:=-uroS v.1
 U.1=0∧ U.2.1 v=C*Z.1∧ U.2.2.val v v=C*Z.2.1 v+C*Z.2.1 v:=by
 intro U Z C; have h₀: (LtV M).1=0:=by rw [LtV,lines_0,(bladeSeal false).1.eq, capital_o]
 have ht: (RtU M).1=baseF true:=by rw [RtU,lines_0,(bladeSeal true).1.eq,(bladeSeal true).1.eq]
 have hz:(LtV M).2.2.val v v=0:=by rw [LtV,lines_2]; exact Capital v.1 M false v.1
 have ha:(LtV M).2.1 v=C:=by rw [LtV,lines_1]; change high*(pilotS M false).2.1 v.1*low=_; rw [pins_Z,mul_neg,neg_mul]
 have he:(RtU M).2.1 v=0:=by rw [RtU,lines_1]; exact Star_p v.2 M true
 let g:= (ContinuousLinearMap.mul ℝ Pal).flip low
 have hX:postF Z g=Z:= fromJ (K_pays ..) g fun i=>(snuff (h:=h) o t i).r
 have hv: Z.1*baseF true=Z.1:=congrArg Prod.fst hX; have hZ: Z.2.1 v*baseF true=Z.2.1 v:=congrArg (fun k:PalOne=> k.2.1 v) hX
 rw [show U= _ from wshape (h:=h) M o t]; let M':=palCart Z (RtU M); change (palCart (LtV M) M').1=0∧(palCart (LtV M) M').2.1 v=_∧(palCart (LtV M) M').2.2.val v v=_
 have hh:M'.1=Z.1:=by change Z.1*(RtU M).1 = _; rw [ht,hv]
 have hx:M'.2.1 v=Z.2.1 v:=by change Z.2.1 v*(RtU M).1+Z.1*(RtU M).2.1 v=_; rw [ht,he,hZ,mul_zero,add_zero]
 unfold palCart; simp only [cart_0,cart_1,cart_2, hh,h₀,hx,hz,ha,mul_zero,zero_mul,zero_add,add_zero,and_self]
lemma linerR(t:Mott false L)(v:Views):let U:=winJ o M h L; let Z:= markJet o L h; let C:=uroS v.2
 U.1=0∧ U.2.1 v=Z.1*C ∧ U.2.2.val v v=Z.2.1 v*C +Z.2.1 v*C:=by
 intro U Z C; have h₀:(RtV M).1=0:=by rw [RtV,lines_0, capital_o,zero_mul]
 have ht:(LtU M).1=baseF false:=by rw [LtU,lines_0,(bladeSeal false).1.eq,(bladeSeal false).1.eq]
 have hz:(RtV M).2.2.val v v=0:=by rw [RtV,lines_2]; exact Capital v.2 M true v.2
 have ha:(RtV M).2.1 v=C:=by rw [RtV,lines_1]; change high*(pilotS M true).2.1 v.2*low=_; rw [pins_A]; try rfl
 let g:= ContinuousLinearMap.mul ℝ Pal high
 have hX:postF Z g=Z:=fromJ (K_pays ..) g fun i=>(snuff (h:=h) o t i).l
 have hv:baseF false*Z.1=Z.1:=congrArg Prod.fst hX; have hZ:baseF false* Z.2.1 v= Z.2.1 v:= congrArg (fun z:PalOne=> z.2.1 v) hX
 have hx:(LtU M).2.1 v=0:=by rw [LtU,lines_1]; exact Star_p v.1 M false
 rw [show U=_ from wshape (h:=h) M o t]; let P:= palCart Z (RtV M); change (palCart (LtU M) P).1=0∧(palCart (LtU M) P).2.1 v=_∧ (palCart (LtU M) P).2.2.val v v=_
 unfold P palCart; simp only [cart_0,cart_1,cart_2,h₀,hx,ha,hz,ht,zero_mul,mul_zero,zero_add,add_zero,mul_add,←mul_assoc,hv,hZ,and_self]
lemma S0_s(t:Mott b L): sectorJ L M o h=0:=by
 rw [seat_b]; let P:= snuff (h:=h) o t (0:Views); let X:=streamF o L h 0; change high*X* low=0
 cases b
 · have hp:= snuff (h:=h) o t (0:Views); rw [show high*X=X from hp.l, ← (show X*high=X from hp.r), mul_assoc,capital_o,mul_zero] -- Capital_o head high*low no binder
 have hp:= snuff (h:=h) o t (0:Views); rw [← (show low*X=X from hp.l),←mul_assoc high,capital_o,zero_mul,zero_mul]
lemma sill(X:InkD n)(u: PressB p (Zhub o) X h c)(v:∀ i,Mott b (orbitPH (X i))): landA M o X p h=0:=by
 apply ContinuousLinearMap.ext; intro i; let V(t:ℝ):=increment 1 (t • gateC o p.threshold i); have hp:=landR M (o:=o) u i; let F(t:ℝ):= sectorJ (orbitPH (X (V t))) M o h; have hx:F=fun _=>0:=funext fun i=> S0_s (h:=h) M o (v _); exact hp.unique (show HasDerivAt F 0 0 from hx.symm ▸ hasDerivAt_const 0 _)
end Loden
end Lenten
end YM.CF.TableF
end
