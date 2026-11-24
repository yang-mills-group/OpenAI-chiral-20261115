import Compass.Before
import Compass.Gateway
import Compass.Cells
import Compass.Door
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Compass
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Hake Levier Hove
-- adapt Mantel. sign.
-- check base
open Nacre Ione
variable {N:Side}(A:Shape)(U:UNI SpinIdx)(p r: Bool)(t:JetS A.s p r U)
variable (o x:Site N)(h:10*separation x o < N.val)
local notation "WS"=>twoU U p
local notation "VS"=>siteU A p U N
local notation "ea"=>A.payA
-- leave include t? check head
open Matrix Classical Pastry Scree
open scoped Classical
local notation "g"=>Tofu A N
set_option quotPrecheck false
local notation "ds" j:max=> (↑(StressFlux.sign A.s j):ℂ)
variable (Y' : Support (More N))(sw:Nonwrapping Y' (Cube.node (Tofu A N o)))(M:Op (Single N))(v:cutM (tolC Y')*M*cutM (tolC Y')=M)
def axPay (s:Signed)(i:Axis):ℂ:= StressFlux.sign s i
def driftH (s:Signed)(p r:Bool)(U:UNI SpinIdx)(X:Hove.Dome): Hove.Dome := (Thera.jazz r (sings p (twoU U p) X.1), if r then (fun i:Axis=> axPay s i • Thera.jazz r (sings p (twoU U p) (X.2.2 (s.perm i))),fun i:Axis=> axPay s i • Thera.jazz r (sings p (twoU U p) (X.2.1 (s.perm i)))) else (fun i:Axis=> axPay s i • sings p (twoU U p) (X.2.1 (s.perm i)),fun i:Axis=> axPay s i • sings p (twoU U p) (X.2.2 (s.perm i))))
include t
lemma to_r(M:Op Kt)(z:ℂ): sings p WS (culm M)= baseF (r.xor false)* sings p WS M* baseF (r.xor true):=by
 unfold culm; rw [singT,win_m,win_m,map_mul,map_mul,←singT,basePull A U p r t false,←singT,←singT,basePull A U p r t true]
lemma star_mul_R (z:ℂ)(M:Op Kt): culm (z • M)=z • culm M:=by unfold culm; rw [_root_.Matrix.mul_smul,_root_.Matrix.smul_mul]
include sw v
lemma dome_P : jetsL o (Thera.jazz r (sings p VS M))= driftH A.s p r U (jetsL (g o) M) :=by
 cases r; swap
 · obtain ⟨e,f,u⟩:= basisMate A U p true t o Y' sw v
   set V':=sings p VS M
   have hrev (X Y: Matrix (Single N) Kt ℂ)(P:Op Kt)(h:Xᴴ*V'*Y=P): Yᴴ * Thera.jazz true V' * X = - star P:=by unfold Thera.jazz; rw [if_pos rfl,_root_.Matrix.mul_neg,_root_.Matrix.neg_mul, ←h]; congr 1; change Yᴴ*V'ᴴ*X=(Xᴴ*V'*Y)ᴴ; rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
   have e': mornC o (Thera.jazz true V') = Thera.jazz true (sings p WS (mornC (g o) M)):=hrev _ _ _ e
   let k:= fun i:Axis=> axPay A.s i
   have Lv(W:Op Kt)(i:Axis): culm (-star (k i •sings p WS W))= k i • Thera.jazz true (sings p WS (culm W)):=by
      unfold Thera.jazz; rw [to_r A U p true t W 0, if_pos rfl,star_mul, star_mul]; change culm _=(k i • (-((baseF false)ᴴ * ((sings _ _ W)ᴴ * (baseF true)ᴴ)))); rw [φ_a,φ_a]; have hK:star (k i)=k i:=by unfold k axPay; simp
      rw [star_smul,hK]; unfold culm; rw [_root_.Matrix.mul_neg, _root_.Matrix.neg_mul,_root_.Matrix.mul_smul,_root_.Matrix.smul_mul,smul_neg]; rw [_root_.Matrix.mul_assoc]; rfl
   refine Prod.ext e' (Prod.ext (funext fun i=>?_) (funext fun i=>?_))
   · change culm (partX o (Thera.jazz true V') i)=k i • _; rw [partX,hrev (rampF true o) (spanH false o i) _ (u i)]; exact Lv _ i -- e(u i):X=rampF true, Y span false, yes.
   change culm (partY o (Thera.jazz true V') _)=k _ • _; rw [partY,hrev (spanH true o _) (rampF false o) _ (f _)]; exact Lv ..
 obtain ⟨he,f,u⟩:= basisMate A U p false t o Y' sw v
 refine Prod.ext he (Prod.ext (funext fun i=>?_) (funext fun i=>?_))
 all_goals
   simp only [Bool.false_xor] at f u
 all_goals simp only [jetsL,driftH,Thera.jazz,Bool.false_xor,Bool.false_eq_true, ↓reduceIte] ; change culm _=axPay _ i • sings p WS (culm _)
 · rw [partX,f i,star_mul_R A U p false t, to_r A U p false t _ 1]; rfl
 rw [partY,u _,star_mul_R A U p false t,to_r A U p false t _ 1]; rfl
end YM.CF.Compass
