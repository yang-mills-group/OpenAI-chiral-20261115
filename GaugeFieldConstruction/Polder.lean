import GaugeFieldConstruction.Pavan
import GaugeFieldConstruction.Kiwi
import GaugeFieldConstruction.Kuril
/- ordered clock output. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Gleam.Guide
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian CF
open Fineness Module Regis Regis.Head ProbabilityTheory Hood CF.Fock CF.Fock.Flux Pacts Prims
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.L2Operator NNReal InnerProductSpace
attribute [local instance] opCStarAlgebra
namespace Pitcher
variable {I:Type*} [LinearOrder I][Fintype I]{P E A B:Op I}{u:Wave I}
variable {F:Type*} [NormedAddCommGroup F][InnerProductSpace ℝ F][MeasurableSpace F][BorelSpace F][FiniteDimensional ℝ F]
namespace Coins
variable (p:Valve P E A B)(v:IsStarProjection P)(h:Sea P u) {S:Finset I} (i j k m n w:F)(a b c:Seated S)
-- expose first two terms point order
abbrev P2Γ {T:Type*} (f:T→T→ℂ) (i j k m:T):= f i k*f j m+f i m*f j k
def P3Γ {T:Type*}(f:T→T→ℂ) (i j k m n w:T):= f i k*P2Γ (fun a b=> f a b) n w j m + f i m*P2Γ f n w j k+ f i n*P2Γ f k m j w + f i w*P2Γ f k m j n -- these use perm, need orientation for asym & proximity. prefer explicit all oriented to k≥i
abbrev T2Γ {T:Type*}(f:T→T→ℂ) (i j k m n w:T) := f i k*(f j n*f m w+ f j w*f m n) + f i m*(f j n*f k w+f j w*f k n)+f i n*(f j k*f m w+f j m*f k w)+ f i w*(f j k*f m n+f j m*f k n) -- leg pairing symmetric
lemma coupleZ (x y z:F→FC I) : x*(y-z)=x*y-x*z := mul_sub x y z
lemma coupeV (x y z:F→FC I) : (x-y)*z=x*z-y*z:=sub_mul ..
lemma matricesM (v:ℂ) (g h:FC I): g*(v • h)=v • (g*h):=Matrix.mul_smul ..
lemma matMtx (v:ℂ)(g h:FC I):(v • g)*h=v • (g*h):=Matrix.smul_mul ..
-- abbreviation paula is def reducible, these smul-mul lemmas don't rewrite sub.
include p v h
-- expand distributivity rfl
set_option quotPrecheck false
-- `repeat' rw` difficult at_Consum. use simp conditional `[Solid.raw]` via forward attribute? declare via wrappers.
lemma wust_solid (L:List F)(u:FC I):Solid I F (Wust L u):=.raw .. -- auto captures p v h omit needed.
macro "copper" p:term:max v:term:max h:term:max : tactic => `(tactic| (
    simp (config := {maxDischargeDepth:=10}) only [coupleZ,coupeV, Wust_K, List.nil_append, List.cons_append, matMtx,matricesM,one_mul,mul_one, spine_d, wust_solid $p $v $h,Solid.minusS,Solid.raw, emit,map_smul, smul_eq_mul,cΩ $p $v $h, trebleR $p $v $h,doubleR $p $v $h, cancelR $p $v $h,lockW,Prims.charm,χØ, papaya]
    push_cast
    try ring))
lemma coatGn : Panel P A B u (Gn i j)=0:=by unfold Gn; copper p v h
lemma coatFn : Panel P A B u (FN F P A B a)=0:=by unfold FN; copper p v h
lemma coatXn : Panel P A B u (XN P A B i a)=0:=by unfold XN; copper p v h
lemma AversGG : Panel P A B u (Gn i j*Gn k m)= P2Γ papaya i j k m:=by unfold Gn P2Γ; copper p v h
lemma AversGF : Panel P A B u (Gn i j*FN F P A B b)= 0:=by unfold Gn FN; copper p v h
lemma AversGX : Panel P A B u (Gn i j*XN P A B k b)= 0:=by unfold Gn XN; copper p v h
lemma AversFG : Panel P A B u (FN F P A B a*Gn k m)= 0:=by unfold Gn FN; copper p v h
lemma AversFF : Panel P A B u (FN F P A B a*FN F P A B b)= - (QueenP P A B a b * QueenP P A B b a):=by unfold FN; copper p v h
lemma AversFX : Panel P A B u (FN F P A B a*XN P A B k b)= 0:=by unfold FN XN; copper p v h
lemma AversXG : Panel P A B u (XN P A B i a*Gn k m)= 0:=by unfold Gn XN; copper p v h
lemma AversXF : Panel P A B u (XN P A B i a*FN F P A B b)= 0:=by unfold FN XN; copper p v h
lemma AversXX : Panel P A B u (XN P A B i a*XN P A B k b)= - (QueenP P A B a b * QueenP P A B b a) * papaya i k:=by unfold XN; copper p v h
lemma AversGGG : Panel P A B u (Gn i j*Gn k m*Gn n w)= T2Γ papaya i j k m n w:=by unfold Gn T2Γ; copper p v h
lemma AversGGF : Panel P A B u (Gn i j*Gn k m*FN F P A B c)= 0:=by unfold Gn FN; copper p v h
lemma AversGGX : Panel P A B u (Gn i j*Gn k m*XN P A B n c)= 0:=by unfold Gn XN; copper p v h
lemma AversGFG : Panel P A B u (Gn i j*FN F P A B b*Gn n w)= 0:=by unfold Gn FN; copper p v h
lemma AversGFF : Panel P A B u (Gn i j*FN F P A B b*FN F P A B c)= 0:=by unfold Gn FN; copper p v h
lemma AversGFX : Panel P A B u (Gn i j*FN F P A B b*XN P A B n c)= 0:=by unfold Gn FN XN; copper p v h
lemma AversGXG : Panel P A B u (Gn i j*XN P A B k b*Gn n w)= 0:=by unfold Gn XN; copper p v h
lemma AversGXF : Panel P A B u (Gn i j*XN P A B k b*FN F P A B c)= 0:=by unfold Gn FN XN; copper p v h
lemma AversGXX : Panel P A B u (Gn i j*XN P A B k b*XN P A B n c)= -(QueenP P A B b c*QueenP P A B c b)*P2Γ papaya i j k n:=by unfold Gn XN P2Γ; copper p v h
lemma AversFGG : Panel P A B u (FN F P A B a*Gn k m*Gn n w)= 0:=by unfold Gn FN; copper p v h
lemma AversFGF : Panel P A B u (FN F P A B a*Gn k m*FN F P A B c)= 0:=by unfold Gn FN; copper p v h
lemma AversFGX : Panel P A B u (FN F P A B a*Gn k m*XN P A B n c)= 0:=by unfold Gn FN XN; copper p v h
lemma AversFFG : Panel P A B u (FN F P A B a*FN F P A B b*Gn n w)= 0:=by unfold Gn FN; copper p v h
lemma AversFFF : Panel P A B u (FN F P A B a*FN F P A B b*FN F P A B c)= QueenP P A B a b*QueenP P A B b c*QueenP P A B c a+QueenP P A B a c*QueenP P A B c b*QueenP P A B b a:=by unfold FN; copper p v h
lemma AversFFX : Panel P A B u (FN F P A B a*FN F P A B b*XN P A B n c)= 0:=by unfold FN XN; copper p v h
lemma AversFXG : Panel P A B u (FN F P A B a*XN P A B k b*Gn n w)= 0:=by unfold Gn FN XN; copper p v h
lemma AversFXF : Panel P A B u (FN F P A B a*XN P A B k b*FN F P A B c)= 0:=by unfold FN XN; copper p v h
lemma AversFXX : Panel P A B u (FN F P A B a*XN P A B k b*XN P A B n c)= (QueenP P A B a b*QueenP P A B b c*QueenP P A B c a+QueenP P A B a c*QueenP P A B c b*QueenP P A B b a)*papaya k n:=by unfold FN XN; copper p v h
end Coins
end Pitcher
end YM.Gleam.Guide
end
