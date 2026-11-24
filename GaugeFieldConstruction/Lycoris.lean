import GaugeFieldConstruction.Pisane
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 120000
namespace YM.Gleam.Guide.Pitcher
open Coins CF CF.Fock CF.Fock.Flux Pacts CF.XGarden.MastTin.ArtCart.Violets
open Filter MeasureTheory Matrix
open scoped Classical Topology InnerProductSpace
variable {N: Lattice.Side}{I:Type} [LinearOrder I][Fintype I]{P A B: Op I}{u:Wave I}
variable {O:Type}[NormedAddCommGroup O][InnerProductSpace ℝ O][MeasurableSpace O][BorelSpace O][FiniteDimensional ℝ O]
variable {X Y Z: O→ FC I}
lemma two_E (S:Solid I O X)(T:Solid I O Y)(g: Panel P A B u (1:O→ FC I)=1) : let a:=Panel P A B u X; let b:=Panel P A B u Y; Panel P A B u ((X-a • 1)*(Y-b • 1))=Panel P A B u (X*Y)- a*b:=by
 intro a b; let u':= (1:O→FC I); have h:Solid I O u':=Solid.major _
 have ht (V' W:O→FC I)(z:ℂ):(z • V')*W=z • (V'*W):=Algebra.smul_mul_assoc .. -- OpCStar local instance
 have hu (V' W:O→FC I)(z:ℂ): V'*(z • W)= z • (V'* W):=Algebra.mul_smul_comm ..
 simp (config:={maxDischargeDepth:=10}) only [sub_mul,mul_sub,ht,hu,mul_one,one_mul,spine_d,S,T,Solid.muls,Solid.minusS,Solid.scaler, (show Solid I O (1:O→FC I) from h),spine_s,g,mul_one]
 unfold a b; ring
lemma thr_E (S:Solid I O X)(T:Solid I O Y)(R:Solid I O Z)(g: Panel P A B u (1:O→FC I)=1) : let a:=Panel P A B u X; let b:=Panel P A B u Y; let c:=Panel P A B u Z; Panel P A B u ((X-a • 1)*(Y-b • 1)*(Z-c • 1))=Panel P A B u (X*Y*Z)- Panel P A B u (X*Y)*c-Panel P A B u (X*Z)*b-Panel P A B u (Y*Z)*a+2*a*b*c:=by
 intro a b c; have h:Solid I O (1:O→FC I):=Solid.major _
 have ht (V' W:O→FC I)(z:ℂ):(z • V')*W=z • (V'*W):=Algebra.smul_mul_assoc ..
 have hu (V' W:O→FC I)(z:ℂ): V'*(z • W)= z • (V'* W):=Algebra.mul_smul_comm ..
 simp (config:={maxDischargeDepth:=10}) only [sub_mul,mul_sub,ht,hu,mul_one,one_mul,spine_d,S,T,R,Solid.muls,Solid.minusS,Solid.scaler,h,spine_s,g,mul_one]
 unfold a b c; ring
end YM.Gleam.Guide.Pitcher
end
