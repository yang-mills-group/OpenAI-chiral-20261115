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
include t
local notation "WS"=>twoU U p
local notation "VS"=>siteU A p U N
local notation "ea"=>A.payA
local notation "da"=>StressFlux.sign
lemma dawn_s (b:Bool)(a:Axis)(y:Cover): sings p WS (moonB b (A.s.perm a) (A.s.act y))=(↑(da A.s a):ℂ) • moonB (r.xor b) a y:=by
 unfold moonB; rw [singT,win_a,map_add,←singT,←singT,scaleT,basePull A U p r t b,dit_pull A U p r t b a,seal_I,space_T, mul_smul,←smul_add]
lemma seam_k {x:Site N} (j:SpinIdx)(k:Slot)(a:Kt) {G:Matrix (Single N) Kt ℂ}(M Y:Op Kt){b:ℂ}{z:ℂ}(hg:∀ i:Kt,G ((Tofu A N x,i.1),i.2) a = b • M i a)
    (u:sings p WS M= Y)
    (hp:(ea x)*cSignX p b=z):
    ((VS).val * foreQ p G) ((x,j),k) a = z * (Y*(WS).val) (j,k) a:=by
 rw [Matrix.mul_apply, sum_entry]; have he:(WS).val * windX p M=Y * (WS).val:=by rw [singT p,twist_formula] at u; rw [←u,mul_assoc,(WS).property.1,mul_one]
 rw [←he,Matrix.mul_apply,mul_sum]; apply sum_congr rfl; intro i _; unfold foreQ; simp only [Matrix.of_apply,hg,smul_eq_mul,sealG]; rw [show Scroll.cSignX p (M i a)=windX p M i a from by cases p<;>rfl]
 all_goals change (ea x*_*(_*_))=_*(_*_)
 all_goals rw [←hp]; first|rfl|ring
-- mask at each endpoint.Site
include h
lemma beamD (j:SpinIdx)(k:Slot)(i:Kt)(b:Bool):
     ((VS).val* foreQ p (rampF b (Tofu A N o))) ((x,j),k) i=(ea o •(rampF (r.xor b) o * (WS).val)) ((x,j),k) i:=by
 let y:=(((x,j),k):Single N); let f:=Lattice.lift (x-o); let v:=Rush.wind o f; let g:= Rush.wind (Tofu A N o) (Lattice.lift (Tofu A N x-Tofu A N o)); have he:g*A.payA x=A.payA o*v:=east_wind A o x h
 have hh:cSignX p g=g:=by cases p; rfl; exact fee_real _
 rw [seam_k A U p r t j k i (baseF b) (baseF (r.xor b)) (b:=g) (z:=A.payA o*v) (fun _=>rfl) (basePull A U p r t b) (by rw [hh,mul_comm]; exact he),Matrix.smul_apply]
 -- Y times WS square vs ramp WS
 simp only [Matrix.mul_apply,smul_eq_mul, Finset.mul_sum,rampF,Matrix.of_apply,Hove.portB,mul_assoc,show ζw o (((x,j),k):Single N)=v from rfl]
lemma beamH (j:SpinIdx)(k:Slot)(i:Kt)(b:Bool)(a:Axis):
 ((VS).val* foreQ p (spanH b (Tofu A N o) (A.s.perm a))) ((x,j),k) i=((ea o*(↑(da A.s a):ℂ)) •(spanH (r.xor b) o a * (WS).val)) ((x,j),k) i:=by -- precedence? ea o * ↑δ • ..
 let y:=(((x,j),k):Single N); let f:=Lattice.lift (x-o); let v:=Rush.wind o f; let g:= Rush.wind (Tofu A N o) (Lattice.lift (Tofu A N x-Tofu A N o)); have he:g*A.payA x=A.payA o*v:=east_wind A o x h
 have hh:cSignX p g=g:=by cases p; rfl; exact fee_real _
 let Q:= (moonB b (A.s.perm a) (A.s.act f)); let Y:= (moonB (r.xor b) a f)
 let c:ℂ:= (da A.s a)
 rw [seam_k A U p r t j k i Q (c • Y) (b:=g) (z:=A.payA o*v) (fun i=> by unfold spanH; unfold ζw Hove.portB ox Q g; simp only [Matrix.of_apply,smul_eq_mul, show Lattice.lift (Tofu A N x-Tofu A N o) = A.s.act f from twist_lift A o x h]) (dawn_s A U p r t b a f) (by rw [hh,mul_comm]; exact he),Matrix.smul_apply]
 simp only [Matrix.smul_mul,Matrix.smul_apply,Matrix.mul_apply,Finset.mul_sum,spanH,Hove.portB,Matrix.of_apply, smul_eq_mul, show ζw o (((x,j),k):Single N)=v from rfl, show ox o (((x,j),k):Single N)=f from rfl]; unfold Y c; apply sum_congr rfl; intro i _; ring
end YM.CF.Compass
