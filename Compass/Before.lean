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
-- Y_support old root g o. extract h via Nonwrapping
variable (Y_ : Support (More N))(sw:Nonwrapping Y_ (Cube.node (Tofu A N o)))
include sw
lemma MatterThin (x:Single N)(p: x∈tolC (markT A Y_)):10*separation x.1.1 o<N.val:=by
 have ht:=mem_filter.mp p; have he:= sw _ ((plex A Y_ _).mp ht.2); change 10*separation (node (g x.1.1)) (node (g o)) < N.val*2 at he -- More double N vs N*2
 rw [ζdist] at he
 have hy: separation (g x.1.1) (g o)=separation x.1.1 o:=AnalyticBridge.VerifiedReset.spin_separation ..
 rw [hy] at he; omega
lemma mask_help (F G:Matrix (Single N) Kt ℂ)(u:∀ x:Single N,10*separation x.1.1 o<N.val→∀ a,F x a=G x a): cutM (tolC (markT A Y_))*F=cutM (tolC (markT A Y_))*G:=by
 ext i j; rw [cutM,Matrix.diagonal_mul,Matrix.diagonal_mul]; split; next t=> rw [u _ (MatterThin A o Y_ sw i t)]
 rw [zero_mul,zero_mul]
include t
lemma mask_R (b:Bool) : let M:=cutM (tolC (markT A Y_)); M*((VS).val*foreQ p (rampF b (g o)))=ea o • (M*(rampF (r.xor b) o*(WS).val)):=by
 intro M; rw [←Matrix.mul_smul]; exact mask_help A o Y_ sw _ _ (fun ⟨⟨x,j⟩,q⟩ u i=> beamD A U p r t o x u ..)
lemma mask_H (b:Bool)(i:Axis) : let M:=cutM (tolC (markT A Y_)); M*((VS).val*foreQ p (spanH b (g o) (A.s.perm i)))=(ea o*ds i) • (M*(spanH (r.xor b) o i*(WS).val)):=by
 intro M; rw [←Matrix.mul_smul]; exact mask_help A o Y_ sw _ _ (fun ⟨⟨x,j⟩,q⟩ u k=> beamH A U p r t o x u j q k b i)
omit t sw
lemma trim_self (i: Support (More N)): (cutM (tolC i))ᴴ=cutM (tolC i):=by ext a b; by_cases h:a=b; subst a; change star ((cutM _) b b)=_; unfold cutM; rw [Matrix.diagonal_apply_eq]; split <;> simp; change star ((cutM _) b a)=_; simp [cutM,h,Ne.symm h]
private lemma flipSq (s:Signed)(i:Axis): ((StressFlux.sign s i:ℂ) :ℂ)*star (StressFlux.sign s i:ℂ) =1:=by unfold StressFlux.sign; cases s.flip i<;>simp
variable {M':Op (Single N)}(Hx:cutM (tolC Y_)*M'*cutM (tolC Y_)=M')
include Hx t sw
lemma basisMate : let W:= sings p VS M';
 (rampF (r.xor false) o)ᴴ * W * rampF (r.xor true) o=sings p WS (mornC (g o) M') ∧
 (∀ i:Axis, (spanH (r.xor false) o i)ᴴ* W * rampF (r.xor true) o=(ds i) • sings p WS (partX (g o) M' (A.s.perm i))) ∧
 (∀ i:Axis, (rampF (r.xor false) o)ᴴ* W * spanH (r.xor true) o i=(ds i) • sings p WS (partY (g o) M' (A.s.perm i))) :=by
 intro W
 let C:=cutM (tolC (markT A Y_)); let L:=cutM (tolC Y_)
 have Hf:(ea o)*star (ea o)=1:=by rw [A.real_payA,A.reflex]
 have He(i:Axis): (ea o*ds i)*star (ea o *ds i)=1:=by
    rw [star_mul,show (ea o*ds i)*(star (ds i)*star (ea o))= (ea o*star (ea o))*(ds i*star (ds i)) from (by ring)]; rw [Hf,flipSq,one_mul]
 have hms :C*(VS).val=(VS).val*L:= maskV A U p Y_
 have h0(b:Bool):= mask_R A U p r t o Y_ sw b
 have h2(b:Bool)(i:Axis):= mask_H A U p r t o Y_ sw b i
 have hS:= sign_cut (N:=N) p (tolC Y_); have s0:=trim_self Y_; have s1:=trim_self (markT A Y_)
 refine ⟨?_,fun i=>?_,fun i=>?_⟩
 · have he:=tableauMate p VS WS _ _ M' _ _ L C _ _ s0 Hf Hf hS s1 hms Hx (h0 false) (h0 true); rw [Hf,one_smul] at he; exact he
 · have he:=tableauMate p VS WS _ _ M' _ _ L C _ _ s0 (He i) Hf hS s1 hms Hx (h2 false i) (h0 true); rw [mul_right_comm (ea o),Hf,one_mul] at he; exact he
 have he:=tableauMate p VS WS _ _ M' _ _ L C _ _ s0 Hf (He i) hS s1 hms Hx (h0 false) (h2 true i); rw [star_mul,mul_left_comm _ _ _,Hf,mul_one, Complex.star_def] at he; rw [Complex.conj_ofReal] at he; exact he
-- reverse variants for θ
end YM.CF.Compass
