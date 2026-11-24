import Bay.D.Dular
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Resonance Brecht Circuit

variable {I J:Type*}[Fintype I][Fintype J]
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
local notation "V"=>stdGaussian E
variable (K:ℝ) (A:Icey I) (y:I→E)

def scrip (x:E):ℂ:=splash A (fun i=>pur K (spanX (y i) x))
private lemma scrip_eq(x:E):scrip K A y x=dip A (fun i j=> Complex.ofReal (dum K (y i) (y j) x)):=dip_bind A _
lemma scrip_cream(x:E):scrip K (creamM A) y x=star (scrip K A y x):=by
 rw[scrip_eq,scrip_eq,←cream_dip];congr 1;funext i j;simp[creamM]
lemma scrip_cont:Continuous (scrip K A y):=by
 have h := (pur_smooth K).continuous
 unfold scrip splash swirl spanX;fun_prop

abbrev wick(i j:I):=ivoryL (y i) (y j)
variable {A K y} {s:Finset I}{b f:ℝ}
lemma mink (p:Rake s f A)(g:0<K)(u:∀i,‖y i‖≤b):
    ‖(∫ x,scrip K A y x∂V)- dip A (wick y)‖ ≤ f * (roughW b/K^2):=by
 simp_rw[scrip_eq]
 rw[dip_int]
 · exact dip_le p (by unfold roughW;positivity) (fun i _ j _=>toot _ g (u i) (u j))
 exact fun _ _ =>(dum_go _ _ g).accepted.ofReal

/-- both Wick crossings. -/
def passes(F:I→J→ℂ)(i j:I)(k l:J):=F i k*F j l +F i l*F j k
def hashes(y:I→E)(z:J→E)(i:I)(j:J):= ivoryL (y i) (z j)
lemma sable {B:Icey J}{z:J→E}{t:Finset J}{e:ℝ}
   (p:Rake s f A)(q:Rake t e B)(g:0<K)
   (u:∀i,‖y i‖≤b)(w:∀k,‖z k‖≤b):
   ‖(∫ x,scrip K A y x*scrip K B z x∂V) -
     (dip A (wick y)*dip B (wick z)+dips A B (passes (hashes y z)))‖≤f*(e*(roughW b/K^2)):=by
 simp_rw[scrip_eq,←dips_prod]
 simp_rw [←dips_plus A B]
 rw[dips_int]
 · exact dips_le p q (by unfold roughW; positivity) (fun _ _ _ _ _ _ _ _=>toots _ _ _ _ g (u _) (u _) (w _) (w _))
 intro i j k l
 have h:= ((dum_go (y i) (y j) g).times (dum_go (z k) (z l) g)).accepted.ofReal (𝕜:=ℂ)
 simp_rw[←Complex.ofReal_mul]; exact h

lemma wick_fee(p:Rake s f A) (t:0≤b)(u:∀i,‖y i‖≤b):
 ‖dip A (wick y)‖≤f*b^2:=by
 apply dip_fee p _ (sq_nonneg _)
 intro i _ j _
 rw[wick,ivoryL,Complex.norm_real,sq]
 exact (norm_inner_le_norm ..).trans (mul_le_mul (u i) (u j) (by positivity) t)
lemma passes_smul{B:Icey J}(F:I→J→ℂ)(c:ℂ):
    dips A B (passes (c • F)) = c^2*dips A B (passes F):=by
 rw[←dips_times]
 congr 1; funext i j k l; simp [passes]; ring
-- if uniformly ‖F-G‖≤d ≤1, ‖G‖≤u, etc.
lemma passes_fee {B:Icey J}{t:Finset J}{e g d:ℝ}
     (p:Rake s f A)(q:Rake t e B)(u:0≤g)(v:0≤d)
     {F G:I→J→ℂ}
     (h:∀i∈s,∀k∈t,‖F i k-G i k‖≤d)
     (c:∀i∈s,∀k∈t,‖G i k‖≤g):
     ‖dips A B (passes F)-dips A B (passes G)‖ ≤ f*(e*(4*d*(g+d))):=by
 apply dips_le p q (by positivity)
 have e(i j k l)(a:i∈s)(b:j∈s)(m:k∈t)(n:l∈t): ‖F i k*F j l-G i k*G j l‖≤2*d*(g+d):=by

   let F1 := F i k
   let F2 := F j l
   let G1 := G i k
   let G2 := G j l
   change ‖F1*F2-G1*G2‖≤_
   rw[show F1*F2-G1*G2=(F1-G1)*G2 + F1*(F2-G2) from by ring]
   apply (norm_add_le ..).trans
   rw[norm_mul,norm_mul]
   have w:‖F1‖≤g+d:=(norm_le_norm_add_norm_sub _ _).trans (add_le_add (c i a k m) ((norm_sub_rev ..).trans_le (h i a k m)))
   refine (add_le_add 
            (mul_le_mul (h i a k m) ((c j b l n).trans (le_add_of_nonneg_right v)) (norm_nonneg _) v)
            (mul_le_mul w (h j b l n) (by positivity) (by positivity))).trans_eq ?_
   ring
 intros i a j b k m l n
 unfold passes; rw[add_sub_add_comm]
 refine ((norm_add_le ..).trans (add_le_add (e i j k l a b m n)
     (e i j l k a b n m))).trans_eq ?_
 ring

end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.passes_fee
