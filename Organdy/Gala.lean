import Organdy.Spray
import Organdy.Cauliflower
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset
open scoped NNReal

open Regis Head Lattice Precision Wilson Pressure Work.F03 Exterior
open Larva (Chip Tint dot blush stains decree wet_iff)
variable {n N:Side}
local notation "G" => SU.group

open RG Gleam ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
variable {M:Bed}{Z:PathData G}{q: Clip}{ρ θ v a η C:ℝ}


-- collections of copies (chess supports assume l+2 around anchors, maybe enlarge more)
variable {J:Type*}
structure Ballroom (J:Type*) (n:Side) where
 path:J→Signed
 post:J→Site n
namespace Ballroom
variable (R:Ballroom J n)
def back(y:Site n)(j:J):Site n:=affine (R.path j) (R.post j) y
def area (l:ℕ)(y:Site n)(j:J):Support n:=
 halo (l+2) {R.post j,R.back y j}
def Space (l:ℕ)(y:Site n):Prop:=
 Pairwise (Disjoint on R.area l y)
end Ballroom

-- contributions of arbitrary site region h
abbrev GFace (n:Side) := Cell n×Bool×SU.group.ColorIndex
def hall (h:Support n):Finset (GFace n):=univ.filter (fun i=>i.1.1∈h)
def volt (h:Support n)(x:Altar G n):ℝ:= Real.sqrt (∑i∈hall h,x i^2)
lemma volt_non(h:Support n)(x:Altar G n):0≤volt h x:=Real.sqrt_nonneg _
lemma volt_energy(h:Support n)(x:Altar G n):
 (volt h x)^2=∑i∈hall h,x i^2:=Real.sq_sqrt (by positivity)
lemma hall_iff {h:Support n}{i:GFace n}:i∈ hall h ↔ i.1.1∈h:=by simp [hall]

lemma hall_exit {h g:Support n}(a:Disjoint h g):Disjoint (hall h) (hall g):=
 Finset.disjoint_left.mpr fun _ b c=>Finset.disjoint_left.mp a (hall_iff.mp b) (hall_iff.mp c)

lemma volt_take {h:Support n}{i:GFace n}(p:i.1.1∈h)(x:Altar G n): |x i|≤volt h x:=by
 rw [←sq_le_sq₀ (abs_nonneg _) (volt_non ..),sq_abs,volt_energy]
 exact single_le_sum (f:=fun i=>x i^2) (fun _ _=>sq_nonneg _) (hall_iff.mpr p)
variable [Fintype J]
lemma volts (f:J→Support n)(h:Pairwise (Disjoint on f))
 (x:Altar G n): ∑j,(volt (f j) x)^2 ≤ ‖x‖^2:=by
 simp_rw [EuclideanSpace.real_norm_sq_eq,volt_energy]
 have w:(↑(univ:Finset J):Set J).PairwiseDisjoint (fun j=>hall (f j)):=
    fun i _ j _ y=>hall_exit (h y)
 rw [← sum_biUnion w]
 exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>sq_nonneg _)
lemma volt_budget (f:J→Support n)(h:Pairwise (Disjoint on f))
 (x:Altar G n): ∑j,volt (f j) x ≤ Real.sqrt (Fintype.card J) * ‖x‖:=by
 have a:=sum_mul_sq_le_sq_mul_sq univ (fun _:J=>(1:ℝ)) (fun j=>volt (f j) x)
 simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,card_univ] at a
 apply le_of_sq_le_sq _ (by positivity)
 rw [mul_pow,Real.sq_sqrt (by positivity)]

 exact a.trans (mul_le_mul_of_nonneg_left (volts f h _) (by positivity))

variable {k c:ℝ}{s:Signed}{b:Site n}{y:Support n}{l:ℕ}
lemma kiln_pos :0 ≤ kilnBound q:=by unfold kilnBound;positivity
lemma sough_volt
 (p:|ρ|≤2)(x z:Altar G n)(h:b∈y)
 (i:Chip n)(e:i∈ stains 0 l):
  |sough q ρ s b x i-sough q ρ s b z i| ≤ kilnBound q*volt (halo (l+2) y) (x-z):=by
   let j:=relay s b i; let f:= ((j.1,false,j.2) : GFace n)
   have t:=relay_fee s b i (wet_iff.mp e)
   have w:|(x-z) f|≤ volt (halo (l+2) y) (x-z):=
     volt_take (i:=f) (halo_spec.mpr ⟨_,h,t⟩) (x-z) -- infer i?
   let u:=(Real.sqrt q.direct)⁻¹
   have hu:0≤u:=by unfold u; positivity
   change |ρ*draftSig s i*(u*x f)-ρ*draftSig s i*(u*z f)|≤(2*u)*volt (halo (l+2) y) (x-z)
   rw [←mul_sub,←mul_sub,abs_mul,abs_mul,abs_mul,abs_of_nonneg hu]
   rw [show |draftSig s i|=1 from turn_one ..,mul_one,mul_assoc]
   exact mul_le_mul p (mul_le_mul_of_nonneg_left w hu) (by positivity) (by norm_num)

variable {A:Ink (Chip n)}
lemma unfurl_volt
   (pk:0<k) (p:|ρ|≤2)(x z:Altar G n)(h:b∈y)
   (g:A.qty≤c)(e:A.Within (stains 0 l)):
 ‖unfurl q k ρ A s b x - unfurl q k ρ A s b z‖ ≤
    4*c*(1+k)*kilnBound q*volt (halo (l+2) y) (x-z) :=by
  have hc:=kiln_pos (q:=q)
  refine le_trans (air_gap pk g e ?_ _ _ (fun i a=>sough_volt p x z h i a)) (le_of_eq (by ring))
  exact mul_nonneg hc (volt_non ..)
lemma compose_limit
   (pk:0<k) (g:A.qty≤c)
   (z:Site n)(s:Signed)(b:Site n)(x:Altar G n):
    |compose q k ρ A z s b x| ≤ (c*k)^2:=by
    have d(t w):‖unfurl q k ρ A t w x‖≤ c*k:=air_limit pk g _
    have h:0≤c:=(A.qty_nonneg).trans g
    unfold compose
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul,RCLike.norm_conj,sq]
    exact mul_le_mul (d ..) (d ..) (norm_nonneg _) (by positivity)

def wager (q:Clip)(c k:ℝ):ℝ:=8*kilnBound q*c^2*k*(1+k)
lemma wager_non (u:0<k):0≤wager q c k:=by
    have y:=kiln_pos (q:=q)
    unfold wager
    positivity

lemma compose_volt
   (pk:0<k) (p:|ρ|≤2) (g:A.qty≤c) (e:A.Within (stains 0 l))
   (x z:Altar G n){d:Site n}(h:b∈y)(u:affine s b d∈y):
 |compose q k ρ A d s b x-compose q k ρ A d s b z|≤
   wager q c k*volt (halo (l+2) y) (x-z):=by
 refine (shade_gap (unfurl_volt pk p _ _ h g e)
  (unfurl_volt pk p _ _ u g e)
  (show ‖unfurl q k ρ A (s*mir) (affine s b d) x‖ ≤ c*k from air_limit pk g _)
  (show ‖unfurl q k ρ A s b z‖ ≤ c*k from air_limit pk g _)).trans_eq ?_
 unfold wager; ring

def soiree (q:Clip)(k ρ:ℝ)(A:Ink (Chip n))(z:Site n)(R:Ballroom J n)
   (x:Altar G n):ℝ:=
   ∑j,compose q k ρ A z (R.path j) (R.post j) x

variable (z:Site n)(R:Ballroom J n)(pk:0<k)(p:|ρ|≤2)(g:A.qty≤c)
variable (space:R.Space l z)
include pk in
lemma soiree_smooth (ρ:ℝ):
    ContDiff ℝ 1 (soiree q k ρ A z R):=
   ContDiff.sum (fun _ _=>compose_smooth pk ..)

include pk g
lemma soiree_limit (x:Altar G n):
 |soiree q k ρ A z R x| ≤ Fintype.card J * (c*k)^2:=by
 unfold soiree
 exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum
    (fun j _=>compose_limit (q:=q) (ρ:=ρ) pk g z (R.path j) (R.post j) x)).trans_eq (by simp))

include p space

lemma soiree_gap (e:A.Within (stains 0 l))(x y:Altar G n):
 |soiree q k ρ A z R x-soiree q k ρ A z R y| ≤
   (wager q c k * Real.sqrt (Fintype.card J))*‖x-y‖:=by
 simp_rw [soiree]
 rw [←sum_sub_distrib]
 rw [mul_assoc]
 refine le_trans ?_ (mul_le_mul_of_nonneg_left (volt_budget _ space _) (wager_non pk))
 rw [mul_sum]
 apply (abs_sum_le_sum_abs ..).trans
 apply sum_le_sum;intro j _
 exact compose_volt (y:={R.post j,R.back z j}) pk p g e _ _
   (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))

lemma leads (e:A.Within (stains 0 l)):
  ∀ i, ‖fderiv ℝ (soiree q k ρ A z R) i‖ ≤ wager q c k * Real.sqrt (Fintype.card J):=by

 let r:ℝ≥0:=⟨_,mul_nonneg (wager_non (q:=q) (c:=c) pk) (Real.sqrt_nonneg (Fintype.card J))⟩
 have h:LipschitzWith r (soiree q k ρ A z R):=
    LipschitzWith.of_dist_le_mul fun i j=>by
      rw [Real.dist_eq,dist_eq_norm]
      exact soiree_gap z R pk p g space e i j

 intro i
 exact norm_fderiv_le_of_lipschitz ℝ h

omit space g p

variable (B:Z.Bounds q θ v a)(P:Attached M Z)(L:Floor M q n η C)(O:Bid.Sworn M n G)

include L O

lemma omen:
 clouds B P (soiree q k ρ A z R)=Fintype.card J * Optic.monetary B P k ρ A z:=by
 unfold soiree clouds
 let S:=stamen B P n
 let f(j:J):S→ℝ:=fun x=>compose q k ρ A z (R.path j) (R.post j) x.val
 have h(j:J): Integrable (f j) (stdGaussian S):=
     Regis.bree _ _ 
      (((compose_smooth pk A ..).continuous.comp continuous_subtype_val).measurable)
      (fun _=>compose_limit pk (le_refl A.qty) ..)
 rw [integral_finsetSum univ (fun i _=>h i)]
 change (∑j,clouds B P (compose q k ρ A z (R.path j) (R.post j)))=_
 simp_rw [even_keel B P L O pk]
 simp
