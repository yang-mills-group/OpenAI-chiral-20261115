import Merino.Cuff.Suede

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.JadeEye
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n : Side}
open Push.Uniform Planned.JetPort Peaks Cuff
open scoped ContDiff

abbrev pale (z:Hue × Hue) : Bool→Twig :=
 fun b => if b then damask z.2 true * damask z.1 true else
   damask z.1 false * damask z.2 false

lemma pink (v:Hue × Hue): ContDiffAt ℝ ω pale v:=by
 have h : ∀ b,ContDiff ℝ ω (fun z: Hue => damask z b):=by
   intro b; exact contDiff_iff_contDiffAt.mpr (fun z=>(contDiffAt_pi.mp (suave z)) b)
 apply contDiffAt_pi.mpr
 rintro (_|_)
 · exact (((h false).comp contDiff_fst).mul ((h false).comp contDiff_snd)).contDiffAt
 exact (((h true).comp contDiff_snd).mul ((h true).comp contDiff_fst)).contDiffAt

abbrev Duo (n:Side):= Bows n × Bows n
abbrev du (n:Side): Duo n→Pane n:= fun z=>increment (dyeB n z.1) z.2
abbrev deo (n:Side): Duo n→Chin n:= fun z=>profile (du n z)

lemma milk (X:Duo n)(i:Edge (Site (More n))):
   deo n X i = pale (X.1 i,X.2 i):=by
  change (fun b:Bool=>if b then brand (group.lieExp (X.2 i)*(group.lieExp (X.1 i)*1)) else
     star (brand (group.lieExp (X.2 i)*(group.lieExp (X.1 i)*1))))=_
  simp only [mul_one,brand_mul,star_mul]
  rfl

def combo (i:Edge (Site (More n))):Duo n→L[ℝ](Hue×Hue):=
  ((ContinuousLinearMap.proj (φ:=fun _=>Hue) i).comp (ContinuousLinearMap.fst ..)).prod
    ((ContinuousLinearMap.proj (φ:=fun _=>Hue) i).comp (ContinuousLinearMap.snd ..))
lemma leaner (X:Duo n)(i:Edge (Site (More n))): ‖combo i X‖≤‖X‖:=
  max_le_max (norm_le_pi_norm X.1 i) (norm_le_pi_norm X.2 i)
lemma deo_cost:∃ B:ℝ,0≤B ∧
    ∀ {n:Side} {X:Duo n},‖X‖ ≤ 1 → Jet.Allows 6 (deo n) X B:=by
 obtain ⟨A,h,p⟩:=exists_allows (f:=pale)
   (isCompact_closedBall (0:Hue×Hue) 1) (fun x _=>pink x) 6
 let B:=Jet.composeCost 6 A 1
 have hB:0≤B:=by unfold B Jet.composeCost; positivity
 refine ⟨B,hB,?_⟩
 intro n X u
 refine Jet.allows_pi hB fun i=> ?_
 simp_rw [milk]
 let L:Duo n→L[ℝ](Hue×Hue):= combo i
 have hi:‖L X‖≤1:=(leaner _ _).trans u
 have ha:=p (L X) (by simpa using hi)
 exact Jet.Allows.comp (f:=L)
    ⟨ha.analytic.of_le le_top,ha.norm_le⟩
    (Jet.allows_linear (L.opNorm_le_bound zero_le_one fun x=> by rw [one_mul]; exact leaner _ _) hi)

lemma vague {d:ℝ} (p:0<d):
  ∃ r:ℝ,0<r∧r≤1∧∀ {n:Side}{X:Duo n}, ‖X‖≤r → dist (deo n X) 1 < d:=by
 have h:pale 0 = 1:=by
    funext b; cases b <;> simp [pale,damask,brand_one]
 obtain ⟨r,hr,H⟩:= continuousAt_iff.mp ((pink 0).continuousAt) d p
 refine ⟨min 1 (r/2),by positivity,min_le_left .., ?_⟩


 intro n X u; rw [dist_eq_norm,pi_norm_lt_iff p]; intro i
 rw [Pi.sub_apply,milk, Pi.one_apply,←h,←dist_eq_norm]
 apply H
 rw [dist_eq_norm,sub_zero]
 exact (leaner _ _).trans_lt ((u.trans (min_le_right ..)).trans_lt (half_lt_self hr))


def glint {d:ℝ}(A : Openc (More n) d→ℂ): Duo n → ℂ:=fun X=>
  Jet.equalizer A (deo n X)
structure Room (d r C:ℝ):Prop where
 price:0<C
 haveR:0<r
 get {n:Side}(x:Duo n)(h:‖x‖≤r):deo n x ∈ Openc (More n) d
 pay {n:Side}(f:Openc (More n) d→ℂ)(K:ℝ)(h:Looks _ f)
   (v:Continuous f)(g:∀ t,‖f t‖≤K) {x:Duo n}: ‖x‖≤r →
     Jet.Allows 6 (glint f) x (K*C)
lemma Room.reserve {d:ℝ}(hd:0<d):
   ∃ r C,Room d r C:=by
 let e:=d/2; have he:0<e:=half_pos hd
 let W:= (1+(2:ℝ)^6/e)^6
 obtain ⟨B,h,p⟩:=deo_cost
 let C:=Jet.composeCost 6 W B
 let D:=(1:ℝ)
 have hg:0≤D:=zero_le_one
 obtain ⟨r,hr,hr1,u⟩:=vague he
 have hp:0<C:=by unfold C Jet.composeCost W; positivity
 refine ⟨r,D*C+1,by positivity,hr,fun x h'=>?_,?_⟩
 · exact shade hd (mem_ball.mpr ((u h').trans (half_lt_self hd)))


 intro n f K hf v g x hx
 have hK:0≤K:=(norm_nonneg _).trans (g ⟨1,shade hd (mem_ball_self hd)⟩)
 have hT: ball (deo n x) e⊆Openc (More n) d:= by
    apply Set.Subset.trans _ (shade hd); apply ball_subset_ball'
    have hv:=u hx; unfold e at *; linarith only [hv]
 have h0:= (Jet.allows_looks hf v hT he 6 g).comp (p (hx.trans hr1))
 have h1: D*(Jet.composeCost 6 (K*W) B)≤K*(D*C+1):=by
    rw [mul_add,mul_one]
    apply le_trans _ (le_add_of_nonneg_right hK)
    unfold C Jet.composeCost; exact le_of_eq (by ring)
 rw [show D=1 from rfl, one_mul] at h1
 exact h0.mono h1
