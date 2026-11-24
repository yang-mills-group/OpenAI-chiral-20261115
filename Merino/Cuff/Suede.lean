import Merino.Cabinet
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Cuff
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n

open Push.Uniform Planned.JetPort Peaks
open scoped ContDiff

-- profile-solo
abbrev Hue := SU.group.Color
abbrev Bows (n:Side):= Directions group (More n)

/- The single-link profile as an analytic function of exponential
arguments. L2 op norm instances here! Gauge.exp_jet
gives Frobenius, converted via Laic.entry_F. -/
def damask (v:Hue):Bool→Twig:=fun h=>
  if h then brand (group.lieExp v) else star (brand (group.lieExp v))
section
open scoped Matrix.Norms.Frobenius
lemma eager (i j:SU.F)(v:Hue):ContDiffAt ℝ ω (fun x=>fund (group.lieExp x) i j) v:=
  (entry_F i j).contDiff.contDiffAt.comp _ (group.exp_jet.contDiffAt)
end
lemma suave (v:Hue): ContDiffAt ℝ ω damask v:=by
 let f(x):= SU.fund (group.lieExp x)
 have hf:ContDiffAt ℝ ω f v:= Nacre.tort.mpr (fun i j=>eager i j v)
 have ht:ContDiffAt ℝ ω SU.triple (f v):=by
   -- from plex at any base
   refine tort.mpr ?_
   rintro ⟨i,r⟩ ⟨j,s⟩
   have he (i j:SU.F): ContDiffAt ℝ ω (fun p:Op SU.F=> p i j) (f v):=tort.mp contDiffAt_id i j
   refine ContDiffAt.mul contDiffAt_const ?_
   cases r with
   | inl a=> cases s with
      | inl b=> change ContDiffAt ℝ ω (fun p=>SU.each p (.inl a) (.inl b)) _; simp_rw [each,Join.both,Matrix.fromBlocks_apply₁₁,ExTwo.wedge_entry]; exact ((he _ _).mul (he _ _)).sub ((he _ _).mul (he _ _))
      | inr b=> exact contDiffAt_const
   | inr a=> cases s with
      | inl b=> exact contDiffAt_const
      | inr b=> exact Complex.conjCLE.contDiff.contDiffAt.comp _ (he a b)

 have hu: ContDiffAt ℝ ω (fun p=>brand (group.lieExp p)) v:= (ht.comp v hf).prodMk hf
 apply contDiffAt_pi.mpr; rintro (_|_)
 · exact (starL ℝ: Twig≃L[ℝ] Twig).contDiff.contDiffAt.comp _ hu
 exact hu

abbrev dyeB (n:Side): Bows n→Pane n:= increment 1
abbrev gleam (n:Side): Bows n→Chin n:= fun x=>profile (dyeB n x)

lemma shines (X: Bows n)(i:Edge (Site (More n))):
   gleam n X i= damask (X i):=by
  change (fun (b:Bool)=>if b then brand (group.lieExp (X i)*1) else star (brand (group.lieExp (X i)*1)))=_
  rw [mul_one]; rfl


lemma gleam_cost:∃ B:ℝ,0≤B ∧
    ∀ {n:Side} {X:Bows n},‖X‖ ≤ 1 → Jet.Allows 3 (gleam n) X B:=by
 obtain ⟨A,h,p⟩:=exists_allows (f:=damask)
   (isCompact_closedBall (0:Hue) 1) (fun x _=>suave x) 3
 let B:=Jet.composeCost 3 A 1
 have hB:0≤B:=by unfold B Jet.composeCost; positivity
 refine ⟨B,hB,?_⟩
 intro n X u
 refine Jet.allows_pi hB fun i=> ?_
 simp_rw [shines]
 let L:Bows n→L[ℝ]Hue:= ContinuousLinearMap.proj i
 have hi:‖L X‖≤1:=(norm_le_pi_norm X i).trans u
 have ha:=p (L X) (by simpa using hi)
 exact Jet.Allows.comp (f:=L)
    ⟨ha.analytic.of_le le_top,ha.norm_le⟩
    (Jet.allows_linear (L.opNorm_le_bound zero_le_one fun x=> by rw [one_mul]; exact norm_le_pi_norm x i) hi)

lemma vague {d:ℝ} (p:0<d):
  ∃ r:ℝ,0<r∧r≤1∧∀ {n:Side}{X:Bows n}, ‖X‖≤r → dist (gleam n X) 1 < d:=by
 have h:damask 0 = 1:=by
    funext b; cases b <;> simp [damask,brand_one]
 obtain ⟨r,hr,H⟩:= continuousAt_iff.mp ((suave 0).continuousAt) d p
 refine ⟨min 1 (r/2),by positivity,min_le_left .., ?_⟩


 intro n X u; rw [dist_eq_norm,pi_norm_lt_iff p]; intro i
 rw [Pi.sub_apply,shines, Pi.one_apply,←h,←dist_eq_norm]
 apply H
 rw [dist_eq_norm,sub_zero]
 exact (norm_le_pi_norm _ _).trans_lt ((u.trans (min_le_right ..)).trans_lt (half_lt_self hr))

lemma shade {d:ℝ}(h:0<d): ball (1:Chin n) d ⊆ Openc (More n) d:=by
 intro x hx
 refine ⟨1,guard0 h.le,?_⟩
 rw [profile_trivial]
 exact (dist_eq_norm x 1) ▸ (show dist x 1<d from hx)


def flash {d:ℝ}(A : Openc (More n) d→ℂ): Bows n → ℝ:=fun X=>
  (Jet.equalizer A (gleam n X)).re
structure Room (d r C:ℝ):Prop where
 price:0<C
 haveR:0<r
 get {n:Side}(x:Bows n)(h:‖x‖≤r):gleam n x ∈ Openc (More n) d
 pay {n:Side}(f:Openc (More n) d→ℂ)(K:ℝ)(h:Looks _ f)
   (v:Continuous f)(g:∀ t,‖f t‖≤K) {x:Bows n}: ‖x‖≤r →
     Jet.Allows 3 (flash f) x (K*C)
lemma Room.reserve {d:ℝ}(hd:0<d):
   ∃ r C,Room d r C:=by
 let e:=d/2; have he:0<e:=half_pos hd
 let W:= (1+(2:ℝ)^3/e)^3
 obtain ⟨B,h,p⟩:=gleam_cost
 let C:=Jet.composeCost 3 W B
 let D:=‖Complex.reCLM‖
 have hg:0≤D:=norm_nonneg _
 obtain ⟨r,hr,hr1,u⟩:=vague he
 have hp:0<C:=by unfold C Jet.composeCost W; positivity
 refine ⟨r,D*C+1,by positivity,hr,fun x h'=>?_,?_⟩
 · exact shade hd (mem_ball.mpr ((u h').trans (half_lt_self hd)))


 intro n f K hf v g x hx
 have hK:0≤K:=(norm_nonneg _).trans (g ⟨1,shade hd (mem_ball_self hd)⟩)
 have hT: ball (gleam n x) e⊆Openc (More n) d:= by
    apply Set.Subset.trans _ (shade hd); apply ball_subset_ball'
    have hv:=u hx; unfold e at *; linarith only [hv]
 have h0:= (Jet.allows_looks hf v hT he 3 g).comp (p (hx.trans hr1))
 have h1: D*(Jet.composeCost 3 (K*W) B)≤K*(D*C+1):=by
    rw [mul_add,mul_one]
    apply le_trans _ (le_add_of_nonneg_right hK)
    unfold C Jet.composeCost; exact le_of_eq (by ring)
 exact (Jet.Allows.linear Complex.reCLM h0 le_rfl).mono h1
end YM.CF.Merino.Cuff
