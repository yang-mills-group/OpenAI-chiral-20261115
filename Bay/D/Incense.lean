import Bay.D.Villa
import Bay.D.Flax
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
open Buffered Lamour.Bridge.Celeste.Clock Fabric
open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Papal
open Vale clocks

open YM.CF.Pannier.Chancel Journey

variable {x y:ℝ}{z w:ℂ}
lemma gloss_exp (_p:0≤x)(h:‖z‖≤Real.exp y)
  (v:‖w-z‖ ≤ x*Real.exp y):
 ‖w‖≤Real.exp (y+x):=by
 rw[add_comm,Real.exp_add]
 exact (norm_le_norm_sub_add w z).trans ((add_le_add v h).trans
    ((mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos y).le).trans' (le_of_eq (by ring))))
abbrev Pebble (K:Calibration)(x:ℝ)(B:Axis→ℕ):=
 8*oar x * acres K B
lemma Tunic.bulk {n:Side} {o d:Seat n}{F:Pane n→ℝ}
 {L:List (Fabric n)}
 (h:Sylvan (Tunic o d F z) 0 L): L.length ≤ Fintype.card (Seat n):=by
 have hg(i:Fin L.length):= (h.core _ (List.get_mem L i)).fit₁
 rw[←Fintype.card_fin L.length]
 refine Fintype.card_le_of_injective (fun i=>(L.get i).o) ?_
 intro i j h₀
 have u{a b:Fin L.length}(v:a<b): (L.get a).o≠(L.get b).o:=fun e=>by
   have hh:= h.annex.rel_get_of_lt v _ (hg a) _ (hg b)
   rw[e,separation_self] at hh;omega
 exact le_antisymm (le_of_not_gt (fun l=>u l h₀.symm)) (le_of_not_gt (fun l=>u l h₀))

variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
 (s i k:ℕ)
local notation "N"=>count Y s i
local notation "Ω"=>hat P.R.L P.x s
local notation "𝒟"=>Fintype.card (Seat (count Y s i))
variable (f:Ferry Y s i k)
def Kindness:Prop:=
 ∀ (o d:Seat N)(F:Pane N→ℝ)(W:Chalk (More N) ℝ)(z:ℂ), Lease Y s i k o d F W → ‖z‖≤thetaB Ω → ∀ (L:List (Fabric N)), Sylvan (Tunic o d F z) 0 L →
    ‖compass Y i k s (buffet L)-solder Y i k f.depth s (buffet L)‖ ≤ oar Ω * Real.exp (L.length * Fly z (beans Y s i k W) Ω)

lemma laterKindness (t:0<Ω):
 ∀ᶠ j:ℕ in atTop,∀ f:Ferry Y s i j,Kindness Y s i j f:=by
 let W₀:ℝ:= thetaB Ω * Ni Ω + |wavePay Ω|
 have h₀:0≤W₀:=by unfold W₀ thetaB Ni atRate; positivity
 have hV:0<oar Ω:=by unfold oar;positivity
 let M:=1+thetaB Ω * Mi Ω
 have hg:1≤M:= le_add_of_nonneg_right (by unfold thetaB Mi atRate; positivity)
 let q:=oar Ω * Real.exp (- (𝒟*W₀)) / M^𝒟
 have m:0<M:=zero_lt_one.trans_le hg
 have pv:0<q:=by unfold q; positivity
 filter_upwards [thaw_plot Y q pv s] with j v b o d F W z H ht L h
 

 change Ion _ _ _ _ _ _ _ _ _ _ _ _ _ at H
 have p:=Tunic.bulk h
 have hn:= H.perks.1
 refine (v i b.depth _ (M^𝒟) (h.occupy fun _ y=>y.fit).env (fun x=> (Tunic.count h _ hn H.limit x).trans ((pow_le_pow_left₀
   (show (0:ℝ)≤1+‖z‖*Mi Ω by positivity)
   (add_le_add le_rfl (mul_le_mul_of_nonneg_right ht hn)) L.length).trans (pow_le_pow_right₀ hg p)) )).trans ?_
 unfold q;rw [div_mul_cancel₀ _ (pow_pos m _).ne']
 refine mul_le_mul_of_nonneg_left (Real.exp_monotone ((neg_le_neg (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr p) h₀)).trans ?_)) hV.le
 rw [←mul_neg]
 refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
 exact neg_le.mp ((neg_le_abs _).trans (abs_add_le .. |>.trans
    (add_le_add (le_trans (by rw [abs_mul]) (mul_le_mul ((Complex.abs_re_le_norm z).trans ht)
       H.flavor_fee (abs_nonneg _) ((norm_nonneg _).trans ht))) le_rfl)))


variable (H:Real.exp 1≤P.x)
def Canopy:Prop:=
 ∀ (o d:Seat N)(F:Pane N→ℝ)(W:Chalk (More N) ℝ)(z:ℂ), Lease Y s i k o d F W → ‖z‖≤thetaB Ω → ∀ (L:List (Fabric N)), Sylvan (Tunic o d F z) 0 L →
    ∀ (B:Axis→ℕ), Will (Journey.tent Y H) N B (Fabric.Broad 0 L) →
 ‖compass Y i k s (buffet L)‖ ≤ Real.exp (L.length * Fly z (beans Y s i k W) Ω + Pebble (Journey.tent Y H) Ω B)
lemma pilaster
   (t:0<Ω) (q:Kindness Y s i k f)
   (g:Chintz Y s i k):Canopy Y s i k H:=by
 intro o d F W z h hz L hL B u
 let α:= Journey.tent Y H
 let a:=oar Ω
 let c:=Fly z (beans Y s i k W) Ω
 let R:=acres α B
 have hv:0<a:=by unfold a oar;positivity
 have hv':0<(sites N):=zero_lt_one.trans_le (sites_pos _)
 have hx:1≤ (R:ℝ):= by exact_mod_cast (acres_pos α B)
 let ν:=solder Y i k f.depth s
 obtain ⟨r,J,e,m,p,v,l⟩:= villa
    (W:=Tunic o d F z) (fun y=>y.rev) (fun _ y=>y.fit)
    (revive Y H s i k f)
    (Journey.terrain Y H (Y.ir i) s).symm
    hL B u

 have hh: ‖ν (buffet J)‖≤Real.exp (J.length*c+7*a*sites N):=by
    have t':= (g.wind o d F W h z hz J p)
    have ht: ‖ν (buffet J) - compass Y i k s (buffet J)‖ ≤ a*Real.exp (J.length*c+6*a*sites N):=by
      rw [norm_sub_rev]
      exact (q o d F W z h hz J p).trans (mul_le_mul_of_nonneg_left
         (Real.exp_monotone (le_add_of_nonneg_right (by positivity :0≤ 6*a*sites N))) hv.le)
    refine (gloss_exp hv.le t' ht).trans (Real.exp_monotone ?_)
    change J.length*c+6*a*sites N+a≤_
    nlinarith only [mul_le_mul_of_nonneg_left (sites_pos N) hv.le]
 have he: ‖ν (buffet L)‖≤Real.exp (L.length*c+7*a*R):=by
    apply le_of_pow_le_pow_left₀ (n:=r) (by omega) (Real.exp_pos _).le
    rw [← Real.exp_nat_mul]
    refine (l.trans hh).trans (Real.exp_monotone ?_)
    have hm: sites N ≤ (r:ℝ)*R:= by unfold sites; exact_mod_cast m
    rw[v,Nat.cast_mul]
    nlinarith only [mul_le_mul_of_nonneg_left hm hv.le]
 refine (gloss_exp hv.le he ((q _ _ _ _ _ h hz L hL).trans
   (mul_le_mul_of_nonneg_left
      (Real.exp_monotone (le_add_of_nonneg_right (mul_nonneg
      (show 0≤ (7:ℝ)*a by positivity) (Nat.cast_nonneg R)))) hv.le))).trans (Real.exp_monotone ?_)
 change _ ≤ L.length*c+8*a*R
 nlinarith only [mul_le_mul_of_nonneg_left hx hv.le]

theorem canopies (g:DryDock P):
 ∀ᶠ j in atTop,∀ (a:ℕ),∀ᶠ b:ℕ in atTop,Canopy Y j a b H:=by
 filter_upwards [flaxCompass Y g,(stage_slope P.V P.x).eventually_gt_atTop 0] with j h k a
 filter_upwards [ferry_later Y j a,laterKindness Y j a k] with b f v
 exact pilaster Y j a b f H k (v f) (h a b f.depth f.enters)
#print axioms canopies
end YM.CF.Bay.D
