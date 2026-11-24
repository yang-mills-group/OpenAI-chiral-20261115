/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import ExactRunning.Scenes.Frame
import YM.Next.STATIONARY.Loops.HessianMatch
import YM.Next.STATIONARY.OneLoop.Lattice

/-!
# Endpoint record

For a single endpoint PathData: `epCost` at positive cutoff uses the
left Hessian (`flare`) of the main action completed with a
Mail·Mailᵀ term (Mail = `mail U`, gauge tangent map in left link
coordinates), and ghost `tonic` = MailᵀMail.

`Endpoint` records the film F of the uncompleted Hessian, with tickets
at every period and nonsingularity of the completed symbol where
shade > 0. Thus for positive cutoffs the thermodynamic quantity `epValue`
measures the actual cost, as follows.

Use two background plane waves, (-p,p), both in axis-1 **bond**
direction in color i, with p along axis 0 (axes 0–3; quiet).
Evaluate the Hessian of regulated cost per site, in the thermodynamic
limit: a momentum profile diagonal on the quiet waves (see `Endpoint.data`,
`Medium.plays`). Take the second coefficient in real external momentum
(`alphaK`); we only need the real part. All in this endpoint's own units.

`harvest` packages up the massless film and a uniform singularity estimate
on its *massive* relative (via `astronomy`); hypotheses independent
of any blocking for the next step.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
variable {G : Gauge} {R : PathData G} {p : Clip} {m : Side} {F : KindF G}

abbrev Entry (G : Gauge) := Fslot G
def stripe (i : G.ColorIndex) : Entry G := (coord 1,i)

def magcurve (V : Kin (Fslot G)) (i : G.ColorIndex) (t : ℝ) : ℂ :=
  V (tilt 0 t) (stripe i) (stripe i)

def alphaK (V : Kin (Fslot G)) (i : G.ColorIndex) : ℝ :=
  quad (fun t => (magcurve V i t).re)

/-- No slicing implicit. -/
def epScene (F : KindF G) : Scene (Fslot G) :=
  (↑((1:ℝ)/2):ℂ) • tableau (granary G F) - tableau (quarry G)

/-- Quadratic magnetic test on the regulated endpoint. -/
def epValue (F : KindF G) (D : Latitude) (i : G.ColorIndex) : ℝ :=
  alphaK (D.run (epScene F)) i

variable (D : Latitude)

/-- Completed left Hessian of fine (or native, i.e., considered as
fine for the next step). -/
def epMat (p : Clip) (R : PathData G) (U : Config G m) :=
  flare p R U + mail U * (mail U)ᵀ

def epCost (p : Clip) (R : PathData G) (U : Config G m) : ℝ :=
  (1/2) * (D.cut m (Entry G)).cutlog (epMat p R U) -
  (D.cut m (Foot G)).cutlog (tonic U)

lemma granary_green {σ : ℝ} (h : Play F σ) : Play (granary G F) σ :=
  h.plus (matina_green.pay matina_green.rear)
lemma granaryG (h : Ticket F (fineFlare p R (m:=m))) :
    Ticket (granary G F) (epMat p R ∘ input G m) :=
  h.plus (pelt_ticket.pay pelt_ticket.rear)

lemma quarry_tab (x : Momentum) (hx : star x=x) :
    (quarry G).tab x = stone x • 1 := by
  have he := crumbly (μ:=0) (G:=G) zero_lt_one x (Work.F07.realStrip _ zero_lt_one hx)
  simpa [cinder,Film.plus,Film.cardF,soda] using he

lemma shade_of_safe {x : Momentum} (hd : 0<D.radius) (hx : star x=x) (hi : D.safe x) :
    0 < shadeK x := by
  obtain ⟨v,hv,hh⟩ := Nave.roll x
  rw [← shadeK_round hh]
  have hv' : star v=v := by
    obtain ⟨z,hz⟩ := hh.symm
    simp [hz,hx]; ext; simp [reciprocal]
  rw [← axes_of_real hv']
  have hp := hi.rolls hh.symm
  refine lt_of_lt_of_le (mul_pos (by norm_num) ?_) (orbit_lower _ (by rw [axes_of_real hv']; exact hv))
  rw [flay, norm_pos_iff]
  intro e
  have ha : (v 3).re = 0 := congrArg (fun q : Gaia => q 3) e
  exact (hd.trans_le hp).ne' (by simp [Latitude.mark,ha,wrapDist_zero])


lemma quarry_unit (x : Momentum) (hx : star x=x) (hv : 0<shadeK x) :
    IsUnit ((quarry G).tab x).det := by
  rw [quarry_tab _ hx, det_smul, det_one, mul_one, stone_real hx]
  simp [hv.ne']

lemma tonic_cut_unit (m : Side) (hd : 0<D.radius) :
    IsUnit ((D.cut m (Foot G)).cutdet (tonic (1:Config G m))) := by
  have h := D.cut_unit quarry_g (m:=m) (fun q a b => quarry_unit (G:=G) q a
    (shade_of_safe D hd a b.safe))
  simpa [input_zero] using h

/-- Film F represents this endpoint and is suitable for any of our
positive-radius slices. Reading only the massless vertices. -/
structure Endpoint (p : Clip) (R : PathData G) (F : KindF G) : Prop where
  played : ∃ σ : ℝ, 0<σ ∧ Play F σ
  ticket (m : Side) : Ticket F (fineFlare p R (m:=m))
  floor (x : Momentum) : star x=x → 0<shadeK x → IsUnit ((granary G F).tab x).det

variable {D} (s : Endpoint p R F) (hd : 0<D.radius)
namespace Endpoint
include s hd

lemma unit (m : Side) :
    IsUnit ((D.cut m (Entry G)).cutdet (epMat p R (1:Config G m))) := by
  have h := D.cut_unit (granaryG (s.ticket m))
    (fun q a b => s.floor q a (shade_of_safe D hd a b.safe))
  simpa [Function.comp_def,input_zero] using h

lemma medium : D.Medium (epScene F) := by
  rcases s.played with ⟨σ,hσ,hF⟩
  exact (((D.tableau_Medium (granary_green hF) hσ
    (fun q a b => s.floor q a (shade_of_safe D hd a b))).smul _).sub
    (D.tableau_Medium quarry_p hσ (fun q a b => quarry_unit q a
      (shade_of_safe D hd a b))))

lemma data (m : Side) :
    Resonance D (D.play m (epScene F)) (epCost D p R ∘ input G m) := by
  have h := D.resonance (granaryG (s.ticket m)) (by
    simp only [Function.comp_apply,input_zero]; exact s.unit hd _)
  have j := D.resonance (quarry_g (G:=G) (m:=m)) (by
    simp only [input_zero]; exact tonic_cut_unit D _ hd)
  rw [epScene,D.play_sub,D.play_smul]
  exact (h.weight (1/2)).sub j
end Endpoint

/-- A renewable certificate also controlling *massive* internal
kinetic traces. -/
def Grounds (A C : ℝ) (F : KindF G) :=
  ∀ {μ : ℝ}, 0<μ → μ≤1 → ∀ i,
  Waves1 A μ (keelRay (amena μ G F) i) ∧
  Waves2 C μ (keelRay (amena μ G F) i) G

/-- Endpoint factory. Analytic play and lower bounds used later. -/
lemma harvest (G : Gauge) (h : G.Simple) (σ ε C Z τ A : ℝ)
    (hs : 0<σ) (he : 0<ε) (hC : 0≤C) (hZ : 0≤Z) (ht : 0<τ) (hA : 0≤A) :
    ∃ a b : ℝ, 0≤a ∧ 0≤b ∧
    ∀ (B : Bed) (p : Clip) (R : PathData G) (Λ : ℝ),
      R.Bounds p τ A Λ → Attached B R → B.metric.strip σ C → p.direct ≤ Z →
      (∀ n, Floor B p n ε C) → (∀ n, Bid.Sworn B n G) →
      ∃ F : KindF G, Endpoint p R F ∧ Grounds a b F := by
  obtain ⟨k,E,hk,hE,H,hH,hL⟩ := vintageWilson G
  obtain ⟨v,M,hv,hM,Y⟩ := saunter G h σ ε C Z τ A hs hC hZ ht hA
  let w:= min k v
  have hW : 0<w := lt_min hk hv
  have hx : H.fees w E := hH.less hW (min_le_left ..) le_rfl
  obtain ⟨a,b,ha,hb,V⟩ := astronomy hx hL he hW h C M

  refine ⟨a,b,ha,hb,fun B p R Λ hp ht hh hu hX hj => ?_⟩
  obtain ⟨T,hT,hK,HK⟩ := Y walent walentes B p R Λ hp ht hh hu hX (fun _ => hj _)
  let F := T.combine H; let X:=F.cast
  have hs' := hT.less hW (min_le_right ..) le_rfl
  have ht' : F.fees w (M+E) := hs'.pay hx
  have hx' (m : Side) : Ticket X (fineFlare p R (m:=m)) := by
    obtain ⟨i,rfl⟩ : ∃ i, walent i=m := by
      rcases m with ⟨i,h⟩; cases i with
      | zero => omega
      | succ i => exact ⟨i,rfl⟩
    have hl : AnalyticAt ℝ (intended p R (m:=walent i)) 0 := (strain p R hp).analytic
    have hw := ((Wilson_stream G 2).1 (walent i))
    have hu := Jar.sequelQ (hl.sub hw) hw (HK i) (hL _)
    rw [sub_add_cancel] at hu
    exact Jar.cast_book ht' _ hu hp
  refine ⟨X,⟨⟨w,hW,ht'.live⟩, hx', ?_⟩, ?_⟩

  · -- Curtain
    let k:= min σ w
    have hw : 0<k := lt_min hs hW
    have hm : Play X k := ht'.live.mono (min_le_right ..)
    have hm' : Poster k (curtainG G B) :=
      (rug_played _ (A:=C) (fun i j=> (hh i j).mono (min_le_left ..) le_rfl) hw).amounts
        ((page_linen 0).forge ((page_linen 0).reverse))
    suffices hg : ∀ x ∈ strip k, (granary G X).tab x=curtainG G B x by
      intro x hxx hxs; rw [hg _ (Work.F07.realStrip _ hw hxx)]
      exact pillar_gap hh hs hX he hxx hxs
    apply Poster.renew (granary_green hm).tab hm' hw walentes
    refine fun i=> ⟨_, (granaryG (hx' (walent i))).tab, ?_⟩
    rw [cardM, Function.comp_apply, input_zero, epMat, prom_addition,
      flare_matches hp (hX _) ht (hj _), mailed_zero, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, prom_mul]
    exact (rug_plane _ B (B.metric.rights _ _ hh hs.le)).plus
      ((page_read _ 0).hoist (page_read _ 0 |>.takes))

  intro y hr hsr i
  let k:= min σ (min w (y*(1/128)))
  have hg' : 0<k := lt_min hs (lt_min hW (by positivity))
  have hw : k≤min w (y*(1/128)) := min_le_right ..
  have hm' : Play X k := ht'.live.mono (hw.trans (min_le_left ..))
  have he' : B.metric.strip k C := fun i j=> (hh i j).mono (min_le_left ..) le_rfl
  have ha' : HouseWord G B p C ε k C y X :=
    ⟨hm',he',⟨hr,hsr⟩,hw.trans (min_le_right ..),hg',
     massifTabs hm' walentes (fun _=>hx' _) hp (hX 1)
       (fun _ => hX _) ht (fun _ => hj _) he' hr hsr (hw.trans (min_le_right ..)) hg',
     hX,he⟩
  exact V ⟨k,y,i,B,p,T,ha',hs',hK⟩

end ExactRunning
