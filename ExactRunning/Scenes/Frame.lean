import ExactRunning.Scenes.Medium

/-!
# Internal sum for cut determinant

Given a `Ticket` (Fourier symbol including response to external
waves through second derivatives), `Ticket.receipt` computes the
log|det| Hessian, with no analytic hypotheses in momenta. Apply it
to the entire matrix after compression. On (-p,p) with p quiet,
the active/inactive tags agree at internal momenta r and r+p, so
the summand is that for the original symbol (`tableau`) at active r,
zero otherwise. Thus, given unit cutdet at zero field,
get `Resonance` for the cut log determinant at
finite m against the `play` of the original symbol.

We can take the thermodynamic limit and even take external p derivatives
afterwards, as `Medium` deals only with the original, unmasked
integrand; derive that regularity locally.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

variable {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {m : Side}

def tableau (F : Film ι α α) : Scene ι :=
  fun p r => of (fun i j => F.figure i j p r)

namespace Latitude
variable (D : Latitude)

def masked (F : Film ι α α) : Film ι α α :=
  let Q := Film.cardF (ι:=ι) (D.maskM α)
  ((Q.pay F).pay Q).plus
    (Film.cardF fun p => 1 - D.maskM α p)

private lemma minusK (m : Side) (α : Type) [Fintype α] [DecidableEq α] :
    Jaunt (approached (1-(D.cut m α).e)) (fun p => 1 - D.maskM α p) 0 := by
  have h : approached (1-(D.cut m α).e) = 1 + -(approached (D.cut m α).e) := by
    ext a b
    by_cases h : a=b <;> simp [approached, h,sub_eq_add_neg]
  rw [h]
  simp only [sub_eq_add_neg]
  exact Jaunt.noop.plus ((D.cut_jaunt m α).backside)

lemma ticket_masked [Fintype ι] [DecidableEq ι]
    {F : Film ι α α} {U : OperatorF ι m α α} (h : Ticket F U) :
    Ticket (D.masked F) (fun z => (D.cut m α).compMat (U z)) := by
  have hh := Ticket.current (ι:=ι) _ _ (D.cut_jaunt m α)
  exact ((hh.pay h).pay hh).plus (Ticket.current _ _ (D.minusK m α))

lemma tab_masked (F : Film ι α α) (q) :
    (D.masked F).tab q = if D.active q then F.tab q else 1 := by
  by_cases h : D.active q <;> simp [masked, maskM, Film.pay,Film.plus,Film.cardF,h]

lemma cut_unit [Fintype ι] [DecidableEq ι] {F : Film ι α α}
    {U : OperatorF ι m α α} (h : Ticket F U)
    (hf : ∀ q, star q = q → D.active q → IsUnit (F.tab q).det) :
    IsUnit ((D.cut m α).cutdet (U 0)) := by
  apply isUnit_of_approached (isUnit_of_jaunt (D.ticket_masked h).tab _)
  intro p
  rw [D.tab_masked F]
  split
  · exact hf _ (real_frequency _) ‹_›
  simp

lemma spot_masked (F : Film ι α α) (i : ι) (p q : Momentum) (hp : D.quiet p) :
    (D.masked F).spot i p q = if D.active q then F.spot i p q else 0 := by
  simp [masked, maskM, Film.pay,Film.plus,Film.cardF, active_add D _ hp]
  tauto

lemma figure_masked (F : Film ι α α) (i j : ι) (p r) (hp : D.quiet p) :
    (D.masked F).figure i j p r =
      if D.active r then F.figure i j p r else 0 := by
  have hh : (D.masked F).arch i j (-p) p r =
      if D.active r then F.arch i j (-p) p r else 0 := by
    by_cases h : D.active r <;> simp [h,masked, maskM, Film.pay,Film.plus,Film.cardF]
  simp only [Film.figure,Film.framePay,Film.coupon,hh,neg_add_cancel,add_zero,
    tab_masked, D.spot_masked _ _ _ _ hp, D.spot_masked _ _ _ _ hp.neg, active_add D _ hp]
  by_cases h : D.active r <;> simp [h]

lemma resonance [Fintype ι] [DecidableEq ι]
    {F : Film ι α α} {U : OperatorF ι m α α} (h : Ticket F U)
    (hu : IsUnit ((D.cut m α).cutdet (U 0))) :
    Resonance D (D.play m (tableau F))
      (fun z => (D.cut m α).cutlog (U z)) := by
  have hm := D.ticket_masked h
  refine ⟨hm.finance.det_val.log hu.ne_zero, fun {a b p} i j _ hb hp => ?_⟩
  unfold ModeCut.cutlog ModeCut.cutdet
  by_cases he : a+b=0
  · have hf : rolls (mon a) (-p) := (eq_neg_of_add_eq_zero_left he).symm ▸ hp.flip_sign
    have t := hm.receipt hu a b (-p) p hf hp i j
    rw [if_pos he] at t
    rw [if_pos he]
    refine t.trans ?_
    rw [play, of_apply, mesh,shop,
        mul_inv_cancel_left₀ (show (cents m:ℂ) ≠ 0 from by exact_mod_cast cents_pos.ne')]
    exact sum_congr rfl fun _ _ => D.figure_masked F _ _ _ _ (hb.rolls hp)
  rw [if_neg he]
  have t := hm.receipt hu a b (mon a) p (rolls.refl _) hp i j
  rw [if_neg he] at t; exact t

variable {σ : ℝ} {F : Film ι α α}

/-- Local version of analyticity for trace films, enough for Medium
and for sending a mass regulator to zero. -/
lemma _root_.ExactRunning.differentiable_figure (h : Play F σ)
    (i j) {p r : Momentum} (hv : Boulevard σ (-p) p r)
    (h0 : IsUnit (F.tab r).det) (h1 : IsUnit (F.tab (r+p)).det) :
    DifferentiableAt ℂ (uncurry (F.figure i j)) (p,r) := by
  let u := (p,r)
  let X := Momentum × Momentum
  let x := (Prod.fst : X → Momentum); let y := (Prod.snd : X → Momentum)
  have hx : DifferentiableAt ℂ x u := by unfold x;fun_prop
  have hy : DifferentiableAt ℂ y u := by unfold y;fun_prop
  have ha := (h.arch i j).go (x:=u) hv hx.neg hx hy
  have hc := (h.spot i).go (x:=u) hv.proceed hx.neg (hy.add hx)
  have hd := (h.spot j).go (x:=u) hv.second hx hy
  have hg := (h.tab.go (x:=u) hv.second.basic hy).take h0
  have ht := (h.tab.go (x:=u) hv.second.added (hy.add hx)).take h1
  have ht := ((hg.bond ha).less (((hg.bond hc).bond ht).bond hd)).collects
  unfold uncurry Film.figure Film.framePay Film.coupon
  simp only [neg_add_cancel,add_zero]; exact ht

lemma tableau_Medium (h : Play F σ) (hσ : 0 < σ)
    (hf : ∀ q, star q = q → D.safe q → IsUnit (F.tab q).det) :
    D.Medium (tableau F) := by
  intro i j p q a b c d
  apply ContDiffAt.restrict_scalars ℝ (𝕜':=ℂ)
  apply AnalyticAt.contDiffAt
  apply PolyDisc.finiteD
  let W := Momentum × Momentum
  let x := (Prod.fst : W → Momentum); let y := (Prod.snd : W → Momentum)
  let z := (p,q)
  have hh : 0 < σ/2 := half_pos hσ
  have hq := hf q c d
  have hp := hf (q+p) (by simp [a,c]) ((D.safe_add q b).mpr d)
  have hw := duo p q hσ (Work.F07.realStrip _ hh a) (Work.F07.realStrip _ hh c)
  have hy := ((h.tab.go (p:=y) (x:=z) hw.second.basic (by unfold y;fun_prop)).via_det.continuousAt).eventually_ne hq.ne_zero

  have he := ((h.tab.go (p:=fun t=> y t+x t) (x:=z) hw.second.added (by unfold y x;fun_prop)).via_det.continuousAt).eventually_ne hp.ne_zero
  have O := Work.F07.stripOpen (α:=Axis) (σ/2)
  have hp : strip (σ/2) ×ˢ strip (σ/2) ∈ 𝓝 z :=
    mem_nhds_prod_iff.mpr ⟨_,O.mem_nhds (Work.F07.realStrip _ hh a),
      _,O.mem_nhds (Work.F07.realStrip _ hh c),Set.Subset.rfl⟩
  filter_upwards [hy,he,hp] with t yt et ht
  exact differentiable_figure h i j (duo t.1 t.2 hσ ht.1 ht.2) yt.isUnit et.isUnit

end Latitude
end ExactRunning
