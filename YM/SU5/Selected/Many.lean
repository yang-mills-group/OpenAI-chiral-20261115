import YM.SU5.Selected.Ablate

/-!
# Upgrade from chosen phase to interaction across all six representation
families, at once in the selected history. `within_s` money, additional
curvature cutoff on **first field**, at every face contained in the
observing base. No statement of a limit threshold uniform in resolution.
Thus this rules out reading these signals only with a flat gauge field
(and rules out product factorization, as before), but does not address some
stronger dynamics questions (see main task and commentary). -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification CF.Pannier.Chancel

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "ir" => i ∘ G.rows
local notation "uv" => k ∘ G.columns


lemma takeFixture (z : SU.Slot) {q d w : ℕ} (o : Cover) {C Z : ℝ}
    (p : Papal.Cornet Y H q d w C Z) {A:ℝ}{s:ℕ}{F:observable K true} (v:F.val∈Filigree K (Window.family z) (booty o d q) (Sen o (payout d q w)))
    (hA:0<A)(a:SupportedPhysically Λ l s (Sen o (payout d q w)) (Tapestry.cabin A))(pos:1/4≤ ‖E s F.val‖): Fixture Y H V G z q d w o s F A := by
  have hf := FilTest v; let neutral : CovCover K F.val:= F.property.2 rfl
  refine ⟨v,neutral, (obs_in ..).2 ⟨hf,neutral⟩,hA, ?_,
    ⟨p.cents _, Papal.stake_centers Y H o d q w⟩,
    div_pos zero_lt_one (Tapestry.positiveScale Λ s),
    fun j y g => matterSpacing (g j|>.symm), pos, ?_ ⟩
  · intro r L
    have h := proceeds Y H G.history.circuit s r hf.widen
    refine ⟨a.persists r, chroma Y H G.history.circuit s r ((obs_in ..).2 ⟨hf.widen,neutral⟩),
      (G.history.finance _).and (final_distances Y H V G L _),?_⟩
    rw [← h.2]
    exact final_limit Y H G _ _ (aux_test h.1)
  · intro j B r x T Ω
    have hb := Vacancy.cap_level (F := F) Y H V s G.history G.clipped j true B (s+r) (by omega)
    rw [Nat.add_sub_cancel_left] at hb
    exact ⟨hb,(congrArg (fun t : (Aurora Y H V G.history j true B) →L[ℂ] (Aurora Y H V G.history j true B) => inner ℂ Ω (t Ω)) hb).trans
      (Vacancy.inspected Y H V s G.history G.clipped j true B)⟩


variable (D : Axis) (R : ∀ j:Axis, Arena Y H G.history.circuit j 0 false)
open Theory
local notation "X"=> markE Y H V G false D (R D)
lemma adaptSees (s:ℕ)(z:SU.Slot) {q d w:ℕ} {o:Cover} {f:observable K true}{a:ℝ}
    (p:Fixture Y H V G z q d w o s f a) {x:Resident (catalog Y H V G D false (R D))} (u:ExtremeReceipt Y H V G D R x)
    (t: 1/4≤ ‖X x s (restore f)‖): Seen Y H V G D R x s z q d w o f a:=by
  let M := evaluate Y H V G D R x
  let w' : M s f.val= X x s (restore f):= evaluates Y H V G D R x s (restore f)
  have hE:1/4≤‖M s f.val‖:=w'.symm ▸ (show 1/4≤ ‖X x s (restore f)‖ from t)
  let v:= consistency Y H V G D R x (Sen o (payout d q w)) s
  have hv : ¬CF.Pannier.Chancel.Parcel K (Window.family z) (booty o d q) (Sen o (payout d q w)) (M s) := by
    intro g; rw [show M s f.val=0 from v.detects p.anchors.1 g p.dressed, norm_zero] at hE; norm_num at hE
  refine ⟨p, fun j b=> fiber_mean Y H V G j false (R j) D (R D) x b, ?_, fun s t=>consistency Y H V G D R x t s, hE,hv,u,?_,?_⟩
  · intro r j c
    exact (placed_sampling Y H V G j false (R j) D (R D) x (s+r) _ c).trans ((at_refine Y H V G false D (R D) x s (restore f) r).trans w'.symm)
  · intro G' u t
    rw [show G' f.val=0 from u.detects p.anchors.1 t p.dressed, sub_zero]
    exact hE
  unfold CF.Pannier.Chancel.Parcel at hv; push Not at hv
  obtain ⟨a,u,f,t,h⟩ := hv
  refine ⟨a,f,u,t,v.footprint p.anchors.1 u,norm_pos_iff.mpr ?_⟩
  rw [show M s a=0 from v.footprint p.anchors.1 u,mul_zero] at h; exact h

open Set Reliance.ShortWave
-- curvature diagnostic applied simultaneously any contained face. real geometry one cabin fits all.
def catalogueFaces (S:Finset Cover): Finset (Face ℤ):= Finset.filter (fun i:Face ℤ => restsOn {i} S) (S.product Finset.univ)
lemma accounted_f (S:Finset Cover)(i:Face ℤ): i∈catalogueFaces S↔ restsOn {i} S:= by
  constructor; · intro x; exact (mem_filter.mp x).2
  exact fun x=> mem_filter.mpr ⟨mem_product.mpr ⟨restsC {i} x i (mem_singleton_self i),mem_univ _⟩,x⟩
lemma centreCounts (o:Cover)(n:ℕ)(h:1≤n) : (catalogueFaces (Sen o n)).Nonempty:=by
  let u:= nodeC o
  let F:Face ℤ:= (u,⟨(0,1),by decide⟩)
  refine ⟨F,(accounted_f ..).2 ?_⟩
  intro i v x p; obtain rfl:=mem_singleton.mp v
  refine mem_image.mpr ⟨x-u,?_,sub_add_cancel ..⟩
  change x∈ (visits u (square 0 1)).toFinset at p; apply box_test.mpr
  simp [visits,square,Step.vec,posDir,negDir] at p
  constructor
  all_goals (intro i; fin_cases i <;> rcases p with (p|p|p|p|p) <;> subst x <;> norm_num [step] <;> omega)
lemma feudal (S:Finset Cover): restsOn (catalogueFaces S) S:=fun i h=> (accounted_f S i).1 h i (mem_singleton_self _)

private lemma cabin_shrinks (S:Finset Cover) (c:ℝ) (p:0<c): ∀ᶠ s in atTop, SupportedPhysically Λ l s S (Tapestry.cabin c) := by
  have ht:Tendsto (Tapestry.precisionAt Λ) atTop atTop:= tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (show 1 < Λ.R.L.val from (by linarith [Λ.R.coarse])))
  refine (eventually_all_finset S).mpr fun x _ => ?_
  let A(v:Axis):ℝ:= |(x v:ℝ)|+ reserve Λ l
  have h:∀ᶠ s in atTop,∀ v:Axis,A v ≤ c*Tapestry.precisionAt Λ s:= Filter.eventually_all.mpr fun v=> (Tendsto.const_mul_atTop' p ht).eventually_ge_atTop (A v)
  filter_upwards [h] with s hd y hy v; change |y v/2|≤ c
  have he: |Tapestry.precisionAt Λ s*y v| ≤ A v:=by
    apply le_trans (b:=|Tapestry.precisionAt Λ s*y v- (x v:ℝ)|+|(x v:ℝ)|); convert abs_add_le (Tapestry.precisionAt Λ s*y v-(x v:ℝ)) (x v:ℝ) using 1; rw [sub_add_cancel]; unfold A; linarith only [hy v]
  rw [abs_mul,abs_of_pos (Tapestry.positiveScale ..)] at he; have hv:=hd v
  have hh:=Tapestry.positiveScale Λ s; rw [abs_div,abs_of_pos (by positivity : (0:ℝ)<2)]; nlinarith

variable (Z J γ : ℝ)
variable {q d w :ℕ}
variable (x:Resident (catalog Y H V G D false (R D)))
local notation "S₀" o:max=> Sen o (payout d q w)
-- Make threshold simultaneous across all slots. applies in proximity AND across all extensions of the hierarchy.
structure Simultaneous (q d w:ℕ)(s:ℕ) (o:Cover) (a:ℝ) (n:ℕ):Prop where
  buffer : 0<a
  faces : (catalogueFaces (Sen o (payout d q w))).Nonempty
  epsilon : 0<aperture n
  offers (z:SU.Slot): ∃ f, Seen Y H V G D R x s z q d w o f a ∧ ‖E s f.val‖>1/2 ∧ ‖X x s (restore f)‖>1/2 ∧
      ∀ m v, ∀ i: Face ℤ, restsOn {i} (Sen o (payout d q w))→ SU.group.chord (faceValue (onC _ v.1) i) ≤ aperture n → f.val m v=0

local notation "o₀"=> scheduled (payout d q w) (addgap K)
theorem allOffers (t:ExtremeReceipt Y H V G D R x) (p:Papal.Policy Y H q d w Z J γ) {s:ℕ}(a:ℝ)(e:0<a)
    (v:SupportedPhysically Λ l s (S₀ o₀) (Tapestry.cabin a)) (c:Fair Y H V G D (R D) x d q w s):
    ∀ᶠ n in atTop, Simultaneous Y H V G D R x q d w s o₀ a n :=by
  let S:= S₀ o₀; let U:=catalogueFaces S
  let P(n:ℕ)(z:SU.Slot):Prop:= ∃ f, Seen Y H V G D R x s z q d w o₀ f a ∧ ‖E s f.val‖>1/2 ∧ ‖X x s (restore f)‖>1/2 ∧ ∀ m v,∀ i:Face ℤ,restsOn {i} S → SU.group.chord (faceValue (onC _ v.1) i)≤aperture n → f.val m v=0
  have h(z:SU.Slot):∀ᶠ n in atTop,P n z:= by
    obtain ⟨F,g,b,p',v'⟩:= c.attends z
    let d':= FilTest b.first|>.widen
    let f(n:ℕ):= movedF Y H S U n F d' (feudal S)
    filter_upwards [(prices_selected Y H V G D S U s (R D) (feudal S) F d' x).norm.eventually (lt_mem_nhds p'), (prices_irr Y H V G D S U s (R D) (feudal S) F d').norm.eventually (lt_mem_nhds v')] with n bQ eQ
    have hE':3/4 < ‖E s (f n).val‖:= eQ
    have hE:1/2 < ‖E s (f n).val‖:=lt_trans (by norm_num) hE'
    have h:(f n).val ∈ Filigree K (Window.family z) (booty o₀ d q) S:= preserveFil K z S (cutC S U n (feudal S)) b.first
    have hw := takeFixture (F:=f n) Y H V G z o₀ p.old h e v (le_trans (by norm_num) hE.le)
    have ht : ‖X x s (restore (f n))‖>1/2:= bQ; exact ⟨_,adaptSees Y H V G D R s z hw t (le_trans (by norm_num) ht.le),hE,ht,fun m u i w he=> stops K U n F.val m u ((accounted_f ..).2 w) he⟩
  filter_upwards [Filter.eventually_all.mpr h] with i hu
  exact ⟨e,centreCounts o₀ _ p.positive.2.2,aperture_pos i,hu⟩

-- arbitrary small *region* (more than one fixed test); o fixed in level-f coordinates.
theorem allRegion (p:Papal.Policy Y H q d w Z J γ):
    ∃ x:Resident (catalog Y H V G D false (R D)), ExtremeReceipt Y H V G D R x ∧
      ∀ a> (0:ℝ), ∃ᶠ s in atTop, ∀ᶠ n in atTop, Simultaneous Y H V G D R x q d w s o₀ a n := by
  obtain ⟨x,t,v⟩:= jointly Y H V G D Z J γ R p
  exact ⟨x,t,fun a e=> (v.and_eventually (cabin_shrinks (l:=l) (S₀ o₀) a e)).mono (fun r hv=>allOffers Y H V G D R Z J γ x t p a e hv.2 hv.1)⟩
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.allRegion
