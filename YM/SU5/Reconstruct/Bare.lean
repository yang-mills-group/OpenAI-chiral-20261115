import VerifiedSatinSelectedSectors
/-!
# Bare stencil dictionary for the chosen history

Given a finite polynomial in physical resolution fields (not assuming
continuity or ignoring the second link argument at effective scales!), show
that it can be measured using ONE microscopic SU link configuration and the
actual chiral Fock sector on the launch at every paid entry of this Satin
course. The operator obtained need not be regulator independent at the top;
it is the cutoff-dependent prescription for this fixed physical observable.
The supports will be paid on every resolution, including moving top, from
the SAME physical budget. No stochastic positivity assumed, no replacing a
projection/determinant phase by a positive weight. This is for identifying
what our later OS test-field construction is built from. Not a claim that an
individual insertion is a pointlike continuum field in real time.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 270000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H

section measure
variable {n:Side}
/-- Read out a joint effective mark as a function of just one set of links, by the
**diagonal**, for use at launch (not a rule valid at interim levels). -/
def diagMark (f:Mark n) : Evaluation n := fun x => f (x,x)

theorem diagAt {S:Finset (Site (More n))} {f:Mark n} {b:Bool} (p:AtSupport b S f) :
    AtSupport b S (toMark (diagMark f)) := by
  refine ⟨Env.along (g:=fun (x:Fields n) => (x.1,x.1)) p.env
    (measurable_fst.prodMk measurable_fst), fun x y v _ => p.dep (x.1,x.1) (y.1,y.1) v v, fun x => p.allV (x.1,x.1)⟩

-- gauge on the actual shared group acting on matter Slot, not global groups per copy
lemma diag_cov {f:Mark n} (p:covariant f) : covariant (toMark (diagMark f)) :=
  fun g x => p g (x.1,x.1)

variable (i k : ℕ)
local notation "N" => side Y i (Y.uv k)
local notation "w" => (Y.voyage i).CapeT (Y.uv k)
local notation "Q" => (((Y.voyage i).X (Y.uv k)).gram (Y.uv k))


lemma diag_integrand (f:Mark (side Y i (Y.uv k))) (x:Orbit (side Y i (Y.uv k))) :
    acts (f (drawn ((Y.voyage i).CapeT (Y.uv k)) x))
      (denZ (((Y.voyage i).X (Y.uv k)).gram (Y.uv k)) Λ.U ((Y.voyage i).CapeT (Y.uv k)) x) =
    acts (diagMark f x.1) (Vale.capP («K»:=Λ.K) Λ.U (Q).beta (Y.meter.a (Y.uv k)) x.1) := by
  rw [Y.whole i k x]
  by_cases p : flags (Y.meter.a (Y.uv k)).threshold x.1 = ∅
  · let D := Y.history i k
    have hx : (Y.voyage i).CapeT (Y.uv k) x = x.1 :=
      Vale.Grace.Robes.solar x w (D.roof (Y.uv k)).paid (Y.meter.a (Y.uv k)) (D.pole (Y.uv k)) p
    change acts (f (x.1, (Y.voyage i).CapeT (Y.uv k) x)) _=_
    rw [hx]; rfl
  simp only [Vale.capP, Set.indicator_of_notMem (show x.1∉{v:Pane N| flags (Y.meter.a (Y.uv k)).threshold v=∅} from p),map_zero]
/-- A single SU configuration suffices at the top. `A` is an even chiral
mark with all representations in the same exterior algebra (when used here). -/
def bareAmplitude (A: Evaluation (side Y i (Y.uv k))) (U : Pane (side Y i (Y.uv k))) : ℂ :=
  inner ℂ (Dial.mateK _)
    (acts (A U) (Vale.capP («K»:=Λ.K) Λ.U (Q).beta (Y.meter.a (Y.uv k)) U))

-- Push-forward the honest integrable signed read; no abstract disintegration
private lemma firstIntegral (F:Pane n → ℂ) (h: Integrable (fun x:Orbit n=> F x.1) (city n)) :
    Integrable F (prior SU.group (More n)) ∧
    (∫ x:Orbit n, F x.1 ∂city n)=(∫ u:Pane n,F u ∂prior SU.group (More n)) := by
  let a := prior SU.group (More n)
  let b := depot n
  change Integrable _ (Measure.prod a b) at h
  constructor
  · simpa only [integral_const,probReal_univ,one_smul] using h.integral_prod_left
  change (∫ x:Orbit n,F x.1 ∂a.prod b)=_
  rw [integral_prod _ h]; simp [a]

lemma income (f: Mark (side Y i (Y.uv k))) (x:Orbit (side Y i (Y.uv k))) :
    inner ℂ (Dial.mateK _)
      (acts (f (drawn ((Y.voyage i).CapeT (Y.uv k)) x)) (denZ Q Λ.U w x)) =
      bareAmplitude Y i k (diagMark f) x.1 :=
  congrArg (fun y=>inner ℂ (Dial.mateK _) y) (diag_integrand Y i k f x)

lemma partitionIncome (q:(Y.voyage i).kick ≤ k) :
    Integrable (bareAmplitude Y i k 1) (prior SU.group (More (side Y i (Y.uv k)))) ∧
    partitionZ Q Λ.U w = ∫ U:Pane N, bareAmplitude Y i k 1 U ∂prior SU.group (More N) := by
  have hi := (Tapestry.funds Y (Y.uv k) i k (AtSupport.oneM (n:=side Y i (Y.uv k)) ∅).env q le_rfl).1
  change Integrable (fun x:Orbit (side Y i (Y.uv k))=> inner ℂ _ (acts ((1: Mark (side Y i (Y.uv k))) (drawn w x)) (denZ Q Λ.U w x))) _ at hi
  simp_rw [income] at hi
  obtain ⟨t,e⟩ := firstIntegral (bareAmplitude Y i k 1) hi
  refine ⟨t, Eq.trans ?_ e⟩
  unfold partitionZ
  apply integral_congr_ae
  filter_upwards [] with x
  have h:= income Y i k 1 x
  rw [Pi.one_apply, act_one] at h
  exact h

lemma compassIncome {f:Mark (side Y i (Y.uv k))} (p:Envelope f) (q:(Y.voyage i).kick ≤ k) :
    let μ:= prior SU.group (More (side Y i (Y.uv k))); let A:=diagMark f
    Integrable (bareAmplitude Y i k A) μ ∧
    (∫ U:Pane N, bareAmplitude Y i k 1 U ∂μ) ≠0 ∧
    Journey.compass Y i k (Y.uv k) f = (∫ U:Pane N,bareAmplitude Y i k A U∂μ)/(∫ U:Pane N, bareAmplitude Y i k 1 U ∂μ) := by
  intro μ A
  obtain ⟨t,u,v⟩:= Tapestry.funds Y (Y.uv k) i k p q le_rfl
  simp_rw [income] at t v
  obtain ⟨l,e⟩ := firstIntegral _ t -- implicit n may infer
  rw [partitionIncome Y i k q|>.2,e] at v
  exact ⟨l,(partitionIncome Y i k q).2 ▸ u,v⟩
end measure

section budgets
variable (i k j : ℕ)
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "D" i:max k:max=> tidalDressing Y H i k
local notation "t₀" i:max=> side Y i j
local notation "B" => handstamp

lemma finish_location {U:Set RSpace} (f:sequenceOf (tent Y H))
    (v:∀ i:ℕ, f i∈keep Λ l i K true (handstamp U)) :
    ∃ S:Finset Cover, SupportedPhysically Λ l j S U ∧
      ∀ m t:ℕ, Pay Y j m t → AtSupport false (Satin.region S (side Y m j))
        (attire ((tidalDressing Y H m t).finish j f)):= by
  induction j with
  | zero =>
    obtain ⟨S,p,t⟩:= v 0
    refine ⟨S,t,fun m n _=>?_⟩
    exact exhibited Y H 0 m S ((Tapestry.locates ..).1 p)
  | succ j ih=>
    obtain ⟨S,h,p⟩:=ih
    obtain ⟨T,v,g⟩:= v (j+1)
    let a:= followBox (Λ:=Λ) (l:=l) S
    refine ⟨a ∪ T,unionPrinted Λ l (j+1) a T (handstamp U) h.step g,fun m t q=>?_⟩
    have hu:= ascendSupport Y j m t S q (p m t ⟨q.1,Nat.le_of_lt q.2⟩)
    let F: Ward (side Y m j):= (tidalDressing Y H m t).finish j f
    change AtSupport false (Satin.region _ _) (attire ((music Y j m t) F * roving Y H _ m (f _)))
    rw [attire_mul,music,flowing,roamsAttire]
    have Ht:= (exhibited Y H (j+1) m T ((Tapestry.locates ..).1 v))
    exact (hu.mono (Finset.image_subset_image Finset.subset_union_left)).mulM
      (Ht.mono (Finset.image_subset_image Finset.subset_union_right))

lemma breathing_location {U:Set RSpace} {a:Set ℕ} {x: O}
    (p:x∈jetty Λ l K true (handstamp U) (a∩ Set.Iic j)) :
    ∃ S:Finset Cover, SupportedPhysically Λ l j S U ∧
      ∀ m t:ℕ, Pay Y j m t→ AtSupport false (Satin.region S (side Y m j))
        (attire (breathing Y H j m t x)):= by
  apply boarded (P:={f| Officer (a∩ Set.Iic j) (fun i=> keep Λ l i K true (handstamp U)) f})
    (M:=fun x=> ∃ S:Finset Cover, SupportedPhysically Λ l j S U ∧ ∀ m t:ℕ, Pay Y j m t→
      AtSupport false (Satin.region S (side Y m j)) (attire (breathing Y H j m t x))) ?_ ?_ ?_ ?_ p
  · intro f v; change Officer _ _ _ at v
    obtain ⟨S,w,c⟩ := finish_location Y H j f v.observes
    refine ⟨S,w,fun m t p=>?_⟩
    change AtSupport _ _ (attire (breathing Y H j m t (pureShot K f)))
    rw [breathing_pure _ _ _ _ _ f (v.visible _ _ Set.inter_subset_right)]
    exact c _ _ p
  · refine ⟨∅,fun _ q=> absurd q (Finset.notMem_empty _),fun m t _=>?_⟩
    rw [map_zero]; exact AtSupport.zeroM
  · intro x y _ _ hx hy
    obtain ⟨S,g,f⟩:= hx; obtain ⟨T,h,e⟩:= hy
    refine ⟨S∪T, unionPrinted Λ l j S T (handstamp U) g h,fun m t v=>?_⟩
    rw [map_add,attire_add]
    exact ((f m t v).mono (Finset.image_subset_image Finset.subset_union_left)).addM
      ((e m t v).mono (Finset.image_subset_image Finset.subset_union_right))
  intro z x _ wx; obtain ⟨S,w,p⟩:=wx
  refine ⟨S,w,fun m t v=>?_⟩
  rw [map_smul,attire_scale]; exact (p m t v).smulM _

/-- A physical polynomial at finite height gives one actual cutoff-scale experiment:
measure this Borel function of links, with only the chiral letters acting on
one Fock space. -/
def atCutoff (x:Altitude.Cloud (Dome (tent Y H))) : Evaluation (side Y i (Y.uv k)) :=
  diagMark (attire (breathing Y H (Y.uv k) i k x))

lemma tallerJets {x: O}{U : Set RSpace}{a:Set ℕ}
    (p: x ∈ jetty Λ l K true (handstamp U) (a∩ Set.Iic j)) {t:ℕ}(h:j≤t) : x ∈ jetty Λ l K true (B U) (a∩ Set.Iic t):=
  admits Λ l K true _ _ _ _ (Set.inter_subset_inter_right a (Set.Iic_subset_Iic.mpr h)) Set.Subset.rfl p

lemma top_location {U:Set RSpace}{a:Set ℕ}{wide:Bool}{x : O}
    (p:x∈circum Λ l K wide U (a∩ Set.Iic j)) (q:Pay Y j i k) :
    ∃ S: Finset Cover, SupportedPhysically Λ l (Y.uv k) S U ∧
      AtSupport false (Satin.region S (side Y i (Y.uv k))) (toMark (atCutoff Y H i k x)):= by
  obtain ⟨S,v,e⟩:= breathing_location Y H (Y.uv k)
    (tallerJets Y H j ((well_spec ..).1 (wellWider Λ K l wide (B U) _ p)).1 q.2)
  exact ⟨S,v,diagAt (e _ _ ⟨q.1,le_rfl⟩)⟩

lemma relatedHeight {U:Set RSpace} {a:Set ℕ}{wide:Bool}{x: O}
    (p:x∈circum Λ l K wide U (a ∩ Set.Iic j)){t:ℕ} (q:j ≤ t) : x ∈ boardedDB K t := by
  exact jettyBan Λ l K true (handstamp U) a t
    (tallerJets Y H j ((well_spec ..).1 (wellWider Λ K l wide _ _ p)).1 q)

lemma colorAtCutoff {U:Set RSpace} {a:Set ℕ}{wide:Bool} {x : O}
    (p:x∈ circum Λ l K wide U (a∩ Set.Iic j)) (q:Pay Y j i k) :
    covariant (toMark (atCutoff Y H i k x)):=
  diag_cov (paid_coherence Y H i k (Y.uv k) ⟨q.1,le_rfl⟩ x p (relatedHeight Y H j p q.2))

lemma identifyRevenue {x: O} (p:x∈ boardedDB K j)
    (q:Pay Y j i k) :
    let μ:= prior SU.group (More (side Y i (Y.uv k)))
    Integrable (bareAmplitude Y i k (atCutoff Y H i k x)) μ ∧
    (∫ U:Pane (side Y i (Y.uv k)), bareAmplitude Y i k 1 U ∂μ)≠0 ∧
    taking Y H i k x = (∫ U:Pane (side Y i (Y.uv k)), bareAmplitude Y i k (atCutoff Y H i k x) U ∂μ) /
      (∫ U:Pane (side Y i (Y.uv k)),bareAmplitude Y i k 1 U ∂μ) := by
  intro μ
  rw [taking_phys Y H (Y.uv k) _ _ _ ⟨q.1,le_rfl⟩ (Altitude.climbs _ q.2 p)]
  exact compassIncome Y _ _ (Ward.signs _).env q.1
end budgets
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
