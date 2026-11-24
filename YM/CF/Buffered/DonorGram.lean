import YM.CF.Py.Fuse
import YM.CF.Buffered.Microscopic
import YM.CF.Buffered.Margin
import YM.CF.Buffered.RiseReflect

/-!
# The actual numerator across n FiniteGaugeData Block steps

One-forest push, including all auxiliary variables, iterated on gauge sites
`(ratio (apt ...)).embed`. Prove theorem **for the physical tower** with
needed inputs from history grants, stated generally (no bounds on betas or
B0 here). Will apply to the heat trajectory with fixed B=patch.L^b0 and
j and StepData from the chosen FiniteGaugeData patch and teller.
-/
set_option autoImplicit false
set_option maxHeartbeats 640000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window Vale Girt
open Py (Vestal Cape)
open Reed (Fine think)
open Advance Heat
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ}
variable (P : Grasp Y B e) (X : Vestal m B L) (R : Cape m B L) (q : Chi) (d : ℝ)
variable (n : ℕ) (Q : ℕ → Haro.SpaceM)
local notation "ℒ" => Vale.cell m B L
local notation "𝐺" => Vale.apt m B L
local notation "𝐶" => Vale.mesh m L
-- StepData at actual size. Avoid `variable` with local notations inside.
abbrev Steps (m B L : Side) := ∀ i : ℕ, StepData (More (cell m B L i)) (More (cell m B L (i+1)))
variable (A : Steps m B L) (s : ℤ) (i : Axis)
def planeAt (s : ℤ) (L : Side) (x : ℕ) := (L.val:ℤ)^x * s
lemma step_plane (k : ℕ) : (L.val:ℤ)*planeAt s L k = planeAt s L (k+1) := by simp [planeAt,pow_succ',mul_assoc]
local notation "r" => planeAt s L
-- expected numerator and normalized uses below
structure Granted (J : ℕ) : Prop where
  branch (k : ℕ) (h : k<n) : (A k).patch.Branches (A k).kernel SU.group
  aligned (k : ℕ) (h : k<n) : (A k).ratio=ratio (apt m B L k)
  radius (k : ℕ) (h : k<n) : (A k).patch.J=J
  grant (k : ℕ) (h : k<n) : Nonempty (Girt.BaseL P (apt m B L k) (X (k+1)) (R k) (R (k+1)) q d)
  noTies (k : ℕ) (h : k≤n) : Rue.IsleB SU.group (X k).p.threshold
  wears (k : ℕ) (h : k<n) (V : Orbit (cell m B L k)) (v : Rue.FleetS (X k).p.threshold V.1) :
     Scree.stove P (R k) (X (k+1)) (R (k+1)) (apt m B L k) (A k) q d (Q k).val V=denZ (X k) P (R k) V
variable {D J w U : ℕ} (v : Stencil.LaurentRadius j L D) (L' : 3 ≤ L.val) (T : Granted P X R q d n Q A J)
-- may use smaller w than r₂ from readiness, no fixed-scale mode restrictions
variable (t : ∀ k<n,LoomLaw (R k) w) (p : Margin L D w J U)

-- denominator-friendly cover advancement, any number of products DO NOT assert same-side multiplications
def nextMark (k : ℕ) (f : Mark (cell m B L k)) : Mark (cell m B L (k+1)) :=
  pushMark (apt m B L k) (A k) j (Q k).val (X (k+1)).J.M ho q d (X (k+1)).beta (R k) f
def advanceMark (f : Mark (cell m B L 0)) (k : ℕ) : Mark (cell m B L k) := match k with
 | 0=>f
 | k+1=> nextMark (j:=j) (ho:=ho) X R q d Q A k (advanceMark f k)
local notation "tape" => advanceMark (j:=j) (ho:=ho) X R q d Q A
local notation "rise₁" => nextMark (j:=j) (ho:=ho) X R q d Q A
include P L' T v t p
lemma mark_tape {f : Mark (cell m B L 0)} (h : AtSupport false (band (cell m B L 0) i s U) f) (k : ℕ) (u : k ≤ n) : AtSupport false (band (cell m B L k) i (planeAt s L k) U) (tape f k) := by
  induction k with
  | zero=> simpa only [advanceMark,planeAt,pow_zero,one_mul] using h
  | succ k ih=>
    specialize ih (by omega)
    obtain ⟨g⟩:= T.grant k u; obtain ⟨V,b,c,Y,l⟩:= g.cap
    let K:= apt m B L k
    have hz:= surround K (A k) j (Q k).val (X (k+1)).J.M ho q d (X (k+1)).beta (R k) (g.power.symm ▸ v) Y.bill (T.branch k u) g.legal.1 g.legal.2 _ ih (t _ u) (T.aligned k u)
    rw [T.radius k u] at hz; rw [advanceMark, ←step_plane s]; exact hz.mono (margin_band i _ p K rfl L')
include P
-- manuscript factorization to mark's product of advancements. identity before any limits.
lemma tape_ref {f g : Mark (cell m B L 0)} (h : AtSupport false (band (cell m B L 0) i s U) f) (a : AtSupport false (band (cell m B L 0) i s U) g) (k : ℕ) (u : k ≤ n) : tape (reflMark i s f*g) k=reflMark i (planeAt s L k) (tape f k)* tape g k := by
  induction k with
  | zero=> simp [planeAt,advanceMark]
  | succ k ih=>
    specialize ih (by omega); let K:= apt m B L k; obtain ⟨g'⟩:= T.grant k u; obtain ⟨V,b,c,Y,l⟩:= g'.cap
    have hf:=mark_tape P X R q d n Q A s i v L' T t p h k (by omega); have hx:=mark_tape P X R q d n Q A s i v L' T t p a k (by omega) 
    have J':= separated_mult K (A k) j (Q k).val (X (k+1)).J.M ho q d (X (k+1)).beta (R k) (g'.power.symm ▸ v) Y.bill (T.branch k u) g'.legal.1 g'.legal.2 _ _ (hf.refl i (planeAt s L k)) hx (t _ u) (fun x X y Y=> margin_separate i (planeAt s L k) p x y X Y)
    have hg:= rising K (A k) j (Q k).val (X (k+1)).J.M ho q d (X (k+1)).beta (R k) i (planeAt s L k) (T.aligned k u) hf (T.branch k u) Y (g'.power.symm ▸ v) g'.legal.1 g'.legal.2
    rw [advanceMark, ih]; change pushMark K _ _ _ _ _ _ _ _ _ _=_; rw [J',hg]; change reflMark i (L.val * planeAt s L k) _ * _= _; rw [step_plane, advanceMark,advanceMark]; rfl
omit L' t p
lemma single_num {k : ℕ} {f : Mark (cell m B L k)} (h : AtSupport false univ f) (u : k<n) : markedRead f (R k) (denZ (X k) P (R k)) = markedRead (rise₁ k f) (R (k+1)) (denZ (X (k+1)) P (R (k+1))) := by
  obtain ⟨g⟩:= T.grant k u
  exact identity_step _ g _ (T.branch k u) (T.aligned k u) (Q k) ho v h (((measurePreserving_fst (μ:=prior group (More (cell m B L k))) (ν:=depot (cell m B L k))).quasiMeasurePreserving.ae ((T.noTies k u.le) _)).mono fun x h=> T.wears _ u x h)
include L' t p
lemma tape_num {f g : Mark (cell m B L 0)} (h : AtSupport false (band (cell m B L 0) i s U) f) (a : AtSupport false (band (cell m B L 0) i s U) g) (k : ℕ) (u : k ≤ n) : markedRead (reflMark i s f*g) (R 0) (denZ (X 0) P (R 0))=markedRead (reflMark i (planeAt s L k) (tape f k)* tape g k) (R k) (denZ (X k) P (R k)) := by
  induction k with
  | zero=> simp [advanceMark,planeAt]
  | succ k ih=>
     have hf:=mark_tape P X R q d n Q A s i v L' T t p h k (by omega); have hx:=mark_tape P X R q d n Q A s i v L' T t p a k (by omega)
     let V:=reflMark i (planeAt s L k) (tape f k)*tape g k
     have hg: rise₁ k V=reflMark i (planeAt s L (k+1)) (tape f (k+1))*tape g (k+1):= by unfold V; rw [← tape_ref P X R q d n Q A s i v L' T t p h a k (by omega),←tape_ref P X R q d n Q A s i v L' T t p h a _ u,advanceMark]
     rw [ih (by omega), ←hg]; exact single_num P X R q d n Q A v T (((hf.refl i _).mono (subset_univ _)).mulM (hx.mono (subset_univ _))) u
omit P L' T v t p
variable (z : ℤ)
def squareMark (z : ℤ) (i : Axis) {N : Side} (f g : Mark N) := reflMark i z f*g
structure Donor where
  scroll : Scroll (mesh m L n) B (Brace.northZ (mesh m L n) B)
  pin : Pinning (mesh m L n) B
  heat : ℝ
  warm : 0 ≤ heat
  grants : ∃ a D b : ℝ, ScaleK a D scroll ∧ Budget B e b
  clip : Clip
  top : Eyes P (X n) (R n) pin scroll clip heat
  roof : ∃ (x y : ℝ) (k : ℕ), Roof (cell m B L n) x y k (R n) ∧ (X n).p.threshold ≤ x
variable (M : Donor P X R n)
include P L' T v t p M
local notation "Z" => gaugeShift B z
local notation "afterZ" => ((L.val:ℤ)^n * z)
omit P L' T v t p M in
private lemma is_gaugeShift : planeAt (gaugeShift B z) L n = gaugeShift B ((L.val:ℤ)^n*z) := by unfold planeAt gaugeShift; ring
omit M in
private lemma paidT {f : Mark (cell m B L 0)} (h : AtSupport false (band (cell m B L 0) i Z U) f) : AtSupport false (band (cell m B L n) i (gaugeShift B afterZ) 0) (tape f n) := by
  have he:=mark_tape P X R q d n Q A Z i v L' T t p h n le_rfl; rw [is_gaugeShift] at he; exact he.mono (band_anti _ _ (Nat.zero_le _))

-- Shows actual microscopic plane has address multiple of 4B. In application m even,
-- making its opposite another such. Conclusion checks trace and limit for any m.
theorem donor_layerLimit {f g : Mark (cell m B L 0)} (h : AtSupport false (band (cell m B L 0) i Z U) f) (a : AtSupport false (band (cell m B L 0) i Z U) g) :
    let l := fun u=> transfer M.pin M.scroll M.clip (X n).beta (X n).p.threshold M.heat e i (northZ (mesh m L n) B) u
    Tendsto (fun u=> kernelTrace (u+1) (l u (rephased i afterZ (both (tape g n)))) (kernelStar (u+1) (l u (rephased i afterZ (both (tape f n)))))) atTop (𝓝 (markedRead (squareMark Z i f g) (R 0) (denZ (X 0) P (R 0)))) := by
  intro l; obtain ⟨V,W,w,H,gK⟩:= M.grants; obtain ⟨x,y,k,s,A_⟩:= M.roof
  unfold squareMark; rw [tape_num P X R q d n Q A Z i v L' T t p h a _ le_rfl, is_gaugeShift]
  exact summit_trace P (X n) (R n) M.pin M.scroll M.clip M.heat M.top H gK s A_ (T.noTies n le_rfl) i afterZ _ _ (paidT P X R q d n Q A i v L' T t p z h) (paidT P X R q d n Q A i v L' T t p z a) M.warm

theorem unnormDonor {f : Mark (cell m B L 0)} (h : AtSupport false (band (cell m B L 0) i Z U) f) :
    0 ≤ markedRead (squareMark Z i f f) (R 0) (denZ (X 0) P (R 0)) := by
  obtain ⟨V,W,w,H,gK⟩:= M.grants; obtain ⟨x,y,k,s,A_⟩:= M.roof
  unfold squareMark; rw [tape_num P X R q d n Q A Z i v L' T t p h h _ le_rfl, is_gaugeShift]
  exact summit_gram P _ _ M.pin M.scroll M.clip M.heat M.top H gK s A_ (T.noTies n le_rfl) i afterZ _ (paidT P X R q d n Q A i v L' T t p z h) M.warm
-- normalized Gram once denominator nonzero known separately (e.g. pc-low's absolute bound)
include i z
lemma strictDonor (a : partitionZ (X 0) P (R 0)≠0) : 0 < partitionZ (X 0) P (R 0) := by
  apply lt_of_le_of_ne _ a.symm; have he:=unnormDonor P X R q d n Q A i v L' T t p z M (AtSupport.oneM (band (cell m B L 0) i Z U))
  rwa [squareMark,mul_one,show reflMark i (gaugeShift B z) (1:Mark (cell m B L 0))=1 from funext fun _=> theta_one _, markvac] at he
-- normalize assertion includes cross-reading limit trace paid separately
-- any finite combinations bundled via Mark
noncomputable def atZero (f : Mark (cell m B L 0)) := markedRead f (R 0) (denZ (X 0) P (R 0)) / partitionZ (X 0) P (R 0)
theorem donor (a : partitionZ (X 0) P (R 0)≠0) {f : Mark (cell m B L 0)} (h : AtSupport false (band (cell m B L 0) i Z U) f) :
    0 ≤ atZero P X R (squareMark Z i f f) := div_nonneg (unnormDonor P X R q d n Q A i v L' T t p z M h) (strictDonor P X R q d n Q A i v L' T t p z M a).le
end YM.CF.Buffered
#print axioms YM.CF.Buffered.donor_layerLimit
#print axioms YM.CF.Buffered.donor
