import YM.CF.Vp929.Stage.Prices
import YM.CF.Py.Chime
import YM.CF.Py.Fuse
import YM.CF.Bloom.Flux

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} (V : Grace K R L)
variable {d : ℝ} {m n N B : Side} (U : Grasp V.U B d) (W : GivenX V U) (J : Robes N V W) (q : Chi)
  {h x : ℝ} (i k : ℕ)
variable {V U} {N0 : ℕ}

/-- Branch data indexed with bottom at 0, whatever period it is using. -/
structure Spine (m : Side) (k : ℕ) where
  last : V.L.Last U W.C m k
  loom : Cape m B R.L
  freq : ℕ → ℝ
namespace Spine
variable {k W} (A : Spine W m k)
def address (i : ℕ) : Location (R:=R) B (mesh m R.L i) (mesh m R.L (i+1)) :=
  { lag := k-1-i
    G := apt m B R.L i
    count := rfl
    sizes := kint m B R.L i
    input := A.last.Q (i+1)
    output := A.last.Q i
    fee := A.last.shift i
    coarse := A.loom i
    fine := A.loom (i+1)
    freq := A.freq i }
@[simp]
lemma movement (i : ℕ) : (A.address i).movement V = A.last.move i := rfl
def pilot (x : ℝ) (i : ℕ) := x - ∑ u∈range i, A.last.move u
lemma pilot_move (i : ℕ) : A.pilot x i = A.pilot x (i+1)+A.last.move i := by unfold pilot; rw [sum_range_succ]; ring
lemma pilot_zero : A.pilot x 0 = x := by simp [pilot]
lemma pilot_pays {z : ℝ} (t : A.last.music z) (hp : 0 ≤ x) (H : 8*z ≤ x) (hi : i ≤ k) :
    3/4 * hat R.L x i ≤ A.pilot x i ∧ A.pilot x i ≤ 3/2 * hat R.L x i := by
  let f:=A.pilot x
  have hk : A.last.Running f := by intro j p; change |A.pilot x j - (A.pilot x (j+1)+A.last.move j)| ≤ _; rw [pilot_move]; simp
  obtain ⟨r,R'⟩:=V.roomZ; have hx:=Vale.spark hk t 0 i (by omega); change |f _-f _-_ * _| ≤ _ at hx; dsimp only [f] at hx; rw [Nat.zero_add,pilot_zero,abs_le] at hx; have hh: (0:ℝ)≤ i:=Nat.cast_nonneg _; unfold hat
  constructor <;> nlinarith only [mul_nonneg hh (Vale.pitch R.L),hx.1,hx.2,hp,H,mul_le_mul_of_nonneg_left r hh, mul_le_mul_of_nonneg_left R' hh]
structure Can (T : Month x 1 6 2 N0 V W) : Prop where
  size : T.q ≤ m.val
  admissible : 61 ≤ m.val
  cape (i : ℕ) : RocketV V (mesh m R.L i) (mesh m R.L (i+1)) U W J (A.loom i) (apt m B R.L i) q
  frequencies (i : ℕ) : Frequency R.L (cell m B R.L i) (A.freq i)
  pole (i : ℕ) : (T.a i).threshold ≤ J.k
  isle (i : ℕ) : Rue.IsleB SU.group (T.a i).threshold

variable {J q} {T : Month x 1 6 2 N0 V W}
protected lemma Can.request {A : Spine W m k} (c : A.Can J q T) (i : ℕ) (hi : i < k) :
    Location.Request V U W J q (A.address i) N0 (hat R.L x i) (T.a i) (T.a (i+1)) := by
  let j:= k-1-i; let h:=T.boot i; let h':=T.boot (i+1)
  have mp:= T.clear c.size j i; have he:= c.size.trans (amplit m B R.L i)
  refine ⟨c.cape i,(c.cape _).paid,(c.cape (i+1)).size,A.last.sound i,?_,⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,
    (hat_step i) ▸ (show Location.Boot (hat R.L x (i+1)) (T.a (i+1)) from ⟨h'.1,h'.2.1,h'.2.2.1,h'.2.2.2.1,h'.2.2.2.2⟩),?_,?_,c.frequencies i,c.pole _,c.pole _,c.isle _,c.isle _⟩
  · intro b F s v p
    refine ⟨Stake.punt_g V j _ (apt m B R.L i) rfl _ ?_ mp.1.size,T.roll i,A.last.pass i hi,A.last.sound (i+1),mp.2.1,h.2.2.1,h'.2.2.1,rfl,rfl,rfl,rfl,rfl,p,h.2.1,?_, h'.2.2.2.2⟩
    · have H:= W.flag.trans (T.large.trans he); change _ ≤ (cell m B R.L i).val*2; omega
    · change (T.a _).B = _; rw [h'.2.1, hat_step]
  · exact flat_v V 1 2 6 N0 T m c.size i j
  have p:= c.admissible.trans (amplit m B R.L i); change _< (cell m B R.L i).val*2; omega
end Spine

variable {W} {J q} {i}
open Location
lemma Request.balance {x n n' N0} {u : Location (R:=R) B n n'} {p p'} (t : u.Request V U W J q N0 x p p')
    {F F'} {b b' v v'} (hb : matchedX (x+billX R.L) b') (hF' : Charged p' u.input K.j R.L.val h (3*dleaf R.L x) F') (Q : SpaceM)
    (hw : ∀ y, Rue.FleetS p.threshold y.1 → denZ (u.buildOut V p b F v) U u.coarse y =
            stove U u.coarse (u.buildIn V p' b' F' v') u.fine u.G (u.step V) q J.d Q.val y) :
    partitionZ (u.buildOut V p b F v) U u.coarse = partitionZ (u.buildIn V p' b' F' v') U u.fine := by
  let A:= u.buildOut V p b F v; let F:= u.buildIn V p' b' F' v'
  have he : StatV V u.G (V.L.mint ..) U W (u.buildOut V p (b'+u.movement V) 0 0) F (V.L.charge u.lag) u.fee 1 x 2 6 := t.statv b' F' 0 v' hb
  obtain ⟨T⟩:= rig V U W J q t.rocket u.fine t.roof F he.sound u.count (ward_m (V.L.mood u.lag) ((show Laurel F K.j h (3*dleaf R.L x) (3*dleaf R.L x) R.L.val from hF'.laurel ..).lot_p le_rfl le_rfl))
  have hB:(u.step V).patch.Branches (u.step V).kernel SU.group := by unfold Location.step; rw [V.L.patch_x]; exact V.L.cloth
  exact balance_F T he.hunt.scaleP hB Q t.isle (fun y h => (hw y h).symm)
end YM.CF.Py.Rate
