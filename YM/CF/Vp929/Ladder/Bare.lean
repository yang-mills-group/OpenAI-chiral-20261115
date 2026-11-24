import YM.CF.Vp929.Ladder.Geometry

/-! The top arrays, reindex and purchase with two different BudgetPoints. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m m' n n' N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x x' delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k k' : ℕ} {P : Prescription R B}

namespace Branch
variable (P) (A : Branch W m k x N0)
def Represents (p : BudgetPoint) := ∀ b, A.RealQ b →
      denZ (A.gram P b k) U (A.loom k) =ᵐ[city _] denZ (Vale.launch V.L (b.read k).re p _) U (A.loom k)
lemma gram_top (b) : A.gram P b k = construct (A.T.a k) (V.L.path 0) K.top.clip (vanilla _) (b.read k).re
    (A.start (b.read k)).1 0 := by unfold gram chargeLevel; rw [corr_top,Gold.Last.top,Nat.sub_self,offset,dif_neg (lt_irrefl _)]
/-- The unchanged launch. -/
abbrev unchanged (A : Spine W m k) (T : Month x 1 6 2 N0 V W) : Branch W m k x N0 := ⟨A,T,fun _=>0⟩
lemma unchanged_boot (A : Spine W m k) (T : Month x 1 6 2 N0 V W) (b) : (unchanged A T).gram P b k= Vale.launch V.L (b.read k).re (T.a k) _ := by rw [gram_top]; rfl
lemma unchanged_rep (A : Spine W m k) (T : Month x 1 6 2 N0 V W) : (unchanged A T).Represents P (T.a k) := fun b t=> by
  rw [unchanged_boot]
variable {P A}
lemma unchanged_build {A : Spine W m k} {T : Month x 1 6 2 N0 V W} (c : A.Can J q T)
    (e : ∀ y ≥ x, Prices R.L D y) (hp : delay ≤ x) {z : ℝ} (hz : A.last.music z)
    (hx : 8*z ≤ x) : (unchanged A T).Bon J q h D delay := by
  have v:= zero_le_one.trans (e x le_rfl).grade
  have f : Charged (T.a k) (A.last.Q k) K.j R.L.val h (dleaf R.L (hat R.L x k)/1000) 0 :=
    Charged.zero.mono (div_nonneg (e _ (Vale.crown ..)).leaf.le (by norm_num))
  exact ⟨c,hp,e,fun i h=> A.pilot_pays _ hz v hx h,fun b _ =>⟨⟨f,f⟩,fun _=>rfl⟩,fun V _ _ _ _=>holoCorr_const ..⟩

lemma retag_build (u : Retag V U W J h N0 delay) (s : Service V U W J q h D C R0 P N0 delay)
    (A : Spine W m k) {T : Month x 1 6 2 N0 V W} (c : A.Can J q T) (e : ∀ y≥x, Prices R.L D y)
    (hp : delay ≤ x) {z : ℝ} (hz : A.last.music z) (hx : 8*z ≤ x)
    {y : ℝ} (v : delay ≤ y) (hl : y ≤ hat R.L x k) (hu : hat R.L x k ≤ 4/3*y)
    (p : BudgetPoint) (hh : Location.Boot y p) (ht : p.threshold≤J.k) (hi : Rue.IsleB SU.group p.threshold) :
    ∃ F, let B : Branch W m k x N0 := ⟨A,T,F⟩; B.Bon J q h D delay ∧ B.Represents P p := by
  let t:=hat R.L x k; let X:= T.a k; have h':=T.boot k
  have P' : Prices R.L D t:= e _ (Vale.crown ..)
  have hp' (b) (hb : enters t b) : aperture y b := by
    obtain ⟨l,u,v⟩:= hb
    have ht:= P'.grade; have he:= P'.peri
    refine ⟨by linarith,?_⟩
    have hI:= Complex.norm_le_abs_re_add_abs_im b; rw [abs_of_pos (by linarith : 0 < b.re)] at hI; linarith
  obtain ⟨F,hf,fd,H⟩:= u y t v hl hu (mesh m R.L k) (A.loom k) p X hh ⟨h'.1,h'.2.1,h'.2.2.1,h'.2.2.2.1,h'.2.2.2.2⟩ ht (c.pole k) hi (c.isle k)
    (c.cape k).paid (c.cape k).size (ge60 _ _ _ _ c.admissible) (flat_v V 1 2 6 N0 T m c.size k 0)
  let B' : Branch W m k x N0:= ⟨A,T,F⟩
  have hf' (b) (hb : enters t b) : B'.allCorr h k (F b) := by
    have := A.last.top; simp_rw [← this] at hf; exact hf _ (hp' _ hb)
  have hB' : B'.Bon J q h D delay := ⟨c,hp,e,fun i h=> A.pilot_pays _ hz (zero_le_one.trans (e _ le_rfl).grade) hx h,
      fun b he=>⟨hf' _ he, fun e=> by
        let hE:= hp' _ he; have hx: b=(b.re:ℂ):=by apply Complex.ext <;> simp [e]
        rw [hx] at hE ⊢; exact (H _ hE).1⟩,
      fun V t b v e=> fd V t b (fun z hz=> hp' _ (v z hz)) e⟩
  refine ⟨F,hB',fun b hb=>?_⟩
  change denZ (B'.gram P b k) U _ =ᵐ[city _] _; rw [B'.gram_top]; have Tt:= (H _ (hp' _ (hB'.beta_ok s hb k le_rfl).2)).2
  exact ((ae_fleet hi).and (ae_fleet (c.isle k))).mono fun x h=> by
    have B:= Tt x h.1 h.2; rw [hb.coeRe k le_rfl] at B; exact B.symm

private lemma sameBare {p} {F : GramM (mid m B)} {F' : GramM (mid m' B)} {T T'} (u : m=m') (h : HEq T T') {b b' : ℝ} (v : b=b')
    (hf : denZ F U T =ᵐ[city _] denZ (Vale.launch V.L b p _) U T)
    (hf' : denZ F' U T' =ᵐ[city _] denZ (Vale.launch V.L b' p _) U T') : Same U u F T F' T' := by
  subst m' b'; subst_eqs; exact hf.trans hf'.symm

lemma commonTop {A' : Branch W m' k' x' N0} {b b' l p} (u : Under A.toSpine A'.toSpine l)
    (h : A.RealQ b) (t : A'.RealQ b') (e : ∀ i≤k,b.read i=b'.read (i+l)) (H : A.Represents P p) (H' : A'.Represents P p) :
    Same U u.top (A.gram P b k) (A.loom k) (A'.gram P b' k') (A'.loom k') :=
  sameBare u.top (u.height ▸ u.S k) (congrArg Complex.re ((e k le_rfl).trans (congrArg b'.read u.height))) (H _ h) (H' _ t)
end Branch
end YM.CF.Py.Rate
