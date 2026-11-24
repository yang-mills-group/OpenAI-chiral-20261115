import YM.CF.Vp929.Stage.Real
import YM.CF.Vp929.Budget.Offset

/-! Comparing across changes of tag by matching from the top. -/
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
variable {d : ℝ} {m m' n n' N B : Side} (U : Grasp V.U B d) {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x x' delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k k' : ℕ} {P : Prescription R B}

/-- Equality of fields almost everywhere, across the reindexing. -/
def Same (u : m=m') (X : GramM (mid m B)) (S : Scree.Loom (mid m B)) (X' : GramM (mid m' B))
    (S' : Scree.Loom (mid m' B)) : Prop := denZ X U S =ᵐ[city _] denZ (m:=m) (u.symm ▸ X') U (u.symm ▸ S')
lemma Same.partition {u : m=m'} {X S X' S'} (p : Same U u X S X' S') : partitionZ (m:=m) X U S=partitionZ (m:=m') X' U S' := by
  subst m'; unfold partitionZ; exact integral_congr_ae (p.fun_comp _)

private lemma service_same {w : Location (R:=R) B m n} {w' : Location (R:=R) B m' n'} (u₀ : m=m') (u₁ : n=n') (e : HEq w w')
    (s : Service V U W J q h D C R0 P N0 delay) {p p₁ p' p₁'} (t : Location.Request V U W J q w N0 x p p₁) (t' : Location.Request V U W J q w' N0 x' p' p₁')
    (hx : delay ≤ x) (hx' : delay ≤ x') (hh : 0 ≤ h) {b b' : ℝ} (pE : b=b') (hb : enters (x+billX R.L) b) (hb' : enters (x'+billX R.L) b') {F F' v v'} (hF : Charged p₁ w.input K.j R.L.val h (3*dleaf R.L x) F) (hF' : Charged p₁' w'.input K.j R.L.val h (3*dleaf R.L x') F')
    (pI : Same U u₁ (w.buildIn V p₁ b F v) w.fine (w'.buildIn V p₁' b' F' v') w'.fine) :
    let Z:= (P m n w x p p₁).output V w p b F v; let Z':= (P m' n' w' x' p' p₁').output V w' p' b' F' v'
    (P m n w x p p₁).wave b F=(P m' n' w' x' p' p₁').wave b' F' ∧
    Z.beta=Z'.beta ∧ Same U u₀ Z w.coarse Z' w'.coarse ∧
    |Z.v.re-Z'.v.re| ≤ (dleaf R.L x/1000+dleaf R.L x'/1000)*sites (mid m B) := by
  subst m'; subst n'; replace e:=eq_of_heq e; subst w'; subst b'
  obtain ⟨u,v,H⟩:= s.compare _ _ _ _ _ _ _ _ _ hx hx' t t' b F F' v v' hb hb' hF hF' pI; intro Z Z'; refine ⟨u,v, ?_,?_⟩
  · exact ((ae_fleet t.isle).and (ae_fleet t'.isle)).mono fun x v=> H x v.1 v.2
  have ha : 0 ≤ 3*dleaf R.L x := by
    obtain ⟨f,y,q⟩:= hF.inc.weight; refine le_trans ?_ (q 0)
    apply Finset.sum_nonneg; intro i _; split; next => exact mul_nonneg (Real.exp_pos _).le (Roots.gradeE _ _ (y i) hh)
    next => exact le_rfl
  have hA : 0 ≤ 3*dleaf R.L x' := by
    obtain ⟨f,y,q⟩:= hF'.inc.weight; refine le_trans ?_ (q 0)
    apply Finset.sum_nonneg; intro i _; split; next => exact mul_nonneg (Real.exp_pos _).le (Roots.gradeE _ _ (y i) hh)
    next => exact le_rfl
  have c:= ((s.provides _ _ _ _ _ _ hx t).cost (b:ℂ) (F,0) hb ⟨hF,Charged.zero.mono ha⟩).1.1.toCost
  have c':= ((s.provides _ _ _ _ _ _ hx' t').cost (b:ℂ) (F',0) hb' ⟨hF',Charged.zero.mono hA⟩).1.1.toCost
  exact compare_real U Z.beta Z'.beta (J.gran.trans t.rocket.size) (fun y=> (t.rocket.paid.paid y).shrink J.hr.le) hh hh c c' H
variable {U}
/-- Reindex conservatively across the step meshes. -/
structure Under (A : Spine W m k) (A' : Spine W m' k') (l : ℕ) : Prop where
  height : k+l=k'
  mesh (i) : Vale.mesh m R.L i=Vale.mesh m' R.L (i+l)
  Q (i) : HEq (A.last.Q i) (A'.last.Q (i+l))
  S (i) : HEq (A.loom i) (A'.loom (i+l))
  fee (i) : i<k → A.last.shift i=A'.last.shift (i+l)
  freq (i) : i<k → A.freq i=A'.freq (i+l)
namespace Under
variable {A : Spine W m k} {A' : Spine W m' k'} {l : ℕ} (p : Under A A' l)
include p
lemma meshT (i j) (u : i+l=j) : Vale.mesh m R.L i=Vale.mesh m' R.L j := u ▸ p.mesh i
lemma top : Vale.mesh m R.L k=Vale.mesh m' R.L k' := p.meshT _ _ p.height
lemma Address (i j) (u : i<k) (hs : i+l=j) : HEq (A.address i) (A'.address j) := by
  have he : ∀ {m m' n n' : Side} {w : Location (R:=R) B m n} {w' : Location (R:=R) B m' n'}, m=m' → n=n' → w.lag=w'.lag → HEq w.output w'.output → HEq w.input w'.input → w.fee=w'.fee → HEq w.coarse w'.coarse → HEq w.fine w'.fine → w.freq=w'.freq → HEq w w' := by
    rintro m _ n _ w w' rfl rfl v a b c d e f; rw [heq_eq_eq] at *; exact Location.extFields V v a b c d e f
  have hh:i+1+l=j+1:=by omega
  exact he (p.meshT _ _ hs) (p.meshT _ _ hh) (show k-1-i=k'-1-j by have := p.height; omega) (show HEq (A.last.Q i) (A'.last.Q j) from hs ▸ p.Q _) (show HEq (A.last.Q _) (A'.last.Q (j+1)) from hh ▸ p.Q _) (show A.last.shift i=A'.last.shift j from hs ▸ p.fee i u) (show HEq (A.loom i) (A'.loom j) from hs ▸ p.S _) (show HEq (A.loom _) (A'.loom (j+1)) from hh ▸ p.S _) (show A.freq i=A'.freq j from hs ▸ p.freq i u)
omit p in
lemma refl(A : Spine W m k) : Under A A 0 := ⟨rfl,fun _=> rfl,fun _=>HEq.rfl,fun _=>HEq.rfl,fun _ _=>rfl,fun _ _=>rfl⟩
end Under
namespace Branch
variable {A : Branch W m k x N0} {A' : Branch W m' k' x' N0} {z z' : ℝ} {b : Bet k} {b' : Bet k'}
local notation "M" => cell m B R.L
local notation "X" => hat R.L x
local notation "X'" => hat R.L x'
local notation "E" => A.toSpine
local notation "E'" => A'.toSpine
local notation "Z" => A.gram P b
local notation "Z'" => A'.gram P b'
variable (hh : 0≤h) (p : Service V U W J q h D C R0 P N0 delay)
    {l : ℕ} (u : Under A.toSpine A'.toSpine l) (hn : A.Bon J q h D delay) (hm : A'.Bon J q h D delay)
    (t : A.RealQ b) (t' : Solved P A' z' b') (H : ∀ i ≤ k, b.read i=b'.read (i+l))
    (he : Same U u.top (A.gram P b k) (A.loom k) (A'.gram P b' k') (A'.loom k'))
include p u hn hm hh t t' H he
/-- Guess vector at the new tag copied across. Descending licenses both comparability and that
these guesses coincide with the canonical outputs at that tag. -/
lemma same_descent (i) (hi : i ≤ k) :
    Same U (u.mesh i) (Z i) (A.loom i) (Z' (i+l)) (A'.loom (i+l)) ∧
      (i<k → (A.active P b i).beta = (b.read i).re ∧ A.wave P b i=A'.wave P b' (i+l) ∧
        |(Z i).v.re-(Z' (i+l)).v.re| ≤ (dleaf R.L (X i)/1000+dleaf R.L (X' (i+l))/1000)*sites (M i)) := by
  rcases hi.eq_or_lt with y|y
  · subst i; refine ⟨?_,fun e=>by omega⟩; exact u.height ▸ he
  let j:=i+l
  have hj:j<k':=by have := u.height; unfold j; omega
  have e:i+1+l=j+1:=by unfold j; omega
  have g:=t'.toRealQ
  have he': Same U (u.meshT _ _ e) (Z (i+1)) (A.loom (i+1)) (Z' (j+1)) (A'.loom (j+1)) := by
    have he (j) (h : i+1+l=j) : Same U (u.meshT _ _ h) (Z (i+1)) (A.loom (i+1)) (Z' j) (A'.loom j) := by subst j; exact (same_descent (i+1) y).1
    exact he _ e
  rw [A.gram_fine P _ i y,A'.gram_fine P _ j hj] at he'; have v:= service_same U (u.mesh i) (u.meshT _ _ e) (u.Address i j y rfl) p (hn.request i y) (hm.request j hj) (hn.late.trans (Vale.crown ..)) (hm.late.trans (Vale.crown ..)) hh (congrArg Complex.re (Eq.trans (H (i+1) y) (congrArg _ e))) (hat_step i ▸ (hn.beta_ok p t _ y).2) (hat_step j ▸ (hm.beta_ok p g _ hj).2) (hn.flow (hn.charged p t _ y)) (hm.flow (hm.charged p g _ hj)) he'
  change A.wave P b i=A'.wave P b' j ∧ (A.active P b i).beta=(A'.active P b' j).beta ∧ Same U _ (A.active P b i) (A.loom i) (A'.active P b' j) (A'.loom j) ∧ |(A.active P b i).v.re-(A'.active P b' j).v.re| ≤ _ at v
  have hp:=hm.paysStep p t' j hj; have hr:(A.active P b i).beta=(b.read i).re := (v.2.1.trans hp).trans (congrArg Complex.re (H i y.le)).symm
  rw [hm.success p g j hj hp,hn.success p t i y hr] at v
  exact ⟨v.2.2.1,fun _=>⟨hr,v.1,v.2.2.2⟩⟩
termination_by k-i
lemma solved_descent (hA : b.read 0=(x:ℂ)+(z:ℂ)) : Solved P A z b := hn.isSolved p t hA fun i hi=> (((same_descent hh p u hn hm t t' H he i hi.le).2 hi).1)
end Branch
end YM.CF.Py.Rate
