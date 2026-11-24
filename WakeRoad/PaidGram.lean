import WakeRoad.GramSignal

set_option autoImplicit false
set_option synthInstance.maxSize 28000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind
namespace GramSignal
variable {P:Spine}
open WakeInvestment
lemma single_expenditure (A:ℝ) {r:ℕ→ℕ} (p:∀ᶠ s in atTop,(r s:ℝ) ≤ sPow P.par s A):
    Tendsto (fun s:ℕ=> ‖staffWeight (r s)‖ * chip (hat P.par.R.L P.par.x s) (-3)) atTop (𝓝 0) := by
  have he:Tendsto (fun x:ℝ=> 4*(BProof.coin x 0 A 0)^5*chip x (-3)) atTop (𝓝 0) := by
    simp_rw [mul_assoc, chip, BProof.coin_pow,BProof.coin_mul] -- no sPow
    have hz:=BProof.coin_purchases (a:=0* (5:ℕ) + -3/400000) (b:=A*(5:ℕ)+0) (c:=0*(5:ℕ)+0) (Or.inl (by norm_num))
    simpa using hz.const_mul 4
  have hf (n:ℕ): ‖staffWeight n‖ = 4*(n:ℝ)^5:=by
    rw [staffWeight,norm_mul,norm_pow,norm_pow,Complex.norm_real,Real.norm_of_nonneg (by positivity),Complex.norm_natCast]; ring
  simp_rw [hf]
  apply squeeze_zero' (Eventually.of_forall (fun s=>by have := chip_pos (hat P.par.R.L P.par.x s) (-3); positivity)) (p.mono (fun s h=>?_)) (he.comp (turnover P.par))
  have q:= chip_pos (hat P.par.R.L P.par.x s) (-3)
  change 4* _ * _ ≤ 4*(sPow P.par s A)^5*_
  gcongr

lemma duo_expenditure (A:ℝ) {r:ℕ→ℕ} (p:∀ᶠ s in atTop,(r s:ℝ) ≤ sPow P.par s A):
    Tendsto (fun s:ℕ=> ‖staffWeight (r s)^2‖ * chip (hat P.par.R.L P.par.x s) (-3)) atTop (𝓝 0) := by
  have he:Tendsto (fun x:ℝ=> 16*(BProof.coin x 0 A 0)^10*chip x (-3)) atTop (𝓝 0) := by
    simp_rw [mul_assoc, chip, BProof.coin_pow,BProof.coin_mul]
    have hz:=BProof.coin_purchases (a:=0* (10:ℕ) + -3/400000) (b:=A*(10:ℕ)+0) (c:=0*(10:ℕ)+0) (Or.inl (by norm_num))
    simpa using hz.const_mul 16
  have hf (n:ℕ): ‖staffWeight n^2‖ = 16*(n:ℝ)^10:=by
    rw [norm_pow,staffWeight,norm_mul,norm_pow,norm_pow,Complex.norm_real,Real.norm_of_nonneg (by positivity),Complex.norm_natCast]; ring
  simp_rw [hf]
  apply squeeze_zero' (Eventually.of_forall (fun s=>by have := chip_pos (hat P.par.R.L P.par.x s) (-3); positivity)) (p.mono (fun s h=>?_)) (he.comp (turnover P.par))
  have q:= chip_pos (hat P.par.R.L P.par.x s) (-3)
  change 16* _ * _ ≤ 16*(sPow P.par s A)^10*_
  gcongr

open Jewel Papal
variable (P) (f : ℕ → ℕ)
local notation "Y" => P.run
local notation "Λ" => P.par
local notation "iA" n:max=> P.period (P.projection.rows (f n))
local notation "kA" n:max=> P.cutoff (P.projection.columns (f n))
local notation "ν" s:max n:max=> side P.run (iA n) s

/- Aux price-passage: the inner-index price limit of a two-index observation converging
on the curried filter has the same outer-index limit. -/
lemma passStair {g:ℕ×ℕ→ℂ}{e:ℕ→ℂ}{z:ℂ}(p:Tendsto g stairs (𝓝 z))
    (h:∀ s,Tendsto (fun n=>g (s,n)) atTop (𝓝 (e s))) : Tendsto e atTop (𝓝 z):=by
  refine Metric.tendsto_nhds.mpr fun ε hp=> ?_
  filter_upwards [eventually_curry_iff.mp (Metric.tendsto_nhds.mp p (ε/2) (half_pos hp))] with s t
  exact lt_of_le_of_lt (le_of_tendsto ((h s).dist tendsto_const_nhds) (t.mono (fun n p=>p.le))) (half_lt_self hp)

lemma liftStair {α:Type*}[TopologicalSpace α]{g:ℕ→α}{x:α}(p:Tendsto g atTop (𝓝 x)):
    Tendsto (fun sn:ℕ×ℕ=>g sn.1) stairs (𝓝 x):= p.comp (tendsto_atTop.mpr fun b=> eventually_curry_iff.mpr ((eventually_ge_atTop b).mono fun _ hs=> Eventually.of_forall fun _=>hs))


lemma sharp_house (F:Papal.Weaver) (i k s:ℕ) : sharp Y P.large s i k (household P.calibration F) = Journey.compass Y i k s (F (side Y i s)) := by
  change Journey.compass _ i k s (send Y P.large i s _) = _
  congr 1
  unfold send household Spine.calibration
  generalize_proofs _ pf
  exact eqVia pf
where
  eqVia {n m:Side}(p:n=m) : p ▸ F n=F m:= by subst m; rfl

open Pressure
variable (β : ℕ→ℝ)
def choiceWeave (W:Staff) (d s : ℕ) : Papal.Weaver :=
  W.rungWeave (κFix β s) d (temp (hat P.par.R.L P.par.x s))

lemma paidStaff (s d w:ℕ) (W:Staff)(h: W.Pays d w) :
    TestFamily P.calibration true (household P.calibration (choiceWeave P β W d s)) := by
  -- inspect second arg
  constructor
  · exact ⟨W.skyRent d, W.letterBudget _ P.calibration _ h⟩
  · intro hz; contradiction


variable {P f β} {r:ℕ→ℕ} {d w:ℕ} {W V:ℕ→ Staff}
structure seated (P:Spine)(f:ℕ→ℕ)(d w:ℕ)(W V:ℕ→ Staff)(I:ℝ) : Prop where
 Wpaid(s:ℕ):(W s).Pays d w
 Vpaid(s:ℕ):(V s).Pays d w
 controls: ∀ᶠ s in atTop, ∀ᶠ n in atTop, ∃ (q:ℕ)(o:Seat (side P.run (P.period (P.projection.rows (f n))) s)),
    (W s).tenancy (side P.run (P.period (P.projection.rows (f n))) s) d Staff.clearance q o ∧
    (V s).tenancy (side P.run (P.period (P.projection.rows (f n))) s) d Staff.clearance q o ∧ (q:ℝ) ≤ sPow P.par s I
variable {I:ℝ}(pI:0<I)(g:Pooling P.run (P.period ∘ P.projection.rows) (P.cutoff ∘ P.projection.columns) f β)(Q:P.PhysicalWakeGram) (J:seated P f d w W V I) (pr:∀ᶠ s in atTop,(r s:ℝ) ≤ sPow P.par s I)

include g Q J pI pr
lemma compass_single : Tendsto (fun sn:ℕ×ℕ=> staffWeight (r sn.1)*Journey.compass Y (iA sn.2) (kA sn.2) sn.1 (choiceWeave P β (W sn.1) d sn.1 (ν sn.1 sn.2))) stairs (𝓝 0):=by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun sn=>norm_nonneg _) _ (liftStair (single_expenditure I pr))
  apply eventually_curry_iff.mpr
  filter_upwards [Q I pI, J.controls, grow_e I (w:ℝ) pI P.par] with s z u k
  filter_upwards [g.up.tendsto_atTop.eventually z,u] with n h hx
  obtain ⟨q,o,a,_,b⟩:=hx
  exact (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left (h.single (J.Wpaid _) a (paidFix P.run g P.large s) b k) (norm_nonneg _))

lemma compass_difference :
    Tendsto (fun sn:ℕ×ℕ=>staffWeight (r sn.1)^2*
      (Journey.compass Y (iA sn.2) (kA sn.2) sn.1
        ((choiceWeave P β (W sn.1) d sn.1*choiceWeave P β (V sn.1) d sn.1) (ν sn.1 sn.2))-wale Y sn.1 (iA sn.2) (kA sn.2) (W sn.1) (V sn.1) (κFix β sn.1))) stairs (𝓝 0):=by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun sn=>norm_nonneg _) _ (liftStair (duo_expenditure I pr))
  apply eventually_curry_iff.mpr
  filter_upwards [Q I pI, J.controls, grow_e I (w:ℝ) pI P.par] with s z u k
  filter_upwards [g.up.tendsto_atTop.eventually z,u] with n h hx
  obtain ⟨q,o,a,b,c⟩:=hx
  exact (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left (h.duo (J.Wpaid _) a (J.Vpaid _) b (paidFix P.run g P.large s) c k) (norm_nonneg _))

open CF.Hiro CF.Onyx Regis.Head.Brecht Ballad
open Stationary (Gaia)
variable {a:Gaia}(e:a≠0) (u:∀ i,0<r i)(U:Tendsto r atTop atTop)
    (p:Tendsto (fun s=>riseX (r s) ((W s).u-(V s).u)) atTop (𝓝 a))
    (b:Tendsto (fun s=>riseX (2*(r s:ℝ)) ((W s).face.1-(V s).face.1)) atTop (𝓝 a))
    {L G:Twah.DirSpin} (t:∀ s,(W s).spin=L) (v:∀ s,(V s).spin=G)
    {F D:PlaqAxes} (t':∀ s,(W s).face.2=F) (v':∀ s,(V s).face.2=D)

include u U e p b t v t' v'
lemma compass_limit : Tendsto (fun sn:ℕ×ℕ=>staffWeight (r sn.1)^2 * Journey.compass Y (iA sn.2) (kA sn.2) sn.1 ((choiceWeave P β (W sn.1) d sn.1*choiceWeave P β (V sn.1) d sn.1) (ν sn.1 sn.2))) stairs (𝓝 (shotR L G (X:=a)*speckleV F D SU.group a)) := by
  have hp:= (compass_difference pI g Q J pr).add (wale_target u U W V e p b g L G t v F D t' v')
  rw [zero_add] at hp
  exact hp.congr fun sn=> by ring

omit u U e p b t v t' v' Q g pr pI
lemma seated.back : seated P f d w V W I :=
  ⟨J.Vpaid,J.Wpaid,J.controls.mono (fun _ k=>k.mono (fun _ z=>by obtain ⟨q,o,u,v,w⟩:=z; exact ⟨q,o,v,u,w⟩))⟩

omit J
lemma e_pass (Z:Papal.Weaver) (s:ℕ) (h:TestFamily P.calibration true (household P.calibration Z))(u:StrictMono f) (x:ℂ):
    Tendsto (fun n=> x * Journey.compass Y (iA n) (kA n) s (Z (ν s n))) atTop (𝓝 (x*P.E s (household P.calibration Z))) := by
  have p:= ((FixedProbe.coherent_price P.run P.large s P.projection h).comp u.tendsto_atTop).const_mul x
  exact p.congr fun n=> congrArg (x * ·) (sharp_house P Z _ _ s)

def oneStaff (P:Spine) (β:ℕ→ℝ) (d:ℕ)(r:ℕ→ℕ)(W:ℕ→ Staff)(s:ℕ) :=
  staffWeight (r s) * P.E s (household P.calibration (choiceWeave P β (W s) d s))
def twoStaff (P:Spine) (β:ℕ→ℝ)(d:ℕ)(r:ℕ→ℕ)(W V:ℕ→ Staff)(s:ℕ) :=
  staffWeight (r s)^2 * P.E s (household P.calibration (choiceWeave P β (W s) d s*choiceWeave P β (V s) d s))
def staffCov (P:Spine) (β:ℕ→ℝ)(d:ℕ)(r:ℕ→ℕ)(W V:ℕ→ Staff)(s:ℕ):=
  twoStaff P β d r W V s-oneStaff P β d r W s*oneStaff P β d r V s

include u U e p b t v t' v' Q g pr pI J
/-- Unselected *mixed staff vs mixed staff* signal. This normalization keeps BOTH actual
unselected one-points. Not yet a disqualification of the separate gauge and matter product. -/
theorem staff_limit : Tendsto (staffCov P β d r W V) atTop (𝓝 (shotR L G (X:=a)*speckleV F D SU.group a)) ∧ Tendsto (oneStaff P β d r W) atTop (𝓝 0) ∧ Tendsto (oneStaff P β d r V) atTop (𝓝 0):=by
  have he(s:ℕ) : TestFamily P.calibration true (household P.calibration (choiceWeave P β (W s) d s*choiceWeave P β (V s) d s)):=
    (paidStaff P β s d w (W s) (J.Wpaid s)).mul (paidStaff P β s d w (V s) (J.Vpaid s))
  have se : Tendsto (oneStaff P β d r W) atTop (𝓝 0):=
    passStair (compass_single pI g Q J pr) fun s=>e_pass _ _ (paidStaff P β s d w (W s) (J.Wpaid s)) g.up _
  have sv : Tendsto (oneStaff P β d r V) atTop (𝓝 0):=
    passStair (compass_single pI g Q J.back pr) fun s=>e_pass _ _ (paidStaff P β s d w (V s) (J.Vpaid s)) g.up _
  have du : Tendsto (twoStaff P β d r W V) atTop (𝓝 (shotR L G (X:=a)*speckleV F D SU.group a)):=
    passStair (compass_limit pI g Q J pr e u U p b t v t' v') fun s=>e_pass _ _ (he s) g.up _
  refine ⟨?_,se,sv⟩
  have hc:= du.sub (se.mul sv); rw [mul_zero,sub_zero] at hc; exact hc

#print axioms staff_limit
#check @staff_limit
end GramSignal
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
