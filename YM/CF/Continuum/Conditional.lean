import YM.CF.Continuum.CoherentSeams
import YM.CF.Continuum.ReflectTest
import YM.CF.Vale.Land

/-!
# Reflection frozen: at the *capP* densities of the FiniteGaugeData construction

Orientation, projection normalization, all positive-side occupancy probes of
`crossForm`. Nothing here asserts RP after integrating against gauge Haar
fields --- averaging the PSD assertion given here could directly work for a positive
measure supported on such configurations (or related e.g. by gauge frame changes),
a result neither available nor called for in this problem. For comparison attempts this singles out
the gauge-dependent normalization factor of the heat-to-overlap limit *even*
at the seam and demonstrates entrywise tests compatible from the native stencil
view.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter NormedSpace Lattice RG Wilson SU Lat Fock Phase Mir Cube Mir.Trip RP Reflect Finset Spire Brace Spark Scroll Tulip Dial Peaks Pressure Paige Vault Scree Vale Vale.Grace MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192
variable {m B N : Side}
local notation "Λ"=>CSide m B
local notation "Ω"=>Xmind m B
local notation "ν"=>northZ m B

section normalization
def oneField (u : Bkg (More N)) (T : Phys N) (F : Evaluation N) := inner ℂ (mateK N) (acts (F u) T)
lemma oneField_vac (u : Bkg (More N)) (T:Phys N) : oneField u T 1=inner ℂ (mateK N) T:= by unfold oneField; rw [Pi.one_apply,act_one]
lemma oneField_scalar (u : Bkg (More N)) (T:Phys N) (F:Evaluation N) (a:ℂ) : oneField u (a • T) F=a*oneField u T F:=by unfold oneField; rw [map_smul,inner_smul_right]

def conditional (u : Bkg (More N)) (T : Phys N) (F : Evaluation N) := oneField u T F / oneField u T 1
lemma conditional_rescale {u: Bkg (More N)}(T:Phys N)(a:ℂ)(p:a≠0): conditional u (a • T)=conditional u T:=by funext F; unfold conditional; rw [oneField_scalar,oneField_scalar,mul_div_mul_left _ _ p]
lemma one_read_conditional {u: Bkg (More N)}{T:Phys N}(p:oneField u T 1≠0) : conditional u T 1=1:=div_self p
end normalization

variable (U : Skin m B) {K: Teller group}{P:Patch}{e:ℝ}{Y: Pricing K.j P.L P.odd_side (Thread K.j)} {L: Grasp Y B e}{v:ℕ} (β:ℝ)(q:BudgetPoint) (i:Axis)
-- auxiliary kernel for positive condition
def seamed (m B:Side) (i:Axis) (u : Skin m B)(F:Evaluation (CSide m B)):= inner ℂ (linearB (CSide m B)) (acts (toSeam m B i (F u)) (acts (lineOp (projector (wiel m B (axisCut m B i (northZ m B)) u))) (linearB (CSide m B))))
def edgeTest (m B:Side)(x:Skin m B)(F:Evaluation (CSide m B)):= inner ℂ (linearB (CSide m B)) (acts (crossL (helix (CSide m B)).symm (F x)) (sound m B (northZ m B) x))
private lemma pays_vac : edgeTest m B U 1= inner ℂ (linearB Λ) (sound m B ν U):= by unfold edgeTest; rw [Pi.one_apply,cross_one,act_one]
private lemma compatible_sea (k:Guard U e)(b:Room B e)(F:Evaluation Λ) :
    seamed m B i U F=star (edgeTest m B U 1)*edgeTest m B U F:=by
  let A:=lineOp (projector (wiel m B ν U)); let S:= seamShift m B i; let T:=quantU S; let X:=linearB Λ; let Z:=sound m B ν U
  have hp:star (edgeTest m B U 1)=inner ℂ Z X:=by rw [pays_vac]; exact inner_conj_symm ..
  have he : projector (wiel m B (axisCut m B i ν) U)= twist S (projector (wiel m B ν U)):=by rw [show wiel m B _ U=twist S (wiel m B ν U) from (swingFringe ν _ _).symm,projector_twist (wiel_ok ν b k)] -- projector direction?
  have hv:acts A X=inner ℂ Z X • Z:=Sea.scalar (lensP ν b k) (Phase.unity ν b k) _
  let G:=crossL (helix Λ).symm (F U); have hZ:acts T.val X=X:= fixedSign ..
  unfold seamed toSeam; rw [he, line_twist, hp, ←act_mul, ←map_mul]; change inner ℂ X (acts (twist T (G*A)) X) = _
  nth_rw 2 [←hZ]; rw [RP.bra S hZ, act_mul,hv,map_smul,inner_smul_right]; rfl

variable (u:L.roundZ ≤ (CSide m B).val)(g:Guard U e)(h: flags q.threshold U=∅)
local notation "Q"=> conditional (N:=Λ) U (capP (K:=K) (P:=P) L β q (m:=m) U)
include u g
lemma phase_single (F:Evaluation Λ): oneField U (changeM L U babyM) F=Complex.exp (-candle m B (L.cost m babyM) U) * edgeTest m B U F:= by
  unfold changeM; rw [oneField_scalar,show babyM=firstM from rfl, Brace.fundus L.topB L.baseY (L.couture u firstM) U g]; congr 1; exact (cCash ..).symm
include h
lemma envelope_singlet (F:Evaluation Λ): oneField U (capP (K:=K) (P:=P) L β q U) F=Complex.exp (-((β*basicP K.top.clip U:ℝ):ℂ)-candle m B (L.cost m babyM) U)*edgeTest m B U F:=by
 rw [capP,Set.indicator_of_mem (show U∈_ from h),oneField_scalar,phase_single U u g, sub_eq_add_neg, Complex.exp_add,mul_assoc]
theorem conditional_balance (p : oneField U (capP (K:=K) (P:=P) L β q U) 1≠0)(F:Evaluation Λ) : Q F=seamed m B i U F/seamed m B i U 1 ∧ 0 < seamed m B i U 1:=by
  let b:=L.baseY; let c:=edgeTest m B U 1; have hp : c≠0 := fun e=>p (by rw [envelope_singlet U β q u g h]; rw [show edgeTest m B U 1=0 from e,mul_zero])
  rw [compatible_sea U i g b,compatible_sea U i g b]; constructor
  · unfold conditional; rw [envelope_singlet U β q u g h, envelope_singlet U β q u g h]; rw [mul_div_mul_left _ _ (Complex.exp_ne_zero _),mul_div_mul_left _ _ (show star c ≠0 from star_ne_zero.mpr hp)]
  apply lt_of_le_of_ne (star_mul_self_nonneg _); exact (mul_ne_zero (star_ne_zero.mpr hp) hp).symm

theorem conditional_positive (r : mirrorPane m B i U=U) (p : oneField U (capP (K:=K) (P:=P) L β q U) 1≠0) : Q 1=1 ∧ TestOK m B i Q :=by
 refine ⟨div_self p,⟨?_,?_,?_⟩⟩
 · intro F G _ _; unfold conditional oneField; rw [Pi.add_apply,act_add,inner_add_right,add_div]
 · intro F _ c; unfold conditional oneField; rw [Pi.smul_apply,act_smul,inner_smul_right]; ring
 intro F f; unfold crossForm; rw [(conditional_balance U β q i u g h p (flipTime m B i F * F)).1]; apply div_nonneg _ ((conditional_balance U β q i u g h p 1).2.le); unfold seamed; rw [toSeam_fiscal i f U, r]; exact (by
    let V:=toSeam m B i (F U); have he := ((mem_localObs ..).mp f).2.2.1 U; have hh:= reflector_line (c:=ν) U (show rayUK m B i U=U from r) V (toSeam_forward i he.sector rfl) (wiel_ok (axisCut m B i ν) L.baseY g); simpa only [chord,Bool.false_eq_true, ite_false, one_smul] using hh)

theorem conditionally_normalized {Z:ℂ} (c:Z≠0)(r : mirrorPane m B i U=U) (p : oneField U (capP (K:=K) (P:=P) L β q U) 1≠0) {X:Type*}[Fintype X](F:X→Evaluation (CSide m B))(u':∀ j,F j∈nonnegativeTime m B i) : let Φ:= conditional U (Z⁻¹ • capP (K:=K) (P:=P) L β q U); Φ 1=1 ∧ (reflectionForm i Φ F).PosSemidef:=by
  intro Φ; unfold Φ; rw [conditional_rescale _ _ (inv_ne_zero c)]; obtain ⟨v',X⟩:= conditional_positive U β q i u g h r p; exact ⟨v',X.ref_matrix i u'⟩
end YM.CF.Window
