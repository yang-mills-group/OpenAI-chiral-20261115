import YM.CF.BProof.Diary.Prelude
/-! Theorem:B-main. Stop independently of depth, with width chosen before Profile.
All Φ are physical Gauge kernels. X.q grainZ included in trajectory certificate.
Important: B (width) and chosen Profile P fixed through the h and x purchases. No Fit
or Reflection necessary; hence the theorem also holds on the Fit option of taking the
trajectory. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof
open Function Filter NormedSpace Finset
open Lattice Tenant Lat Cube Skye RG Wilson Push.SectorMeasure Precision
open Vale Vale.Grace Hom Py Paige Rush Scroll Scree Jet Vault Drapes
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Pressure
namespace Estimator
open Diary Start
variable {N B : Side} {K : Teller SU.group} {P : Patch} {R : ChartRatio SU.group}
variable {V : Grace K P R} {d h u x : ℝ} {F : Grasp V.U B d} {W : GivenX V F} {A:Prelude V u}{J : Robes N V W}
variable (M:Side) {N₀ : ℕ} (X : Month x 1 6 2 N₀ V W) (q : Chi) (R₀ δ : ℝ → ℝ)
structure Life (Z: Profile J A) (x h:ℝ) : Prop where
 delay : Z.Afford (h:=h) x
 minX : 2<x
 slow : d ≤ A.cap V
 pearl : u ≤ W.pearl.q
 height : Z.Height ≤ h
variable (Z:Profile J A) (L:Life Z x h)(i:ℕ)
abbrev stage (x:ℝ)(j:ℕ) := hat P.L x j -- imple
abbrev meterSide (j:ℕ) := (More (cell (M*N) B P.L j))
local notation "νΦ"=> cell (M*N) B P.L i
local notation "σ_"=> More (cell (M*N) B P.L i)
local notation "ψζ"=> hat P.L x i
abbrev DutyK (x:ℝ)(i:ℕ) := Mote.Licence Z.course radiusB (dleaf P.L) (Z.course.council radiusB (hat P.L x i)) (hat P.L x i) h
noncomputable def pass := Classical.choice (L.delay ψζ (Vale.crown ..))
abbrev legal (x:ℝ) (i:ℕ) := Mote.Extent Z.course (hat P.L x i) (Z.course.council radiusB (hat P.L x i)) (cell (M*N) B P.L i) -- local notation bug i binding; tune
-- Port visible by every matching period using only earlier x data
abbrev Harbor (x:ℝ) (i:ℕ) := Gates.Stage.Setup A.S P.L Z.a (More (cell (M*N) B P.L i)) (Z.course.council radiusB (hat P.L x i)) (hat P.L x i)
variable (Y0: Harbor M Z x i) -- notation auto args order
variable (p: legal M Z x i)
section
include L p
lemma map_space : Nonempty (Harbor M Z x i):= Mote.Grade Z.course (pass Z L i) p Z.choice -- arguments M?
end
-- L is a certificate at x. `born` bound means the Mark comes specifically from the recipe
-- with expressions & kernels built here. `Point` includes additional cost.
open Anthem
variable (Y: Cape (M*N) B P.L) (ρ:ℕ→ℝ) {n:ℕ} (T: Run V J X M h q R₀ δ n Y ρ)
abbrev LevelK := Score Y0.yard (Manus.Poles νΦ)
def Choice (Q: Score Y0.yard (Manus.Poles (cell (M*N) B P.L i))) : Prop:= Mote.Built Z.course (pass Z L i) Y0 (Y i) (T.D i) W.pearl (ν:=J.k) (Q0:=Q)
def Outcome(Q: Score Y0.yard (Manus.Poles (cell (M*N) B P.L i))) : Prop:= Mote.Yield (F:=F) Y0 (Y i) (T.D i) Q
include p
/-- All Mark locations for Y0 (chosen once here even with n varying). For every true run
at every such period/depth the certified witnesses charge and attain the bound. `Numerator`
definition is on its physical Orbit; it includes no scalar offset. `Profile.spends`
pays all eventual pivot increases before choosing x.
-/
theorem B_main (ht:i≤ n): ∃ Q: Score Y0.yard (Manus.Poles (cell (M*N) B P.L i)), Choice M X q R₀ δ Z L i Y0 Y ρ T Q ∧ (Real.exp (-(10*(hat P.L x i)^10)*((More (cell (M*N) B P.L i)).val:ℝ)^4)≤ ‖numerator (T.D i) F (Y i) Q.test‖) ∧ ∀ j, Allowed (Y0.yard.band j) (Q.slot j) ∧ Paid (Q.slot j) (Real.exp (10*(hat P.L x i)^10*((More (cell (M*N) B P.L i)).val:ℝ)^3)):=by
 let Yp:=Z.course; let Φ:= pass Z L i; have he:0<h:= lt_of_lt_of_le (lt_of_lt_of_le one_pos Z.height_p) L.height
 obtain ⟨q,u,v⟩:= Mote.bought Yp Φ Y0 (Y i) (T.D i) W.pearl p (clients M T Φ ht he.le (lt_trans zero_lt_two L.minX)) L.pearl V.note (orderK V) W.health.le (L.slow.trans (min_le_left ..)) (L.slow.trans (min_le_right ..)) -- tune order
 exact ⟨q,u,v.output,v.mark⟩
omit p
include L
lemma admissible : ∃ q:ℕ,0<q∧ ∃ m:ℕ,∀ M:Side,m≤M.val→q∣M.val→Admits V J X M∧ legal M Z x i:=by
 obtain ⟨A,h,H⟩:= Z.course.powers (pass Z L i); refine ⟨A,h,J.h+X.q+61,fun M p t=>?_⟩; have he : M.val ≤ (M*N).val:=Nat.le_mul_of_pos_right _ N.property; refine ⟨⟨by omega,by omega,by omega⟩, H _ ?_⟩; change A∣ (((M.val*N.val)*(P.L^i).val*2)*B.val); exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left t _) _) _) _ -- tune
end Estimator
end YM.CF.BProof
#print axioms YM.CF.BProof.Estimator.B_main
