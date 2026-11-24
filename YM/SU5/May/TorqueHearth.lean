import YM.SU5.May.TorqueBudget
import YM.SU5.May.TorqueFiscal
import YM.SU5.May.TorquePlate
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.Torque
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted WindRose
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {i k : ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} (V:Universal Y H i k I E)
  (G : GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "v₁" n:max => i (G.rows n)
local notation "v₂" n:max => k (G.columns n)
open LocalLimit.Intermediate Harbour
open Hygrometry Hygrometry.MeterFunding
open May.Floe
open Push.SectorMeasure
open Advance.Depths
variable (κ:ℕ){U : Finset Cover}
open Whorl Flare Buffered.Stent.Purchase
variable {X Y': Finset Cover}
variable {c:ℝ} (s m t T:ℕ) (F:Intermediate.Room T → Corr (Λ.Ctor (Y.ir m) T))(z:Intermediate.Room T)
variable (pf:campus Y m t T F)(bt:T ≤ Y.uv t) (hr: phaseMoney Y m t T F z)
local notation "Tz" s:max=> Harbour.earns Y m t T F z s
local notation "𝗠" i:max j:max=> Journey.side Y i j
set_option maxHeartbeats 700000 in
include pf bt hr in
lemma wages_width (k:s<T) {ρ:ℝ}{b:Bool}{f:Mark (Journey.side Y m s)} (h:Maintain (𝗠 m s) b κ ρ c (Satin.region U (𝗠 m s)) f)(Q:0≤c)(p:0≤ρ): Maintain (𝗠 m (s+1)) b κ ((Real.sqrt Λ.R.L.val)⁻¹*(Real.exp (feesT Λ (s+1)-feesT Λ s)*ρ)) c (Satin.region (wingspan Λ l U) (𝗠 m (s+1))) (assembleNext Y m t s T F z f):=by
 let A:= steps Λ.V (Y.ir m) Λ.block (Y.uv t) s ; let D:= Vale.apt (Y.ir m) Λ.block Λ.R.L s; let α:=Harbour.screen Y m t T F z; let hv:= installed Y bt pf hr
 change Maintain _ _ _ _ _ _ (pushMark D A Λ.K.j _ _ _ Chi.canonical Λ.J.d _ _ _); rw [Λ.kJ,←Λ.rJ]
 refine scopeF ?_ (mayRaise Λ.R D rfl A (k:=aliasLaw Λ) (Tz s).val (α (s+1)).J.M Λ.R.odd_side _ _ _ _ ?_ (Satin.region U (𝗠 m s)) (hv.branch _ k) Q h) ?_ le_rfl
 rotate_left 1
 · exact Λ.kJ.trans Λ.rJ.symm ▸ Journey.legal Λ
 rotate_right 1
 · have he: padded D (Satin.region U (𝗠 m s)) (Stencil.clothRadius Λ.R.L (aliasLaw Λ)) ⊆ padded D (Satin.region U (𝗠 m s)) (Λ.R.L.val*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J):= le_trans ((halo_subset _ _).trans (before_zone D (Satin.region U (𝗠 m s)) (aliasLaw Λ))) (Corona.halo_mono (Nat.mul_le_mul_left Λ.R.L.val (by unfold gross; omega)) (Finset.Subset.refl _)); exact he.trans (next_contains U _ _ _)
 apply mul_le_mul_of_nonneg_left _ (by positivity)
 apply mul_le_mul_of_nonneg_right _ p; apply Real.exp_monotone
 rw [feesT,feesT,Finset.sum_range_succ,mul_add, add_sub_cancel_left]; apply mul_le_mul_of_nonneg_left (salary_fee z bt pf k) (Finset.sum_nonneg fun _ _=> norm_nonneg _)
variable (Λ)
noncomputable def price_leg(a:ℕ):= (Real.sqrt Λ.R.L.val)⁻¹^a * Real.exp (feesT Λ (s+a)-feesT Λ s)
private lemma next_leg (a:ℕ): (Real.sqrt Λ.R.L.val)⁻¹*(Real.exp (feesT Λ (s+a+1)-feesT Λ (s+a))*price_leg Λ s a)=price_leg Λ s (a+1):=by
 -- args order check s not κ
 unfold price_leg; let A:=feesT Λ; rw [pow_succ',←add_assoc s, show feesT Λ (s+a+1) - feesT Λ s=(feesT Λ (s+a+1)-feesT Λ (s+a))+(feesT Λ (s+a)-feesT Λ s) from (by ring),Real.exp_add]; ring
variable {Λ}
include pf bt hr
lemma whirlwind(a:ℕ){b:Bool}{f: Mark (Journey.side Y m s)} (V:s+a ≤ T) (hc:0≤c)(e:Maintain (𝗠 m s) b κ 1 c (Satin.region X (𝗠 m s)) f): Maintain (𝗠 m (s+a)) b κ (price_leg Λ s a) c (Satin.region (volumeAround Λ l a X) (𝗠 m (s+a))) (climb Y m t s T F z f a):=by
 induction a with
 | zero=> simp only [price_leg, pow_zero, one_mul,Nat.add_zero, sub_self, Real.exp_zero]; exact e
 | succ a ih=>
   erw [←next_leg Λ s a]; exact wages_width Y κ (s+a) m t T F z pf bt hr V (ih (by omega)) hc (by unfold price_leg; positivity)
omit pf bt hr
-- projection for root testers. Legislature. $ρ ≤ K L^{-a/2} *e^{m^u}$ ANY u>0. No dependence on bets.
lemma leg_shelter {u:ℝ}(hv:0<u) : ∃ A ≥ (0:ℝ),∀ m s a:ℕ,s+a ≤ turnUp Y m → price_leg Λ s a ≤ (Real.sqrt Λ.R.L.val)⁻¹ ^ a * Real.exp (A*(Y.ir m).val^u):=by
 obtain ⟨C,hC,h⟩:= earlyPrice Λ (u:=u/8) (by positivity); refine ⟨C,hC,fun m s a p=>?_⟩
 apply mul_le_mul_of_nonneg_left _ (by positivity); apply Real.exp_monotone
 have hg:0 ≤ feesT Λ s:= (show 0 ≤ feesT Λ 0 from (by simp [feesT])).trans ((fee_up Λ) (Nat.zero_le _)); refine ((sub_le_self _ hg).trans ((fee_up Λ) p)).trans ((h (turnUp Y m)).trans_eq ?_)
 apply congrArg; let N:= (Y.ir m).val; have he:turnUp Y m=N^8:= by unfold turnUp Py.buoy warning N; ring -- tune N let
 rw [he]; push_cast; set v:ℝ:= (N:ℝ); rw [← Real.rpow_natCast_mul (by positivity:v≥0)]; push_cast; ring_nf
#print axioms whirlwind
#print axioms leg_shelter
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.Torque
