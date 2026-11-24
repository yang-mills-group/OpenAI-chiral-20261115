import YM.SU5.FiniteGaugeData.Brique.Bolt
/-! # Haar average and extraction of a singlet with STILL a local-center charge under link rotations alone
All barycenter transport here *within* one resolution/operator class, just actual chiral matrix data. Don't project to gauge orbits of any factorized law. Later estimates won't need norm estimates on the extracted (nonzero positive) value here. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Window.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Spire Tenant Fock Fock.Brique Tulip Dial Fir Buffered Skye Scree Nacre
variable {N L B:Side} {σ : Window.Family} {S:Finset (Site N)} {R T U : Support (More N)} {t:List (Site N)} {k n j w:ℕ} {a b c e f r C d f₁ f₂:ℝ}
open scoped Classical
-- local instance opCStarAlgebra (using classical may interfere)
attribute [local instance] opCStarAlgebra
local notation "Μ" => FC (Single N)
local notation "Φ" => SU.group.probHaar
section
variable (A:FC (Single N))
abbrev orbitB (A: FC (Single N)) (h:SU.E) := flipsP (globalH N h) A
lemma orbit_cont : Continuous (orbitB A) := (flips_cont A).comp (f:= globalH N) (continuous_pi fun _=> continuous_id)
lemma orbit_integrable : Integrable (orbitB A) Φ := by exact (orbit_cont A).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
def centB(N:Side) : FC (Single N)→ₗ[ℂ]FC (Single N) where
 toFun A:=∫ h:SU.E,orbitB A h∂ Φ
 map_add' a b:=by unfold orbitB; simp_rw [map_add]; exact integral_add (orbit_integrable a) (orbit_integrable b)
 map_smul' x b:=by unfold orbitB flipsP; simp_rw [twist_scalar,RingHom.id_apply,integral_smul]
lemma cent_norm (A:FC (Single N)): ‖centB N A‖ ≤ ‖A‖:= by
 apply le_trans (norm_integral_le_of_norm_le (integrable_const ‖A‖) (Eventually.of_forall (fun i=> (twist_norm ..|>.le : ‖orbitB A i‖≤‖A‖)))) (by simp)
lemma cent_invariant(g:SU.E): orbitB (centB N A) g= centB N A:=by
 let H:Μ→L[ℝ] Μ := ⟨(flipsP (globalH N g)).toAlgEquiv.toLinearMap, Fock.breeze _⟩; change H (∫ y:SU.E, orbitB A y∂Φ) = ∫ y:SU.E, orbitB A y∂Φ
 refine (H.integral_comp_comm (orbit_integrable A)).symm.trans ((show (∫ y:SU.E,H (orbitB A y)∂Φ)= ∫ y:SU.E, orbitB A (g*y)∂Φ from ?_).trans (integral_mul_left_eq_self _ _)); exact integral_congr_ae (Eventually.of_forall fun i=> (by unfold H; change flipsP _ (flipsP _ A)=flipsP _ A; rw [←wind_join,prop_global])) -- tune H
lemma cent_one(N:Side):centB N 1=1:=by change (∫ y:SU.E,orbitB _ _∂ Φ)=(1:FC (Single N)); unfold orbitB; simp only [flips_one,integral_const,probReal_univ,one_smul]
lemma cent_tiny (P:Trio σ N R t A): Trio σ N R t (centB N A):= by
 let X:= (syllabus σ N R t).restrictScalars ℝ; apply Convex.integral_mem (f:=orbitB A) X.convex (X.closed_of_finiteDimensional) ?_ (orbit_integrable A); exact Eventually.of_forall fun i=> Trio.wind _ P
omit A
end
-- theorem owner in arbitrary linear functional on MARK, uniform material acquisition across the orbit (no cost to any appropriate lift elsewhere after Barque); Stump inputs incl grain. 
open Branch Cascade
variable {Z:Peg N}(O:Casing N Z.e (Z.Ft false) c C d){o:Seat N}{W:Pane N→ℂ} {F:Corset T R o}{Y: FC (Single N)}{X:Op (Single N)}
variable (ι:Mark N→ₗ[ℂ]ℂ)
def lobby (W:Pane N→ℂ)(F:Corset T R o) : FC (Single N)→L[ℝ] ℂ :=
 let X:FC (Single N)→ₗ[ℂ]ℂ := {
  toFun:=fun i=> ι (cargo F W i)
  map_add':=fun a b=>by rw [show cargo F W (a+b)=cargo F W a+cargo F W b from funext fun i=>by unfold cargo; rw [map_add,smul_add]; rfl, map_add]
  map_smul':=fun a x=>by rw [show cargo F W (a•x)=a • cargo F W x from (by funext i; unfold cargo; simp_rw [flipsP,twist_scalar, Pi.smul_apply]; exact smul_comm ..),map_smul]; rfl }
 (X.toContinuousLinearMap).restrictScalars ℝ
section
private lemma fee_of_zero {D:Μ} (p:Barque σ S U D) (t: ∀ (A:FC (Single N)), (∀ h:SU.E, orbitB A h=A) →∀ t:List (Site N), t≠[]→t.Nodup→ t.toFinset⊆ S →Trio σ N U t A→ ι (cargo F W A) =0): lobby ι W F (centB N D)=0:=by
 induction p with
 | @stage Y t' u v w h=> exact t (centB N Y) (cent_invariant _) _ u v w (cent_tiny Y h)
 | zero=> simp only [map_zero]
 | add _ _ a b=> rw [map_add,map_add,a,b,add_zero]
 | @mul b _ a ih=> rw [map_smul]; change ι (cargo F W _) =_; rw [show ∀ (a:ℂ)(b:Μ), cargo F W (a • b)=a • cargo F W b from ?_,map_smul]; exact (congrArg _ (show ι _= 0 from ih)).trans (smul_zero _); intro a b; funext i; unfold cargo; rw [flipsP,twist_scalar]; exact smul_comm ..
/- Pick nonzero. HAAR avg only at one accessible vertex; marks on a single field orbit with that frame.
     Expected `casingAt` from blend. -/
variable {θ:ℝ}
include O in
theorem centBuys (Ψ:Etude σ S T (Z.Ft false 1) a b Y) (p:0 ≤ Z.e) (A: θ < ‖ι (cargo F W 1)‖) (H:∀ (Y:FC (Single N)),Etude σ S T (Z.Ft false 1) a b Y→ ‖ι (cargo F W Y)‖ ≤ θ) :
    ∃ A:FC (Single N), (∀ h:SU.E, orbitB A h=A) ∧ ∃ t:List (Site N), t≠[] ∧ t.Nodup ∧ t.toFinset⊆ S ∧ Trio σ N (T\ S.image node) t A ∧ ι (cargo F W A) ≠ 0:=by
 have hv(g:SU.E):‖ι (cargo F W (orbitB Y g))‖ ≤ θ:= H _ ((show Z.Ft false 1= _ from globalWind (N:=N) g ▸ O.coloredWT 1 (guard0 p) (globalH N g)).symm ▸ Ψ.turn (globalH N g)) -- ▸ expression tune
 let L:= lobby ι W F
 have he : ∫ y:SU.E, L (orbitB Y y) ∂Φ= L (centB N Y) := L.integral_comp_comm (orbit_integrable _)
 have ht:‖L (centB N Y)‖ ≤ θ:=by rw [←he]; exact (norm_integral_le_of_norm_le (integrable_const θ) (Eventually.of_forall hv)).trans (by simp)
 by_contra! x
 have hk : lobby ι W F (centB N Y) = lobby ι W F 1:=sub_eq_zero.mp (by rw [←map_sub]; nth_rw 1 [← cent_one N]; rw [←map_sub]; exact fee_of_zero ι Ψ.rays x)
 change ‖lobby ι W F (centB N Y)‖≤θ at ht; rw [hk] at ht; exact lt_irrefl _ (A.trans_le ht)
end
end YM.CF.Window.Brique
