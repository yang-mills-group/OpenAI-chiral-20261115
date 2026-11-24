import YM.CF.Tar.Rein
import YM.CF.Tar.Silt
import YM.CF.Paxos.Seed
set_option autoImplicit false

set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Beau Haro Ione Salt
set_option maxHeartbeats 1000000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(nK B1:ℕ)(k₀:ℕ)
local notation "NK"=> trunkY nK B1
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht (trunkY nK B1) B0)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
local notation "Xc"=> cell M B R.L
local notation "Lr"=>dleaf R.L
local notation "Fh"=> hueR V a p i N0 T M ht (trunkY nK B1) B0
local notation "μh"=> hat R.L x
variable (R0 E C δ:ℝ→ℝ){wα:ℝ}(y:ℝ)(D':Heron V a p i N0 k₀ J q h wα R0 E C δ y)(hy:y ≤ x)
variable (V0 Jx:ℕ→ℝ)(Fp:ℝ→ℝ)(Hμ:Sculp V a p i N0 M k₀ J q h δ R0 E C y D' hy Fp nK B1 Jx V0)
local notation "S'"=> StarPS NK
open Oise
variable (W0:Cape M B R.L)(Wp:∀ j:ℕ,RocketV V (mesh M R.L j) (mesh M R.L (j+1)) U W J (W0 j) (apt M B R.L j) q)
local notation "HR"=> (fun i=>(Hμ.rateB i).le)
local notation "Vq"=> θ_guess (l0:=trunkY nK B1) Jx (fun i=>(Hμ.rateB i).le)
local notation "Ωs"=> fun j:ℕ=> wage_B nK B1 j R.L x
variable (Ue: RegBudget (cell M B R.L (trunkY nK B1)))(sE:ℂ) (pS:∀ b:ℝ,Provides R.L K.j (color_b (hueR V a p i N0 T M ht (trunkY nK B1) B0 (trunkY nK B1)) b Ue 0 0 sE) h (V0 (trunkY nK B1)) (zone_F (trunkY nK B1) (post_H nK)))
structure Pull_K (L:Vestal M B R.L)(v:ℕ→ Haro.SpaceM)(z:ℕ→ℝ) : Prop where
 wear (j:ℕ): j<(trunkY nK B1) →∀ V':Orbit (cell M B R.L j),Rue.FleetS (L j).p.threshold V'.1→ stove U (W0 j) (L (j+1)) (W0 (j+1)) (apt M B R.L j) (V.L.op ((trunkY nK B1)-1-j) (kint M B R.L j)) q J.d (v j).val V' = denZ (L j) U (W0 j) V'
 tip(j:ℕ): j<(trunkY nK B1)→ ‖v j‖≤ Jx j
 price(j:ℕ):j<(trunkY nK B1)→ |z j|≤ mode_D nK j R.L x δ
 owns(j:ℕ): j ≤ (trunkY nK B1)→ CloseC (hueR V a p i N0 T M ht (trunkY nK B1) B0 j) (L j)
 note(j:ℕ): j≤ (trunkY nK B1)→ Provides R.L K.j (L j) h (V0 j) (zone_F j (post_H nK))
 sift(j:ℕ):j≤ (trunkY nK B1)→matchedX (hat R.L x j) (L j).beta
 shift(j:ℕ): j<(trunkY nK B1)→ ((L (j+1)).beta - (B0 (j+1))) - ((L j).beta -B0 j) = z j
 color:(L 0).beta=B0 0
 boot:L (trunkY nK B1)=color_b (hueR V a p i N0 T M ht (trunkY nK B1) B0 (trunkY nK B1)) (L (trunkY nK B1)).beta Ue 0 0 sE
variable(hp:1≤ h)(hn:61 ≤ M.val)
include Wp D Hμ pS hn hp
set_option maxHeartbeats 1400000 in
lemma root_BΩ :∃ L v z,Pull_K V a p i N0 T M ht nK B1 B0 J q h δ V0 Jx W0 Ue sE L v z ∧ ∀ j<(trunkY nK B1), ‖Complex.exp (L (j+1)).v‖* tide_W nK j (Hertz V a p i N0 M k₀ J q h R0 E C δ y D' hy) ≤ ‖Complex.exp (L j).v‖ :=by
 let Mψ:= Jx; have hh(j):0<Mψ j:= Hμ.rateB _; have h_v(j):0≤ Mψ j:=(hh j).le
 obtain ⟨A,Q,v,Y,Bk,Xp⟩:= leap_T V a p i N0 T M ht nK B1 k₀ B0 D J q h R0 E C δ y D' hy V0 Jx Fp Hμ W0 Wp Ue sE pS hp hn (trunkY nK B1) le_rfl; rw [Nat.sub_self] at Xp -- tune signature
 let f(i:Fin (trunkY nK B1))(v:S'):= (Bk i v / ((Ωs) i),(Mψ i)⁻¹ • (Y i v).val)
 have hz(i):= Hμ.maxim i; have hx(v:S'):‖(fun i=>f i v)‖≤1:=by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=>?_ ; let a:= Mψ i; let b:= (Y i v).val; have ha:0<a:=hh i; have hv:‖b‖≤a:= (Y i v).property; change max (‖Bk i v/ ((Ωs) i)‖) (‖a⁻¹ • b‖) ≤ 1
    refine max_le ?_ ?_; · rw [Real.norm_eq_abs,abs_div,abs_of_pos (hz _),div_le_one (hz _)]; exact (Xp.fee i (by omega) i.isLt v).trans (Hμ.dose _ i.isLt)
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]; exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq (inv_mul_cancel₀ (ne_of_gt ha))
 let G(z:S'):S':=⟨fun i=>f i z,hx z⟩
 have hg:Continuous G:=Continuous.subtype_mk (continuous_pi (fun (i:Fin (trunkY nK B1))=> ((Xp.contD i.val).div_const ((Ωs) i)).prodMk ((continuous_subtype_val.comp (Xp.contW i.val)).const_smul (Mψ i)⁻¹))) _
 obtain ⟨z,hK⟩:= Moen.Space.bow zero_lt_one G hg
 have hw(i:Fin (trunkY nK B1)): f i z=z.val i:=congrFun (congrArg Subtype.val hK) i
 have hyψ(i:ℕ)(h:i<(trunkY nK B1)):θ_guess Mψ h_v i z=Y i z ∧ Bk i z=guess_Q _ (Ωs) z i:=by
    let j:Fin (trunkY nK B1):=⟨i,h⟩; unfold θ_guess guess_Q; rw [dif_pos h,dif_pos h]; have hα: Mψ i≠0:= (hh i).ne'
    constructor
    · apply Subtype.ext; change Mψ i • (z.val j).2= (Y i z).val; rw [←hw j]; exact smul_inv_smul₀ hα ((Y i z).val)
    rw [←hw j]; change _=((Ωs) i)*(Bk i z/ ((Ωs) i)); rw [mul_comm,div_mul_cancel₀ _ (hz _).ne']
 let Lz:= Hymn_v V a p i N0 T M ht nK B1 B0 A Q v z; refine ⟨Lz,fun i=>(Y i z).val, fun i=>Bk i z,⟨fun j q=> Xp.wear j (by omega) q z (hyψ j q).1 (hyψ j q).2,fun i _=>(Y i z).property,fun i p=> Xp.fee i (by omega) p z,fun _ _=> ⟨rfl,rfl,rfl,rfl⟩,fun i p=>Xp.paid i (by omega) p z,fun j u=> tilt_a V a p i N0 T M ht k₀ B0 J q h δ R0 E C y D' hy Hμ D z j u,?_,?_,?_⟩,fun j u=>Xp.good j (by omega) u z (hyψ _ u).1⟩ -- hy shadows. fix
 · intro i p; change tempo_v _ B0 (Ωs) z (i+1)-_-(tempo_v _ B0 (Ωs) z i- _) =_; rw [boom_z,(hyψ i p).2]; ring
 · change tempo_v _ B0 (Ωs) z 0=B0 0; simp [tempo_v]
 unfold Lz Hymn_v; rw [Xp.cash,Xp.past,Xp.heat]; rfl
end YM.CF.Py
