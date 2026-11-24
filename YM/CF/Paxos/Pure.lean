import YM.CF.Paxos.Vary
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
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(l0:ℕ)(k₀:ℕ)
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht l0 B0)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
local notation "Xc"=> cell M B R.L
local notation "Lr"=>dleaf R.L
local notation "Fh"=> hueR V a p i N0 T M ht l0 B0
local notation "μh"=> hat R.L x
variable (R0 E C δ:ℝ→ℝ){wα:ℝ}(y:ℝ)(D':Heron V a p i N0 k₀ J q h wα R0 E C δ y)(hy:y ≤ x)
local notation "S'"=> StarPS l0
open Oise
variable (HR:∀ j,0 ≤ R0 (hat R.L x j))(W0:Cape M B R.L)(Wp:∀ j:ℕ,RocketV V (mesh M R.L j) (mesh M R.L (j+1)) U W J (W0 j) (apt M B R.L j) q)
local notation "Vq"=> θ_guess (l0:=l0) (fun i=>R0 (μh i)) HR
structure Pull_P (L:Vestal M B R.L)(v:ℕ→ Haro.SpaceM)(z:ℕ→ℝ) : Prop where
 wear (j:ℕ): j<l0 →∀ V':Orbit (cell M B R.L j),Rue.FleetS (L j).p.threshold V'.1→ stove U (W0 j) (L (j+1)) (W0 (j+1)) (apt M B R.L j) (V.L.op (l0-1-j) (kint M B R.L j)) q J.d (v j).val V' = denZ (L j) U (W0 j) V'
 tip(j:ℕ): j<l0→ ‖v j‖≤ R0 (hat R.L x j)
 price(j:ℕ):j<l0→ |z j|≤ δ (hat R.L x j)
 owns(j:ℕ): j ≤ l0→ CloseC (hueR V a p i N0 T M ht l0 B0 j) (L j)
 note(j:ℕ): j≤ l0→ Laurel (L j) K.j h (dleaf R.L (hat R.L x j)) (dleaf R.L (hat R.L x j)) R.L.val
 sift(j:ℕ):j≤ l0→matchedX (hat R.L x j) (L j).beta
 shift(j:ℕ): j<l0→ ((L (j+1)).beta - (B0 (j+1))) - ((L j).beta -B0 j) = z j
 color:(L 0).beta=B0 0
 boot:L l0=pay_K (hueR V a p i N0 T M ht l0 B0 l0) (L l0).beta
variable(hp:1≤ h)(hn:61 ≤ M.val)
include Wp D D' hy hn hp
set_option maxHeartbeats 1400000 in
lemma root_W :∃ L v z,Pull_P V a p i N0 T M ht l0 B0 J q h R0 δ W0 L v z ∧ ∀ j<l0, ‖Complex.exp (L (j+1)).v‖*Hertz V a p i N0 M k₀ J q h R0 E C δ y D' hy j ≤ ‖Complex.exp (L j).v‖ :=by
 let Mψ(j):= R0 (μh j); have hh(j):0< Mψ j:= D'.hex _ (hy.trans (crown ..)); have h_v(j):0≤Mψ j:=(hh j).le
 obtain ⟨A,Q,v,Y,Bk,Xp⟩:= able_c V a p i N0 T M ht l0 k₀ B0 D J q h R0 E C δ y D' hy h_v W0 Wp hp hn
 let f(i:Fin l0)(v:S'):= (Bk i v / ν_PS R.L,(Mψ i)⁻¹ • (Y i v).val)
 have hz:=billx_T V; have hx(v:S'):‖(fun i=>f i v)‖≤1:=by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=>?_ ; let a:= Mψ i; let b:= (Y i v).val; have ha:0<a:=hh i; have hv:‖b‖≤a:= (Y i v).property; change max (‖Bk i v/ ν_PS R.L‖) (‖a⁻¹ • b‖) ≤ 1
    refine max_le ?_ ?_; · rw [Real.norm_eq_abs,abs_div,abs_of_pos hz,div_le_one hz]; exact (Xp.fee i (by omega) i.isLt v).trans ((le_abs_self _).trans (D'.wean _ (hy.trans (crown ..))))
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]; exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq (inv_mul_cancel₀ (ne_of_gt ha))
 let G(z:S'):S':=⟨fun i=>f i z,hx z⟩
 have hg:Continuous G:=Continuous.subtype_mk (continuous_pi (fun (i:Fin l0)=> ((Xp.contD i.val).div_const (ν_PS R.L)).prodMk ((continuous_subtype_val.comp (Xp.contW i.val)).const_smul (Mψ i)⁻¹))) _
 obtain ⟨z,hK⟩:= Moen.Space.bow zero_lt_one G hg
 have hw(i:Fin l0): f i z=z.val i:=congrFun (congrArg Subtype.val hK) i
 have hyψ(i:ℕ)(h:i<l0):θ_guess Mψ h_v i z=Y i z ∧ Bk i z=ra_C R.L z i:=by
    let j:Fin l0:=⟨i,h⟩; unfold θ_guess ra_C; rw [dif_pos h,dif_pos h]; have hα: Mψ i≠0:= (hh i).ne'
    constructor
    · apply Subtype.ext; change Mψ i • (z.val j).2= (Y i z).val; rw [←hw j]; exact smul_inv_smul₀ hα ((Y i z).val)
    rw [←hw j]; change _=ν_PS R.L*(Bk i z/ ν_PS R.L); rw [mul_comm,div_mul_cancel₀ _ hz.ne']
 let Lz:= Rowt V a p i N0 T M ht l0 B0 A Q v z; refine ⟨Lz,fun i=>(Y i z).val, fun i=>Bk i z,⟨fun j q=> Xp.wear j (by omega) q z (hyψ j q).1 (hyψ j q).2,fun i _=>(Y i z).property,fun i p=> Xp.fee i (by omega) p z,fun _ _=> ⟨rfl,rfl,rfl,rfl⟩,fun i p=>Xp.paid i (by omega) p z,fun j u=> mood_a V a p i N0 T M ht k₀ B0 D J q h R0 E C δ y D' hy z j u,?_,?_,?_⟩,fun j u=>Xp.good j (by omega) u z (hyψ _ u).1⟩ -- hy shadows. fix
 · intro i p; change tempo_b R.L B0 z (i+1)-_-(tempo_b R.L B0 z i- _) =_; rw [mood_z,(hyψ i p).2]; ring
 · change tempo_b R.L B0 z 0=B0 0; simp [tempo_b,debt_p]
 unfold Lz Rowt; rw [Xp.cash,Xp.past,Xp.heat]; rfl
end YM.CF.Py
