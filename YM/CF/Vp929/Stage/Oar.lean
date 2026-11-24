import YM.CF.Continuum.Oriented
set_option autoImplicit false
set_option maxHeartbeats 980000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars true
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade.Earn
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
variable (F:Pilot)(Z:Pluck R) (I: Stake.Isle){σ:ℝ}(Q: Tun I Z F σ){H:Muster G S x d T}
variable {U:Grasp V.U B d}{W:GivenX V U}{X: GramM (mid N B)}{Y: GramM (mid P B)}(M: Sheep V U W G Y.J X.J (k+2) n A)(P_:∀ X: Support (Domain P B),Lend P B d X)

open Corne

-- VOLUME_STAGE allprice. determinant lower purchase per coordinate.
section all
variable {I:Type}[Fintype I][DecidableEq I](a:Matrix I I ℝ)
private lemma finestGap (hp:a.IsHermitian) (g:FreeResolvent.Gap a t)(i:I): t ≤ hp.eigenvalues i:=by
 let A:=hp.eigenvectorUnitary.val; let v:= A.col i; let s:=hp.eigenvalues i; have h:a *ᵥ v=s • v:=hp.mulVec_eigenvectorBasis i
 have hu:dotProduct v v=1:=by
    have he:star A * A=1:= Unitary.coe_star_mul_self ..; have hw:=congr_fun (congr_fun he i) i
    simp only [Matrix.mul_apply,Matrix.one_apply_eq,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial] at hw; exact hw
 simpa only [h,dotProduct_smul,smul_eq_mul,hu,mul_one] using g.lower v
private lemma logLowerBound(p:a.IsHermitian)(g:FreeResolvent.Gap a t)(h:0<t): Fintype.card I * -|Real.log t|≤ Real.log a.det:=by
 rw [p.det_eq_prod_eigenvalues]; change _≤Real.log (∏ i:I,p.eigenvalues i); rw [Real.log_prod fun i _=> (h.trans_le (finestGap a p g i)).ne']
 exact le_trans (le_of_eq (show _=∑_:I,-|Real.log t| by rw [sum_const,card_univ,nsmul_eq_mul])) (sum_le_sum fun i _=> (neg_abs_le _).trans (Real.log_le_log h (finestGap a p g _)))
end all
lemma detAbove (p:R.Branches K.bind SU.group) : ∃ C:ℝ,0≤C ∧∀ᶠ x:ℝ in atTop,∀{c f:Side}(S:StepData c f)(M:Monk SU.group S)(T:Tube SU.group S), Cert R K S T x → Corne.arcD T x M≤ Fintype.card (Site f)*C:=by
 obtain ⟨m,v,C,hm,hv,hC,h⟩:=Neige.bear K R 2 p; let i:ℝ:= Fintype.card SU.group.ColorIndex; let L:=|Real.log m|
 refine ⟨2*L*i,by unfold L i; positivity,?_⟩; filter_upwards [h] with x h c f S M T t
 let k:=Corne.kist M; have hx:ShardIncome 2 x v C m T k.key k.park k.V k.k:= h S T t _ _ _ (PhysicalNext.JointLoad.Heir.noFlags ..|>.symm) _
 have he:Fintype.card (Active k.key x k.park) ≤ Fintype.card (Site f)*4:=by
    let I:= Active k.key x k.park; let e: I ↪ Edge (Site f):=⟨fun i=> i.val.val, fun u v p => Subtype.ext (Subtype.ext p)⟩
    exact (Fintype.card_le_of_embedding e).trans_eq (by rw [show Fintype.card (Edge (Site f))= Fintype.card (Site f)*Fintype.card Axis from Fintype.card_prod ..]; rfl)
 have hL:=logLowerBound _ (Matrix.isHermitian_iff_isSymm.mpr (show Matrix.IsSymm (Neige.baseX T x k.key k.park k.k k.V) from Char.gramS ..)) hx.soil hm; rw [Fintype.card_prod] at hL
 unfold arcD; apply le_trans (mul_le_mul_of_nonpos_left hL (by norm_num)) _; push_cast; calc
    _ = 1/2*(Fintype.card (Active k.key x k.park) *i)*|Real.log m|:=by unfold i; ring
    _ ≤1/2*(Fintype.card (Site f)*4*i)* |Real.log m|:=by unfold i; gcongr; exact_mod_cast he
    _ = _:=by unfold L; ring
lemma bankDetBoth (p:R.Branches K.bind SU.group) : ∃ C:ℝ,0≤C ∧∀ᶠ x:ℝ in atTop,∀{c f:Side}(S:StepData c f)(M:Monk SU.group S)(T:Tube SU.group S), Cert R K S T x → |Corne.arcD T x M|≤ Fintype.card (Site f)*C:=by
 obtain ⟨E,he,h⟩:= detAbove p; obtain ⟨F,hf,k⟩:=detPay R K p
 refine ⟨max E F, le_trans he (le_max_left ..),?_⟩; filter_upwards [h,k] with x h k c f S M T t; rw [abs_le]; refine ⟨?_, (h S M T t).trans (by gcongr; exact le_max_left ..)⟩
 apply le_trans _ (k S M T t); rw [neg_mul]; apply neg_le_neg; gcongr; exact le_max_right ..
end YM.CF.Jade.Earn
