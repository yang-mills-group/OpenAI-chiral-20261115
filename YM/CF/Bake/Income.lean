import YM.CF.Bake.Road
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade
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
variable {r:ℕ}
variable (w':Hive.Vista U Y.J.M Y.J.P P_ (k+2) M.q ((Fintype.card Play:ℝ)*t) M.lot M.tone)
variable (V_:ℝ)
local notation "Φ"=> F.hat R x
variable(Y1: Monk SU.group S)
-- Rflare independent of Y except Bravo, discounted pref before.All
variable {a A' ε b α γ:ℝ}{q q':Chi}{u u0 s:ℝ}(ε':Fend V H M Z F q Y.p X.p γ α j l r)
variable{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}(D_: Girt.BaseL U G Y G₀ G₁ q' u)(L0: StageP V H Y X U)
variable (k₀ k₁:ℕ)(s0:ℝ)(A_: Roof (mid N B) s s0 k₀ G₀)(A₁: Roof (mid P B) s s0 k₁ G₁)(heV:k₀+k₁ ≤ radiusB x)(pV:1<I.fine)(k_W:5*Y.p.B +4≤10*radiusB x)(η':l≤18)(ss:s ≤ s0)(tK:s0 < d)(hT:0 < s) (pT:0<u)(hU:u< firstRadius SU.group)
variable (Uq:(j+110)*radiusB x+14 ≤ r) (pQ:2*((j+5)*radiusB x) ≤ r)(ht:0 ≤ V_)(hY:Y.p.order=k)(pX:X.p.order=k)(hK:radiusB x ≤ X.p.B)
variable (P_B:Stake.PondP V F x s u j l (k+2)) (K0: Troupe S r (Words S))(P0: Eire.Ride S)
open Plume
open Nor
variable {c vL:ℝ}(Pz: Folk S r (Words S)→ Track (Eire.Ride S) ℝ)
open scoped Classical
variable {γ':ℝ}
variable (h0:vL=(tolQ X.p).supportExponent+γ')(uQ:X.p.B=radiusB x)(p0:0<γ')
variable {f:ℝ→ℝ}
-- beta feasibility any FIXED count of steps. sizeK.ONE.E only
lemma potX (h:sizeK R.L 1 f)(k p:ℕ)(t:∀ᶠ x in atTop,0 < f x ∧degreePrice (radiusB x) (f x) 1≤1/2):∃ g w:ℝ→ℝ,(∀ᶠ x in atTop,DriveT (radiusB x) k p 1 (f x) (g x) (w x)) ∧ sizeK R.L 1 (fun x=>stopE (radiusB x) k p (g x)) ∧ sizeK R.L 1 (fun x=>stopK (radiusB x) k p (w x)):=by
 let g:=fun x=>miteV (radiusB x) k p 1 (f x)
 have hg(m:ℕ)(x)(px:x >0)(ht:degreePrice m x 1≤1/2):0 < miteV m k p 1 x:=by
    have hv: 0 < 1-degreePrice m x 1:=by linarith
    unfold miteV Vow.chi_f; unfold reserveT coin_n Jet.composeCost stilK
    positivity
 have hx:sizeK R.L 1 g:=(prism_k h k p t).scale _
 have hu:∀ᶠ x in atTop,0 < g x ∧ degreePrice (radiusB x) (g x) 1 ≤1/2:= ((t.and ((apollo_d 1 hx).spine.eventually (ge_mem_nhds (by norm_num : 0 < (1/2:ℝ))))).mono fun i x=>⟨hg _ _ x.1.1 x.1.2,x.2⟩)
 let Fq(x):= ringT (radiusB x) (g x); have hv:sizeK R.L 1 Fq:=by
    let Uq:= fun x:ℝ=>(1-degreePrice (radiusB x) (g x) 1)⁻¹; have hz:sizeK R.L 0 Uq:=(sizeK.mild R.L 2).cost_d (by
        filter_upwards [hu] with x v; have h:= v.2; have hP :0<1-degreePrice (radiusB x) (g x) 1:=(by linarith); unfold Uq; rw [abs_of_pos (inv_pos.mpr hP),inv_le_iff_one_le_mul₀ hP,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith)
    unfold Fq ringT; simp only [pow_zero,mul_one]; exact hx.tint hz
 let V:= fun x=>g x + Real.exp 1 *Fq x; have hp:sizeK R.L 1 V:= hx.accrue (hv.scale _)
 have hy:∀ᶠ x in atTop,0 < V x∧ degreePrice (radiusB x) (V x) 1 ≤1/2:=by
    filter_upwards [hu,(apollo_d 1 hp).spine.eventually (ge_mem_nhds (by norm_num : 0 < (1/2:ℝ)))] with i h p; have h1:=h.1; have h2:0 < 1-degreePrice (radiusB i) (g i) 1:=(by linarith [h.2]); refine ⟨add_pos_of_pos_of_nonneg h1 (mul_nonneg (Real.exp_pos _).le (show 0 ≤ Fq i from ?_)),p⟩; unfold Fq ringT; positivity
 refine ⟨g,V,?_ ,prism_k hx k p hu,prism_k hp k p hy⟩
 filter_upwards [hu,hy,hv.spine.eventually (ge_mem_nhds zero_lt_one)] with i hu hv hp; exact ⟨le_rfl,hu.1,hu.2.trans_lt (by norm_num),hp,hv.1,hv.2.trans_lt (by norm_num),le_rfl⟩
end YM.CF.Jade
