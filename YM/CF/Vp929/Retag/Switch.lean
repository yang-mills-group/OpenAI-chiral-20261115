import YM.CF.Vp929.Retag.Registrars
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.SplitFlag
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
open Ione Beau Haro Cascade
open scoped Mew
open Jet SU Taxi Rue
open WilsonStartup
/-! Factor the gas sum. -/
variable {n:Side} (c:Clip)(b p:BudgetPoint)(z:ℂ)(A:ℂ→L[ℝ]ℝ) (V:Orbit n)
lemma allgood (D:Support (More n))(h: Unmasked b p V.1 D) (β:ℝ) : minted c b p β Complex.reCLM V.1 D= Real.exp (-β * tagEnergy c b p D V.1):=by
  rw [minted,if_pos h, ←Complex.ofReal_neg, ←Complex.ofReal_mul,←Complex.ofReal_exp]; rfl
lemma toll_fuel (hv: Rue.FleetS b.threshold V.1)(h : Decent c b)(hp : Decent c p)(ht : b.threshold ≤ p.threshold)(β:ℝ) :
    let T:=Reef.solvent (Design.top SU.group c); let F:= Real.exp (T.inChannels c b β V.1-T.inChannels c p β V.1)
    fueled b (entry c b p β Complex.reCLM) V= F • fueled p 0 V:=by
  let D:=flags b.threshold V.1; let J:=parts (widen b) D; intro T F; rw [registry c b p _ _ _ hv]
  by_cases w : flags p.threshold V.1=∅
  · rw [fuel_one p 0 V w]; let G(Y:Support (More n)):= -β*tagEnergy c b p Y V.1
    have he:F=∏ Y∈J, Real.exp (G Y):=by
      unfold F; rw [← Real.exp_sum]; apply congrArg Real.exp; have hm:= energy_sum c b p β V.1 h hp ht w; change T.inChannels .. - T.inChannels ..= β * ∑ Y∈J, tagEnergy c b p Y V.1 at hm
      unfold G; rw [←mul_sum]; linarith only [hm]
    rw [he, ← (show (algebraMap ℝ (Cipher n)) (∏ Y∈J,Real.exp (G Y))= (∏ Y∈J,Real.exp (G Y)) • (1:Cipher n) from (Algebra.algebraMap_eq_smul_one _)),map_prod]
    refine prod_congr rfl fun Y hy=>?_ ; rw [allgood ..]; rotate_left
    · exact ⟨(Ac.lives _ D hy).1,by rw [Healthy,w]; simp⟩
    rw [Algebra.algebraMap_eq_smul_one]; rfl
  obtain ⟨y,hy⟩:= Finset.nonempty_iff_ne_empty.mpr w
  have hf:y∈D:=older V.1 _ _ ht hy
  let Y:=Ac.burst (pad (widen b)) D y
  have hY : Y∈J:=mem_image_of_mem _ hf; have hX:y∈Y:= (Ac.bright ..).mpr ⟨hf,.refl⟩
  rw [still_force p V w,smul_zero]; refine prod_eq_zero hY ?_; rw [minted,if_neg (fun t:Unmasked b p _ Y=> Finset.disjoint_left.mp t.2 hX hy),map_zero]
open Py.Rate
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {m B:Side} {d:ℝ} (W : Grace K R L) (U : Grasp W.U B d) (S: Scree.Loom (mid m B))
lemma switch_launch (h : Decent K.top.clip b)(hp : Decent K.top.clip p)(ht : b.threshold ≤ p.threshold)(β:ℝ) (V:Orbit (mid m B))(hv: Rue.FleetS b.threshold V.1) :
    denZ (launch W.L β p _) U S V = denZ (construct b (W.L.path 0) K.top.clip (vanilla _) β (0,entry K.top.clip b p β Complex.reCLM) 0) U S V := by
  -- scalar commutation in tank doesn't even require projection
  let k:= K.top.clip; let T:=W.L.path 0; let x:=T.inChannels k p β V.1; let y:=T.inChannels k b β V.1; let F:=Real.exp (y-x)
  let X:=launch W.L β p (mid m B); let Y:=construct b T k (vanilla (mid m B)) β (0, entry k b p β Complex.reCLM) 0
  let A:=spar K.j X.J.M (S V)
  have hw:Y.betaL S V - ((x-y:ℝ):ℂ)= X.betaL S V:=by unfold GramM.betaL GramM.H0; change 0-↑y- Pec.pigment X.J.I _- _=0-↑x-_; push_cast; ring
  have he : Y.board V= (F:ℂ) • X.board V:=by
    unfold GramM.board; change NormedSpace.exp (exponentL b 0 V.1+exponentL b 0 V.1)*_=_ • (NormedSpace.exp (exponentL p 0 V.1+exponentL p 0 V.1)*_); rw [still_Footprint,still_Footprint,add_zero,NormedSpace.exp_zero,one_mul,one_mul,Complex.coe_smul]
    change fueled b _ _= _; unfold F x y T; rw [W.L.born]; exact toll_fuel k b p V hv h hp ht β
  have hz : tank A (Y.board V)= (F:ℂ) • tank A (X.board V):= by rw [he]; unfold tank; rw [smul_sum]; exact sum_congr rfl fun i _=> ((mul_smul (F:ℂ) (crumb (X.board V).val i) _))
  unfold denZ; change _= Complex.exp (Y.betaL S V) • acts (tank A (Y.board V)) (relV U X.J (S V)); rw [hz,act_smul,smul_smul]; change Complex.exp (X.betaL _ _) • _=_; rw [←hw, show (F:ℂ)=Complex.exp (-((x-y:ℝ):ℂ)) from by unfold F; rw [←Complex.ofReal_neg,neg_sub,Complex.ofReal_exp], ← Complex.exp_add,sub_eq_add_neg]
end YM.CF.SplitFlag
