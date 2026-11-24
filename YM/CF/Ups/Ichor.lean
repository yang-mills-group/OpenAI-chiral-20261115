import YM.CF.Ups.Awe
set_option autoImplicit false
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
variable {d e η z g A B':ℝ} {j k k' m n l:ℕ}
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
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
variable {x':ℕ→ℝ}(t:Tendsto x' atTop atTop){L':ℕ→ℕ} (U':∀ i',SpanPS V a p i N0 J q h R0 δ (x' i') (L' i'))
local notation "N_X"=> rimZ V N0 J (x':=x')
variable(X:Month x a i p N0 V W) (H:MeterQ V a p i N0 J q h R0 δ x X)
open Graph
local notation "Mo"=> oYY V N0 J x
local notation "Zo" j:max=>cell Mo B R.L j
variable {ℓ:ℝ}(hp:1≤h)(ht:0 <ℓ)(hx:0 < x)
open Pyx Girt
local notation "hatQ"=> hat R.L x
variable (L0:∀ l:ℕ,SpanPS V a p i N0 J q h R0 δ x l)(R':Cape (oYY V N0 J x) B R.L)(Q:CoilPS V a p i N0 J q h R0 δ X L0 R')
variable {β:ℕ→ℝ}{A:ℕ→Haro.SpaceM}{F:∀ i,InkPS (cell (oYY V N0 J x) B R.L i)}{u:ℕ→ℕ}
local notation "Eρ"=> ν_P V a p i N0 J q h R0 δ L0 R'
variable (dF:ΦS_P V a p i N0 J q h R0 δ L0 R' β A F u)(hpF:K.top.clip.direct ≤1)
local notation "Fp"=> PionK V Mo B R' q
local notation "Lp₀" j:max=> InkPS (Zo j)
local notation "T₀" j:max=> Oracle (Zo j)
open Reed
include Q dF
lemma hear_ps(j:ℕ): ∃ f:Orbit (Zo j)→ Phys (Zo j), Envelope f ∧ (⇑(F j))=ᵐ[city _] f:=by
 obtain ⟨K,w⟩:= Q.stain j; let xz:= F j -- notation x capture
 have he:∀ᵐ z∂city _,‖F j z‖ ≤ K:=by
    filter_upwards [dF.stay j] with i v; exact le_of_tendsto v.norm ((dF.hz.tendsto_atTop.eventually (eventually_ge_atTop j)).mono (fun k p=> w _ p i))
 let f:= ((Lp.memLp (F j)).1).mk (F j); have ht:= (Lp.memLp (F j)).1.stronglyMeasurable_mk; let S: Set (Orbit (Zo j)):= {z| ‖f z‖≤K}; refine ⟨S.indicator f,⟨ht.measurable.indicator (ht.measurable.norm (measurableSet_Iic)),max K 0, fun z=>?_⟩ ,?_⟩
 · by_cases p:z∈ S; rw [Set.indicator_of_mem p]; exact le_trans (show ‖f z‖ ≤ K from p) (le_max_left ..); rw [Set.indicator_of_notMem p,norm_zero]; exact le_max_right ..
 filter_upwards [(Lp.memLp (F j)).1.ae_eq_mk,he] with i v p; exact v.trans (Set.indicator_of_mem (show i∈ S from by change ‖f i‖≤K; change _=f i at v; rwa [←v]) f).symm
structure ActsPS (j:ℕ)(X:Oracle (cell (oYY V N0 J x) B R.L j))(Y:Oracle (cell (oYY V N0 J x) B R.L (j+1)))(b:ℝ)(H:Haro.SpaceM) :Prop where
 town(xz:Orbit (cell (oYY V N0 J x) B R.L (j+1)))(v:Phys (cell (oYY V N0 J x) B R.L (j+1))): Y xz v=∫ y:Orbit (cell (oYY V N0 J x) B R.L j), X y (PionK V (oYY V N0 J x) B R' q j J.d b H y xz v) ∂city _
lemma hand_PS(j:ℕ)(Ω: T₀ j)(g:BoundedT Ω) (hΩ:RealC Ω) (U0: Loyal Ω) :∃ ψ:T₀ (j+1), ActsPS V N0 J q R' j Ω ψ (β (j+1)) (A j) ∧ Loyal ψ ∧ BoundedT ψ ∧ RealC ψ ∧ remark Ω (F j)=remark ψ (F (j+1)):=by
 let x':= L0 (j+1); let Z:=x'.scale; obtain ⟨Kb⟩:=Brioche.us V x'.tip J q h Z j (by omega); have he:x'.Y=R':=Q.tale _; let G':=apt Mo B R.L j; let Y:= x'.E (j+1); let Y':= pay_K Y (β (j+1)); let Kv:Girt.BaseL U G' Y (R' j) (R' (j+1)) q J.d:=by rw [←he]; exact Kb
 have hp:Girt.Ward Y':= by obtain ⟨i,p,u,v⟩:=Kv.grant; exact ⟨i,p,u,v⟩; -- why have K
 let Dx:Girt.BaseL U G' Y' (R' j) (R' (j+1)) q J.d:={Kv with grant:=hp}; let T:= V.L.op 0 (kint Mo B R.L j)
 have h': T.ratio=ratio G'∧T.patch.Branches T.kernel SU.group:= by have ht:= Brioche.drives V x'.tip J q h Z j; simpa only [show j+1-1-j=0 from by omega] using ht
 let b:=β (j+1); let f:= Fp j J.d b (A j); let r:= R' j; let Rc:=R' (j+1)
 let Ω':= Pyx.sweepM (A j) Ω; let u:= Pyx.swipeP (j:=K.j) G' Y' r Rc q J.d T Ω'; -- j must K.j use Tz.
 obtain ⟨ψ,v,e⟩:= boardQ Dx h'.1 h'.2 (barQ (A j) g); have hx(i y v):u i y v=Ω y (f y i v):=sip_Q ..
 have hY(i v0): ψ i v0=∫ x',Ω x' (f x' i v0)∂city _:=by rw [show _=∫ j:Orbit (Zo j),u i j v0 ∂city _ from v i v0]; simp_rw [hx]
 obtain ⟨L,hL,uV⟩:=hear_ps V a p i N0 J q h R0 δ X L0 _ Q dF (j+1); have hQ: Envelope (fun i:Orbit (Zo j) × Orbit (Zo (j+1))=> L i.2) := snap hL measurable_snd
 let Pk(t: Orbit (Zo j) × Orbit (Zo (j+1))):= Ω t.1 (f t.1 t.2 (L t.2)); have hpK: Envelope Pk:=by have ht:= snob Dx T h'.1 h'.2 (barQ (A j) g) hQ; change Envelope (fun i:Orbit (Zo j) × Orbit (Zo (j+1)) => u i.2 i.1 (L i.2)) at ht; simp_rw [hx] at ht; exact ht
 have hpu:= Env.integrableX hpK ((Scree.city _).prod (Scree.city _)); refine ⟨ψ,⟨hY⟩,heart Dx T h'.1 h'.2 v (frock _ U0),e, χPS v hΩ,?_⟩; unfold remark
 calc
   _= ∫ y,(∫ z,Pk (y,z)∂city _)∂city _:=by
      apply integral_congr_ae; filter_upwards [dF.cog j] with i p; rw [p, ← (Ω i).integral_comp_comm (dF.jug ..) ]; exact integral_congr_ae (uV.mono fun z q=> by unfold Pk; simp only; rw [q])
   _= ∫ z,(∫ y,Pk (y,z)∂city _)∂city _:= (integral_prod _ hpu).symm.trans (integral_prod_symm _ hpu)
   _= _:=by apply integral_congr_ae; refine uV.mono fun z p=>?_ ; dsimp only; rw [hY,p]
end YM.CF.Py
