import YM.CF.Iva.Base
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Iva
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
variable {N P B:Side}{G:Ratio (mid N B) (mid P B)}{S:StepData (Domain N B) (Domain P B)}{x β R e a b:ℝ} {n m l k:ℕ}
local notation "G₅"=> SU.group
variable{T:Tube G₅ S}(Z:Muster G S x e T)(M:Monk G₅ S){w t u C D:ℝ}
local notation "l_"=> Z.post
local notation "q_"=> Z.trot
local notation "Ba"=> radiusB x
local notation "Wa"=> (fun y=>M.atop y x)
attribute [local instance] opCStarAlgebra
variable {ρ ρ' η Kp:ℝ}{r1 r2 J0 k₀:ℕ}{s t u w L b' c E_:ℝ}
local notation "dΩ"=> Domain N B
local notation "dF"=> Domain P B
local notation "Γ"=> Single (mid N B)
local notation "F_"=> Rent0 G e
local notation "K₀"=> (fun i:Site dΩ=>M.key.dome (Z.loft*(radiusB x)))
local notation "O'"=> M.key.dome (Z.loft*(radiusB x))
variable {μ₁ μ₂ μ μ₃ c1 c2 x':ℝ}{ψ:nomA N P B→ Op (Single (mid N B))}{X':nomA N P B→ℂ}
variable (p:Gard (a:=μ₁) (a':=μ₂) (C:=c2) (c:=c1) (D:=D) (v:=μ₃) (Z:=x') (Φ:=X') (J:=ψ) (n:=m) (R₁:=J0) Z r1 r2 k₀ k)
-- P proof.K. pay. Sensor from M' leg. Essence: Ledger / Core.κ
variable (F: Monk SU.group S→ Rent0 G e)(i:Site (Domain N B))
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (I I':E→L[ℝ] Directions SU.group (Domain N B))(Rt Vt:E→Rent0 G e)(O:Support (Domain N B)){M': Monk SU.group S}
variable (h:∀ᶠ i in 𝓝 (0:E), Muster.Post Z (M.atop (I i) x) (M'.atop (I' i) x) (Rt i) (Vt i) (F (M'.atop (I' i) x)) (F (Cay.rough (M'.atop (I' i) x) 0)) k O) (hv:‖I'‖ ≤ 1)(hO:M'.V=M.V)(hz:M'.park=M.park)(hx:M'.k=M.k)
variable {Z_ b1 r' γ:ℝ}
local notation "Zn"=> (fun y:E=>M.atop (I y) x)
local notation "Zt"=> (fun y:E=>M'.atop (I' y) x)
open Rue
open Lor Font
variable (L':Wages) (g:LampM Z M' F i r2 n L')
abbrev Kplan(k:ℕ)(u:ℝ):= Jet.composeCost k u 1
local notation "ζ"=> Kplan n
lemma bally (i:Site dΩ)(u v:Γ)(g:0≤a): ζ (wreath (Ba+1) i a u v)=wreath (Ba+1) i (ζ a) u v:=by unfold wreath Kplan; split; rfl; simp [Jet.composeCost]
abbrev creed (Z:Muster G S x e T)(M:Monk SU.group S)(R R':Rent0 G e)(r n:ℕ)(i:Site (Domain N B)):= exp (idyl (poll Z M i R R') (maskS Z R i))-1 -- n unused
include p h g hv hO hz hx
local notation "dω"=> Directions SU.group (Domain N B)
lemma moves_e (hu: Beat.shadows (o:=i) O k₀)(y:i∉ M.key.dome r2):
 i∉ M'.key.dome r2 ∧ |xurn Z M i|≤ L'.ego ∧ Allows n (fun x'=> poll Z (M.atop (I x') x) i (Rt x') (Vt x')) 0 (ζ L'.tip) ∧ (∀ u v:Γ,Allows n (fun x'=> maskS Z (Rt x') i u v) 0 (wreath (radiusB x+1) i (ζ L'.puff) u v)):=by
 have he:i∉M'.key.dome r2:= mt (gateL (M.atop (I 0) x) h.self_of_nhds.duo i k₀ hu (by rw [separation_self]; exact (zero_add _).le.trans p.extra)).mpr y
 have hk := g.leap he
 refine ⟨he,?_ ,?_ , fun u v=>?_⟩
 · have hx':= artB Z (M.atop (I 0) x) h.self_of_nhds.duo p.ash p.ages i k₀ hu p.hunter.tag
   rw [show xurn Z M i=xurn Z M' i from hx']; exact g.ash
 · refine (hg_k I' hv _ _ hk.1).germ ?_; filter_upwards [h] with i' u'; change poll Z _ i _ _=_
   exact (show poll Z (M.atop (I i') x) i _ _=poll Z (M'.atop (I' i') x) i _ _ from congrArg₂ (fun a (b:ℝ)=> a-(b:ℂ)) (fisc Z _ _ _ J0 k k₀ _ u'.duo p.ash p.ages i u'.kindB p.hunter hu _ p.trih p.beta p.pole u'.port u'.noth) (Lich.Muster.artB Z (M.atop (I i') x) u'.duo p.ash p.ages i k₀ hu p.hunter.tag)).symm
 -- maskS needs Funds even when site parity no ferm ⇒ no v≥0 deriv.L avoid using parameter sign in bally
 have hy:= (p.hunter.line : _); refine ((hg_k I' hv _ _ (hk.2.1 u v)).mono (Eq.le ?_)).germ ?_
 · unfold Kplan wreath; split; rfl; simp [Jet.composeCost]
 filter_upwards [h] with i' u'; change maskS Z _ _ u v= maskS Z _ _ u v; exact congrArg (fun A: Op Γ=>A u v) (peg Z _ _ p.trih p.ferr i _ u'.port (Subset.trans (Corona.halo_mono hy (Subset.refl _)) hu)).symm
-- actual sweetK budget even for M markers. No polynomial simplification.$θ_
local notation "W'"=> wreath (Ba+1) i (ζ L'.puff)
lemma phys_r (a t':ℝ)(u:Beat.shadows (o:=i) O k₀)(v:∀ j,0≤W' j j)(p1:0≤L'.puff)(hp:0≤L'.ego)(hz₀:0≤L'.tip) :Rigid (fun y=>elk Z (M.atop (I y) x) (Rt y) (Vt y) r2 k a t' (.inr (.inl i))) n 0 (saber (cull n W' (ζ L'.tip+ L'.ego)) 1):=by
 by_cases t:i∈M.key.dome r2
 · let K:=cull n W' (ζ L'.tip+ L'.ego); have ht:0 ≤ K:=by -- support projection cull
      unfold K cull; refine add_nonneg (fun i=>?_) ?_; · simp only [naked,Pi.single_apply]; split_ifs; exact (show 0≤_ by unfold Kplan Jet.composeCost steel; positivity); exact le_rfl
      unfold thumb; apply sum_nonneg; intro i _; apply sum_nonneg; intro l _ j; unfold steel ank wreath; simp_rw [Pi.single_apply]; split_ifs <;> (first|exact le_rfl| simp only [mul_zero]; rfl| exact (show 0≤_ by unfold Kplan Jet.composeCost; positivity))
   have hy:0 ≤ Rue.saber K 1:=(saber_r 1 ht (fun _=>1) Rue.showK).1
   refine Woody.germ (h:=(show Woody n 0 (0:E) (saber K 1) from ?_)) ?_ -- syntax
   · exact ⟨(Woody.empty (0:E) (k:=n) (n:=LeanV Γ)).own, fun i=> let h':= (Woody.empty (0:E) (k:=n) (n:=LeanV Γ)).haveP i; ⟨h'.smooth,h'.earned.trans (hy i)⟩⟩
   filter_upwards with i'; unfold elk sweetK; simp only [Xb,Fa,Sum.elim_inl,Sum.elim_inr]; unfold docS docA; -- tune
   have th:i ∈ (M.atop (I i') x).key.dome r2:=t; rw [if_pos th,if_pos th]
   rw [show boat (0:Op Γ)=0 from (Subtype.ext (by simp [boat,faceD,twinD])),exp_zero,Complex.exp_zero, show Pastry.hollow (n:=LeanV Γ) 1=1 from Subtype.ext (one_smul ..),one_mul,sub_self]; rfl
 obtain ⟨g',h',pt,hM⟩:= moves_e Z M p F i I I' Rt Vt O h hv hO hz hx L' g u t
 have hV: Allows n (fun y=> docS Z (M.atop (I y) x) (Rt y) (Vt y) r2 i) 0 (ζ L'.tip+L'.ego):=by
    refine (pt.add (Jet.allows_const _ (v:=(↑(xurn Z M i):ℂ)) (by rw [Complex.norm_real]; exact h'))).germ ?_; filter_upwards with z; exact Eq.trans (sub_add_cancel ..) (if_neg t).symm
 exact pylon _ _ _ _ hV (fun a b=> (hM a b).germ (Eventually.of_forall fun y=> Eq.symm (congrArg (fun A:Op Γ=>A a b) (show docA Z (M.atop (I y) x) (Rt y) r2 i=_ from if_neg t)))) -- tune polarity
end YM.CF.Iva
