import YM.CF.Iva.Law
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
local notation "ζ"=> Kplan n
open Fief
-- exact tranmission compressed. Pairs.Far integral Z(u')-Odd.Core. on controls synthetic stamp at any Z
local notation "dω"=> Directions SU.group (Domain N B)
local notation "L₀"=> (violet M)
local notation "N_"=> (violet M')
local notation "W'"=> wreath (Ba+1) i (ζ L'.puff)
abbrev glaze (Z:Muster G S x e T)(L':Wages)(i:Site (Domain N B))(n k:ℕ):= cull n (wreath (radiusB x+1) i (Kplan n L'.puff)) (Kplan n L'.tip+ L'.ego)
variable (ℱ ℳ:E→ Rent0 G e)(w₀:∀ᶠ i in 𝓝 (0:E), Muster.Post Z ((violet M).atop (I i) x) ((violet M').atop (I' i) x) (ℱ i) (ℳ i) (F ((violet M').atop (I' i) x)) (F (Cay.rough ((violet M').atop (I' i) x) 0)) k O) (z':LampM Z (violet M') F i r2 n L')
include p h g hv hz hx hO
lemma art_r(y:i∉ M.key.dome r2)(s:E)(B₁ b:ℝ): let A:=xurn Z M i; let C:=Pastry.hollow (n:=LeanV Γ) (Complex.exp A) ; elk Z (M.atop (I s) x) (Rt s) (Vt s) r2 k B₁ b (.inr (.inl i))=(C-1)+C*creed Z (M.atop (I s) x) (Rt s) (Vt s) r2 n i:=by
 intro a u; let P:=Zn s; unfold elk sweetK; simp only [Xb,Fa,Sum.elim_inr,Sum.elim_inl,docS,docA] -- tune
 simp only [if_neg (show i∉ (Zn s).key.dome r2 from y),treeL,creed];
 let z:=idyl (poll Z P i (Rt s) (Vt s)) (maskS Z (Rt s) i)
 rw [show idyl (Z.burnS P (Rt s) (Vt s) i) (maskS Z (Rt s) i) = Pastry.hollow a+ z from ?_]; letI : NormedAlgebra ℚ (ribbon Γ):=NormedAlgebra.restrictScalars ℚ ℝ (ribbon Γ)
 rw [exp_add,←yeaH]; change u * exp z - 1 = (u-1)+u*(exp z-1); ring -- tune
 unfold z idyl poll; rw [← add_assoc,← horn_s]; have he: xurn Z P i = a:= rfl; rw [he]; abel -- proof target parse
include w₀ ℳ ℱ z'
lemma even_h (hu:Beat.shadows (o:=i) O k₀)(y:i∉M.key.dome r2)(η:0≤L'.span): let A(y):=creed Z (M.atop (I y) x) (Rt y) (Vt y) r2 n i; let Q(y):=creed Z ((violet M).atop (I y) x) (ℱ y) (ℳ y) r2 n i; let H:=cull n W' (ζ L'.tip)
 Rigid A n 0 (Rue.saber H 1) ∧ Rigid Q n 0 (Rue.saber H 1) ∧ Rigid (fun y=> A y+ Q y) n 0 (tide n W' (wreath (Ba+1) i (ζ L'.span)) (ζ L'.tip) (ζ L'.spring)):=by
 intro A Q H; obtain ⟨hp,hk,z1,z2⟩:= moves_e Z M p F i I I' Rt Vt O h hv hO hz hx L' g hu y; obtain ⟨r,d,u,v⟩:= moves_e Z L₀ (M':=N_) p F i I I' ℱ ℳ O w₀ hv hO hz hx L' z' hu y
 have U:=opens_g _ _ _ _ z1 z2; have V:=opens_g _ _ _ _ u v; refine ⟨wiser U,wiser V,evenP _ _ _ _ z1 z2 u v ?_ ?_⟩; obtain ⟨_,_,t,w⟩:=g.leap hp
 · refine (hg_k I' hv _ _ t).germ ?_; filter_upwards [h,w₀] with i' p' hp; dsimp only [Function.comp_apply]; apply congrArg₂ (·+·)
   · exact (congrArg₂ (fun x (y:ℝ)=>x-(y:ℂ)) (fisc Z _ _ _ J0 k k₀ _ p'.duo p.ash p.ages i p'.kindB p.hunter hu _ p.trih p.beta p.pole p'.port p'.noth) (artB Z _ p'.duo p.ash p.ages i k₀ hu p.hunter.tag)).symm
   exact (congrArg₂ (fun x (y:ℝ)=>x-(y:ℂ)) (fisc Z _ _ _ J0 k k₀ _ hp.duo p.ash p.ages i hp.kindB p.hunter hu _ p.trih p.beta p.pole hp.port hp.noth) (artB Z _ hp.duo p.ash p.ages i k₀ hu p.hunter.tag)).symm
 intro l r; refine ((hg_k I' hv _ _ ((g.leap hp).2.2.2 l r)).mono (bally i _ _ η).le).germ ?_; filter_upwards [h,w₀] with i' p' hp'
 let Y:=halo (radiusB x+1+k) {i}; have hh:Y⊆ O:= (Corona.halo_mono p.hunter.line (Subset.refl _)).trans hu
 let t:= peg Z _ _ p.trih p.ferr i _ p'.port hh; let t':= peg Z _ _ p.trih p.ferr i _ hp'.port hh; exact congrArg₂ (·+·) (congrArg (fun A: Op Γ=> A l r) t).symm (congrArg (fun A: Op Γ=>A l r) t').symm
end YM.CF.Iva
