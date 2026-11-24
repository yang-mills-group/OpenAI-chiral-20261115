import YM.CF.Plume.Green

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Plume
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B))(x:ℝ)
local notation "G₀"=> SU.group
local notation "n₀"=> (Domain N B)
local notation "m₀"=> (Domain P B)
local notation "Tabs"=>Arena.Tab S
variable{S}
open scoped Classical ENNReal NNReal
open Girt Next.Fluctuations.Sector Dial
open Lich
-- active Modes: for Shape Y plan agreement full on X.
variable{k b l k1 k' o₁ o₂ r r' j:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]
local notation "bay"=> Stilo.bay
variable {X: Support (Domain N B)}{H H':Ride S}
variable{G:Ratio (mid N B) (mid P B)}{e:ℝ}{Q:GramM (mid P B)}
set_option pp.universes false
variable {V V':Orbit (mid N B)}{y y':Cord S}{K K':Ids (mid P B)}
variable {X0:ι→Palot.leaf (Site (Domain N B))}{i:Troupe S r ι}{t:ℝ}
local notation "U₀"=> cort V.1 y
local notation "U'"=> cort V'.1 y'
local notation "AX"=> BranchX S X0 k
local notation "ScopeF"=> Passage S
variable (h:Spark (Stilo.bay H) y y')(p:Palot.fits (BranchX S X0 k) i H)
variable {A₀:Side}{e:ℝ}{j κ n μ:ℕ}{ho:Odd A₀.val}{Y:Pricing j A₀ ho (Thread j)}{P':Grasp Y B e}{M:Male}{I:Aim (mid P B)}{I':Pec.Pride (mid P B)}{v v' g g' t t' w Z α ι₀:ℝ}
variable (A: Dress G S e r k' (cort V.1 y) Q k X0)(B':Dress G S e r k' (cort V'.1 y') Q k X0)
local notation "µ"=>A.wage
local notation "t₀"=>A.coats i
local notation "t₁"=>B'.coats i
variable {q:Chi}{T:Tube SU.group S}
variable {F:Scree.Loom (mid N B)}{W:Scree.Loom (mid P B)}{x w' o u cψ h₀ K₂:ℝ}{l0:ℕ}
-- structure pre campaign concrete watchers.B.Period.Always localized.
open Muster
variable {F₁: nomA N P B→ Op (Single (mid N B))}{Φ:nomA N P B→ℂ}
variable (D:Muster G S x e T) (B2 :Muster.Gard D r r' b k (a:= v) (a':=v') (C:=g) (D:=g') (n:=n) (J:= F₁) (Z:=Z) (Φ:=Φ) (R₁:= j) (c:=α) («v»:=w)) -- name?
variable {t₀_ A₁ A₂ a₁ b₁ c d d':ℝ}
lemma masks_l (a₀: Eire.Dress G S e r k' U₀ Q k (D.mapV b))(b₀:Eire.Dress G S e r k' U' Q k (D.mapV b)) (K K':Stores S → Rill.Arch G e)(h:a₀.portG=b₀.portG)(h':a₀.portT=b₀.portT)(hv:a₀.dyes=b₀.dyes)(ht:a₀.pens=b₀.pens)(hu:a₀.wage=b₀.wage)(ht':a₀.chi=b₀.chi)
 (c:Belf a₀ u t t' o w' A₁ A₂ w x t₀_ D.post k1 o₁ q F W T K)(c': Belf b₀ u t t' o w' A₁ A₂ w x t₀_ D.post k1 o₁ q F W T K')
 (Y_:Vista P' M I a₀.pens μ b₁ a₁ d d') (R:Pec.Pride (mid P B))(q':Dyes Z e R μ a₀.dyes w t')
 (L t₁_ w:ℝ)(f: Agrees (bay H) V.1 V'.1)(s:Set.EqOn V.2 V'.2 (bay H))(g: Spark (bay H) y y') (p:(bay H)∩flags (temp x) V.1= (bay H)∩flags (temp x) V'.1) (i: Troupe S r (Words S)): let C:= D.ruin _ _ a₀ L t₁_ w B2 K; let E:= D.ruin _ _ b₀ L t₁_ w B2 K'; C.blazon x D.post i H= E.blazon x D.post i H:=by
 intro A B'
 let φ:=BranchX (r:=r) S (D.mapV b) k; by_cases z:Palot.fits φ i H; swap
 · have ht(Z:Eire.Dress G S e r k' U₀ Q k (D.mapV b)):Z.blazon x D.post i H=0:=by by_contra w; unfold Dress.blazon at w; split at w; exact z (fuelFit _ _ w); contradiction
   rw [ht A]; symm; by_contra w; unfold Dress.blazon at w; split at w; exact z (fuelFit _ _ w); contradiction
 let U:= p; have hw:flags (temp x) V.1 ∩ bay H= flags (temp x) V'.1 ∩ bay H:=by rw [inter_comm, p,inter_comm]
 let X:=i.toLeft; let W0:=Eire.capG S (flags (temp x) V.1) (chillB U₀) Q.p.threshold i H; let W1:=Eire.capG S (flags (temp x) V'.1) (chillB U') Q.p.threshold i H; have ht₁:W0↔ W1:=by unfold W0 W1 Eire.capG; rw [hw, earned (S:=S) (V:=V) (V':=V') (t:=Q.p.threshold) g z]
 unfold Dress.blazon; by_cases p':W0; swap; · exact (if_neg p').trans (if_neg (mt ht₁.mpr p')).symm
 have hh:= ht₁.mp p'
 trans Scion.vigor (A.stageT x D.post i) H; exact if_pos p'; refine Eq.trans ?_ (if_pos hh).symm
 obtain ⟨k'',u⟩:= shape_g g z a₀ b₀ c c' hu ht' f s p'
 obtain ⟨_,_,α'⟩:=Dress.Ion a₀ x D.post c.warm i z p'; obtain ⟨_,_,β⟩:=Dress.Ion b₀ x D.post c'.warm i z hh
 have hg:= vestX g z a₀ b₀ α' β R Y_ q' hv ht k'' c.cloth c'.cloth c.wage c'.wage
 refine knot_s x A B' k'' h' h hg ?_ (shades_l x g z a₀ b₀ f c.warm.wear c.warm.years c.warm.pole (c.peg.trans c'.peg.symm) hu ht' c.cloth c'.cloth)
 let Yw:= Eire.trot S U₀ (penn S i); let Z':= Eire.trot S U' (penn S i); let Yw':= a₀.coats i; let Z0:= K (penn S i); let Zq:= b₀.coats i; let ZQ:=K' (penn S i)
 have he: Muster.Post D Yw Z' (onK Yw') (onK Z0) (onK Zq) (onK ZQ) k (bay H):=⟨sail g f _,g.sharesB,D.panelV _ _ _ k'',D.panelV _ _ _ u⟩
 unfold Dress.brew; dsimp only; apply congrArg₂ (· * ·)
 · apply prod_congr rfl; intro j v; obtain ⟨i',t,rfl⟩:=mem_image.mp v; exact D.roofH _ _ _ r r' k b t₁_ w L B2 he _ (litG S _ z _ t)
 apply prod_congr rfl; intro j v; exact D.roofX _ _ _ r r' k b t₁_ w B2 he j (lodX S _ z _ (mem_toRight.mp (mem_toRight.mp v)))
-- at fixed V.Plot. all FTC. 
end YM.CF.Plume
