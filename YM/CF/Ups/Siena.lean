import YM.CF.Ups.Rain
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
variable{N P B:Side}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
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
structure Psalm_P (b:ℝ) where
 month:Month b a i p N0 V W
 life:MeterQ V a p i N0 J q h R0 δ b month
 D: Cape (oYY V N0 J b) B R.L
 L0:∀ l:ℕ,SpanPS V a p i N0 J q h R0 δ b l
 peace: CoilPS V a p i N0 J q h R0 δ month L0 D
 beta:ℕ→ℝ
 wave:ℕ→Haro.SpaceM
 Kb:∀ j:ℕ,InkPS (cell (oYY V N0 J b) B R.L j)
 σ:ℕ→ℕ
 mark:ΦS_P V a p i N0 J q h R0 δ L0 D beta wave Kb σ
local notation "Ψ_"=> Psalm_P V a p i N0 J q h R0 δ
universe a0
structure CantorPS :Prop where
 rise(Ps:ℝ):∃ x:ℝ,Ps<x∧ Nonempty (Psalm_P V a p i N0 J q h R0 δ x)
 path {X:ℕ→ℝ}(u:Tendsto X atTop atTop)(S:∀ i',Psalm_P V a p i N0 J q h R0 δ (X i')): let D(y):=cell (oYY V N0 J (X y)) B R.L 0; (∃ R:ℕ→ℝ, Onyx.Yard D R)∧∀ (α:Type a0)(F:ℕ→ℝ),Onyx.Yard D F →∀ (o:∀ i:ℕ,Site (D i))(E:Emu.Plot α F)(H:List α), Tendsto (fun i:ℕ=> remark (Pyx.plume (Roe.optV F i _ (o i) E H)) ((S i).Kb 0)) atTop (𝓝 (Emu.runes E.rho H))
variable (S:∀ i',Psalm_P V a p i N0 J q h R0 δ (x' i')) (Wk:∀ (L:ℕ→ℕ) (U:∀ i',SpanPS V a p i N0 J q h R0 δ (x' i') (L i')), WeaveC.{a0} V a p i N0 J q h R0 δ U)
local notation "Ωj" j=> cell (oYY V N0 J (x' j)) B R.L 0
include Wk S
lemma arbor(α:Type a0)(F:ℕ→ℝ)(T:Onyx.Yard (fun j=>Ωj j) F) (o:∀ j:ℕ,Site (cell (oYY V N0 J (x' j)) B R.L 0))(E:Emu.Plot α F)(H:List α): Tendsto (fun i:ℕ=>remark (Pyx.plume (Roe.optV F i _ (o i) E H)) ((S i).Kb 0)) atTop (𝓝 (Emu.runes E.rho H)):=by
 let O(z:ℕ):= Roe.optV F z _ (o z) E H; let f(z):= remark (plume (O z)) ((S z).Kb 0); let Y(z:ℕ)(l:ℕ):= (S z).L0 ((S z).σ l); let v(z l:ℕ):=(∫ y,Roe.getF (O z) ((Y z l).E 0) U ((S z).D 0) y ∂city _)/partitionZ ((Y z l).E 0) U ((S z).D 0)
 have ht(z): Tendsto (v z) atTop (𝓝 (f z)):=cardZ V a p i N0 J q h R0 δ _ _ _ (S z).peace (S z).mark 0 (O z)
 let w(z:ℕ):ℝ:= ((z:ℝ)+1)⁻¹; have hw(z):0 < w z:=by unfold w; positivity
 choose l hx using fun z=>(Metric.tendsto_nhds.mp (ht z) (w z) (hw z)).exists
 have he: Tendsto (fun z:ℕ=>v z (l z)) atTop (𝓝 (Emu.runes E.rho H)):= ((Wk _ (fun z:ℕ=>Y z (l z))).wick α F T o E H).2.congr fun i=> by dsimp only; unfold v; rw [← (show (Y i (l i)).Y=(S i).D from (S i).peace.tale _)]
 have ht0:Tendsto (fun i=> dist (v i (l i)) (f i)) atTop (𝓝 0):= squeeze_zero (fun _=>dist_nonneg) (fun i=>(hx i).le) (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
 apply tendsto_iff_dist_tendsto_zero.mpr; exact squeeze_zero (fun i=>dist_nonneg) (fun i=>(dist_triangle (f i) (v i (l i)) (Emu.runes E.rho H)).trans_eq (congrArg (·+ dist (v i (l i)) _) (dist_comm _ _))) (by simpa only [add_zero] using ht0.add (tendsto_iff_dist_tendsto_zero.mp he))
omit S Wk
lemma etna_θ(j k p:ℕ)(a:ℝ)(hk:6≤k)(hp:2≤p)(hj:4≤j)(u:Even j)(ha:0<a) : ∃ (K:Teller SU.group)(L:ChartRatio SU.group), K.j=j ∧ LocalRatio L ∧ K.top.clip.direct≤1 ∧∃ (C:ℝ)(n:ℕ),∀ (P:Patch),n≤ P.L.val→P.J=j→∃ (V:Grace K P L)(T:Acorn.Repair K.j)(l:ℕ),∀ B0:ℕ,l≤ B0→∃ e:ℝ,0<e∧∀ q:Chi,∀ d:ℝ,0<d→d≤e→∃ (U:Grasp V.U (P.L^B0) d)(W:GivenX V U)(M:Side)(J:Robes M V W),U.baseline ≤ T.d∧ J.k≤ J.roomX ∧ ∀ᶠ h:ℝ in atTop,∃ N:ℕ,Coffer (p:=p) (k:=k) V U W q a J.d J.n C N J.k J.roomX h∧ ∃ Q D:ℝ→ℝ,sizeK P.L 2 Q ∧ Chill_v D ∧ CantorPS.{a0} V a p k N J q h Q D ∧ (∀ x:ℝ,∃ z:ℝ,x<z ∧ ∃ S:Month z a k p N V W,MeterQ V a p k N J q h Q D z S) ∧ ∀ (f:ℕ→ℝ)(t:ℕ→ℕ),Tendsto f atTop atTop→∀ X:∀ i',SpanPS V a p k N J q h Q D (f i') (t i'), WeaveC.{a0} V a p k N J q h Q D X :=by
 obtain ⟨K,L,z,uK,h,C,N,Y⟩:=interval_C j k p a hk hp hj u ha; refine ⟨K,L,z,uK,h,C,N,fun P w t=>?_⟩; obtain ⟨V,T,n,hP⟩:=Y _ w t; refine ⟨V,T,n,fun B0 e=>?_⟩; obtain ⟨d,y,pD⟩:=hP B0 e; refine ⟨d,y,fun q d u v=>?_⟩; obtain ⟨U,W,M,J,hv,x,D⟩:=pD q d u v
 obtain ⟨c,b,w,F,r,s,i',⟨P⟩⟩:= Pic.crop0 W.pearl V.note (by omega) W.health; obtain ⟨Xk,Xr,Xp,Y,k',l,S_⟩:= Roe.portH P
 refine ⟨U,W,M,J,hv,x,?_⟩; filter_upwards [D,eventually_ge_atTop Xp,eventually_ge_atTop (1:ℝ)] with H Dg t v; obtain ⟨N,u,g⟩:=Dg; refine ⟨N,u,?_⟩; obtain ⟨Q,E,G,Z,h,h',u,g,w⟩:=g 0; refine ⟨Q,Z,h,g,?_,w,fun f t' p' X=> grip_s V a p k N J q H Q Z p' X v P S_ t⟩

 constructor
 · intro Ps; obtain ⟨u,hq⟩:=eventually_atTop.mp (Ωnorm V a p k N J q H Q Z v P S_ t); obtain ⟨x,u',T0,Y⟩:= w (max 1 (max u Ps)); obtain ⟨ℓ,i,w⟩:= hq x ((le_max_left u Ps).trans ((le_max_right ..).trans u'.le)); have hx:0<x:=zero_lt_one.trans ((le_max_left ..).trans_lt u')
   obtain ⟨X,T,hT⟩:= ψ_C V a p k N J q H Q Z T0 Y v i hx w
   obtain ⟨β,A,G,t',g⟩:=sol_g V a p k N J q H Q Z T0 hx X T hT
   exact ⟨x,(le_max_right ..).trans_lt ((le_max_right ..).trans_lt u'),⟨⟨T0,Y,T,X,hT,β,A,G,t',g⟩⟩⟩
 intro X s Hp D; let pZ: ∀ (L:ℕ→ℕ)(U:∀ i', SpanPS V a p k N J q H Q Z (X i') (L i')), WeaveC.{a0} V a p k N J q H Q Z U:= fun t' S=> grip_s V a p k N J q H Q Z s S v P S_ t
 refine ⟨(pZ (fun _=>0) (fun i=> (Hp i).L0 0)).see,fun α F u o Y=> arbor V a p k N J q H Q Z Hp pZ α F u o Y⟩
end YM.CF.Py
