import GaugeFieldConstruction.Moire
import GaugeFieldConstruction.Gateveil
import GaugeFieldConstruction.Melo
import GaugeFieldConstruction.Bower
import GaugeFieldConstruction.Prairie
import GaugeFieldConstruction.Lepta
import GaugeFieldConstruction.Retic
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
section
open Prism Tap FlightFlux TableF Boom Axon
open Lenten.ModuleB Flot Taxi
open Planned.PrimaryIntegral295
variable {N P B J : Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S} {Xs:GramM (mid N B)}{Y:GramM (mid P B)}(p:BudgetPoint){s ξ μ k x σ C:ℝ}{R:Patch}
variable {i:Roc (mid P B)} {W:tangD (mid N B)→ tangD (mid P B)}
variable {m:ℕ}(hB:Beacon (R:=R) (T:=T) (x:=x) (Xs:=Xs) (Y:=Y) 1 i s W 1 ξ)
variable (A:Support (Domain N B))(hA:A=halo (1000*radiusB x) {S.ratio.parent i.1.val.1})(g:Gatehouse Xs Y σ C x m T)(u:i.1.val.2 ⊆ halo 24 {i.1.val.1})
-- A Rebound directions. u=v test light
abbrev fontY (K:Support (Domain N B))(U:tangD (mid N B)): tangD (mid N B):= Manor Xs.p (S.ratio.parent i.1.val.1) K (radiusB x) U
abbrev CurlW (K:Support (Domain N B))(F:tangD (mid N B) → tangD (mid P B)):= F ∘ Bindδ (temp x) (S.ratio.parent i.1.val.1) Xs.p K (radiusB x)
variable (hs:1 ≤ s)
include hB g hs hA
lemma cogB 
    (n:ℕ)(v:n ≤6)(V:Fin n→tangD (mid N B))(p:∀ j,Xs.p.dirBound (S.ratio.parent i.1.val.1) (V j)) : Sized (4*s) (iteratedFDeriv ℝ n (CurlW (x:=x) (S:=S) (i:=i) (Xs:=Xs) A W) 0 (fun i'=>fontY (x:=x) (i:=i) (S:=S) (Xs:=Xs) A (V i'))) Y.p i.1.val.1:=by
 let Z:= i.1.val.1; let I:= S.ratio.parent Z; let R':=Bindδ (temp x) I Xs.p A (radiusB x); let U':=(fun i'=> highlight A (V i')); let V':= Manor Xs.p I A (radiusB x)∘ V -- type
 let a:ℝ:=(R.L.val:ℝ)⁻¹; have hp:0 ≤a:=by unfold a; positivity
 have ha:a ≤1:=inv_le_one_of_one_le₀ (by exact_mod_cast R.L.property)
 have he:= (hB.touch.releases n v U' (fun j=> highlight_D Xs.p _ _ _ (p j)))
 change Sized (4*s) (iteratedFDeriv ℝ n (W∘ R') 0 V') _ _; rw [Next.Foundations.jets_linear R' (hB.touch.smooth.of_le (Nat.cast_le.mpr v)), ContinuousMultilinearMap.compContinuousLinearMap_apply]; have hh(j): R' (V' j)=U' j:=by unfold R'; rw [smul_apply,←g.tempo]; exact reprV _ _ _ _ (hA.symm ▸ halo_subset _ _ (mem_singleton_self _)) _ -- fill
 rw [show (fun i=>R' (V' i))=U' from funext hh]; exact sizedMonoι (payφ _ hp ha hs he) (mul_le_of_le_one_right (by linarith) ha)
omit hB hs g hA
open Carrier FlightFlux.Fluxim
variable (f:Flight 4 4)(pθ:S.ratio.count=f.L)(sf0:HEq (linesOf f k) T.R.A0) (p0:0<k)
include pθ sf0 p0
abbrev Λgear (m:ℕ)(T S:ℝ)(c:Side):ℝ:=unitStep c ^(m+1)*(T/S)
lemma traceG (F: Wheel Axis SU.group.Color)(n:ℕ)(h:0<n)(u:n ≤2)(pF:∀ i,Paper (n+1) (F i)) (X:GramM (mid N B)) (Y:GramM (mid P B)) (i:Roc (mid P B)):Blade n i.1 (camW i.1.val.1 (Arrow (T:=T) (Xs:=X) i F)- Λgear n X.p.threshold Y.p.threshold S.ratio.count • plot i.1.val.1 F Y.p.threshold):=by
 let Tρ:= X.p.threshold; let Z:= Arrow (T:=T) (Xs:=X) i F; let z:= unitStep S.ratio.count; let F':= Tρ • F; let v:= z^(n+1)
 have hp:= lead_degree p0 f F' (Lattice.lift (S.ratio.residue i.1.val.1)) n h u (fun i=> (FlightFlux.school Axis ℝ _ _).smul_mem Tρ (pF i)) _ pθ.symm sf0
 refine ⟨Z-v • F',hp,fun j a b=>?_⟩; let s:=Y.p.threshold; rw [Pi.sub_apply]; unfold camW FlightFlux.plot;
 simp_rw [Pi.sub_apply,Pi.smul_apply]; let H:=FlightFlux.stem i.1.val.1 j.1; change Z j.2 H-v • Tρ • F j.2 H=Z j.2 H-(v*(Tρ/s)) • s • F j.2 H; rw [smul_smul,smul_smul, mul_assoc,div_mul_cancel₀ _ Y.p.threshold_pos.ne']
omit pθ sf0 p0
variable (E: InkD (mid P B)){h c:ℝ}(P₀:PressB Y.p i.1 E h c) (hq:0≤h)
include hB g hs hA u hq P₀
-- Hess bill.Arbitrary Table.Don't assume symmetry of loams
abbrev GauDebt(w s ξ δ:ℝ):= xHoch 6*(ξ*(4*s)^2)*w+xHoch 6*(ξ*(4*s))*w + mToll (4*s) δ*w
lemma bowCost (F H:Wheel Axis SU.group.Color)(v:Carries (Function.swap F) 3 1)(l:Carries (Function.swap H) 3 1)(pF:Xs.p.dirBound (S.ratio.parent i.1.val.1) (plot (S.ratio.parent i.1.val.1) F Xs.p.threshold))(pH:Xs.p.dirBound (S.ratio.parent i.1.val.1) (plot (S.ratio.parent i.1.val.1) H Xs.p.threshold))(δ:ℝ)(hx:leadDue ξ σ C Xs.p Y.p S.ratio.count m ≤ δ)(he:0 ≤ δ): let V:=S.ratio.parent i.1.val.1; let p(X:Wheel Axis SU.group.Color) :=fontY (S:=S) (Xs:=Xs) (i:=i) (x:=x) A (plot V X Xs.p.threshold); let Y'(F):=camW i.1.val.1 (Arrow (T:=T) (Xs:=Xs) i F); ‖iteratedFDeriv ℝ 2 (term E ∘ (CurlW (S:=S) (x:=x) (Xs:=Xs) (i:=i) A W)) 0 ![p F,p H]-ploy E (Y' F) (Y' H)‖ ≤ GauDebt c s ξ δ:=by
 intro V r' H'
 let Z:=CurlW (S:=S) (x:=x) (Xs:=Xs) (i:=i) A W; let x₀:= plot V F Xs.p.threshold; let y₀:= plot V H Xs.p.threshold; let U(F):= fderiv ℝ Z 0 (r' F); let Qx:=iteratedFDeriv ℝ 2 Z 0 ![r' F,r' H]; let ω':= 4*s; let Pf:= term E; let I:= i.1.val.1;
 have hz: Z 0=W 0:=by unfold Z CurlW; rw [Function.comp_apply,map_zero]
 have ho: Chamber i.1 Y.p (W 0):=hB.touch.home -- tune sequencing syntax
 have ht:ContDiffAt ℝ (2:ℕ∞ω) Z 0:= (show ContDiffAt ℝ (6:ℕ∞ω) _ _ from ContDiffAt.comp 0 (f:= (⇑(Bindδ (temp x) V Xs.p A (radiusB x)))) (g:=W) (by rw [map_zero]; exact hB.touch.smooth) (by fun_prop)).of_le (by decide)
 have hy(m):∀ a:Fin m→ tangD (mid N B), m≤6→ (∀ j,Xs.p.dirBound V (a j)) → Sized ω' (iteratedFDeriv ℝ m Z 0 (fun i'=>fontY (x:=x) (i:=i) (S:=S) (Xs:=Xs) A (a i'))) Y.p I:= fun a t v=>cogB hB A hA g hs m t a v -- tune
 have hQ(U':Wheel Axis SU.group.Color)(v:Xs.p.dirBound V (plot V U' Xs.p.threshold)):Sized ω' (U U') Y.p I:=by
    have hp:= hy 1 (fun _=> plot V U' Xs.p.threshold) (by decide) (fun _=>v); rw [iteratedFDeriv_one_apply] at hp; exact hp
 have hv₂:= hy 2 ![x₀,y₀] (by decide) (fun i=>by fin_cases i; exact pF; exact pH); have htξ: Sized ω' Qx Y.p I:=by
    rw [show (fun j=>fontY (x:=x) (i:=i) (S:=S) (Xs:=Xs) A ((![x₀,y₀]:Fin 2→_) j))=![r' F,r' H] from funext fun i=>by fin_cases i <;>rfl] at hv₂; exact hv₂
 have hτ(t:ℝ)(h:t∈Set.Icc (0:ℝ) 1):=eraF E i.1 P₀ hq _ (ho.2 t h); have ha(x y:Pane (mid P B))(u:Agrees i.1.val.2 x y):lifeH E x=lifeH E y:=congrArg Pastry.pane (P₀.term x y u)
 have hF' : ContDiffAt ℝ (2:ℕ∞ω) Pf (Z 0):=by
    rw [hz]; have ht:=hτ 1 (by simp); rw [one_smul] at ht; exact (stirring 1 _ ha _ ht).of_le (Nat.cast_le.mpr ((by omega:2 ≤6).trans Y.p.order_ge))
 have hT:= begin_X hB
 have hg : ‖fderiv ℝ Pf (W 0) Qx‖ ≤ xHoch 6*(ξ*(4*s))*c:=by
    let Ut(j:Fin 1):=Qx; have hg:=chamber_B (W 0) ho Ut (fun _=> ω') (by decide) hτ ha hT (fun i=>htξ); rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,show fderiv ℝ (lifeH E ∘ RG.increment 1) 0=0 from censored P₀ hq,_root_.zero_apply,sub_zero,Fin.prod_univ_one] at hg; exact hg -- tune
 rw [second_m hF' ht,hz]; let U':= U F; let V':=U H; let Hu:= H' F; let Hv:= H' H
 have hv:= hQ F pF; have hU:= hQ H pH
 let Q':=![U',V']; let V:= iteratedFDeriv ℝ 2 Pf (W 0) Q'; let C:= fderiv ℝ Pf (W 0) Qx -- shadows
 have hh: ‖V-ploy E U' V'‖≤ xHoch 6*(ξ*ω'^2)*c:=by
    let h(j:Fin 2):= ω'; rw [ploy_iter]; have he:= chamber_B (W 0) ho Q' h (by decide) hτ ha hT (fun i=>by fin_cases i; exact hv; exact hU); rw [show ∏ i,h i=ω'^2 from (by unfold h; simp)] at he; exact he
 have hb:= mul_le_mul_of_nonneg_right hx Y.p.threshold_pos.le
 have hu:= refract P₀ hq hv hU he (fun j p=> ((arrowing hB A hA g u F v pF j p.1).trans hb)) (fun j p=> ((arrowing hB A hA g u H l pH j p.1).trans hb)) -- tunes
 change ‖V + C - ploy E Hu Hv‖ ≤ _; rw [show V+C-ploy E Hu Hv=(V-ploy E U' V'+C)+(ploy E U' V'-ploy E Hu Hv) from (by abel)]; apply (norm_add_le ..).trans; exact add_le_add ((norm_add_le ..).trans (add_le_add hh hg)) hu
end
end YM.CF.Oath
end
