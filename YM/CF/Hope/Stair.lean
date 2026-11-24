import YM.CF.Hope.Story
import YM.CF.Feu.Jack
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hope
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione Beau
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
variable {F G:InkD n}{X₀:Scree.Hub n}
local notation "sR"=> X₀.val.2
local notation "sO"=> X₀.val.1
local notation "Fη"=> (Scree.tariff P sO h)
variable(p:PressB P X₀ F h a)(q:PressB P X₀ G h b)(hv:0 ≤ h)
abbrev Oars (P:BudgetPoint)(X:Scree.Hub n)(F:InkD n)(h d:ℝ):Prop:= ∃ b: Raid (Dwell n),0≤b∧(∀ V:Pane n,pingS P.threshold X.val.2 V→ Rue.Rigid (fun x:tangD n=> F (increment V (Prism.trunk P X.val.1 x))) P.order 0 b) ∧ joinV (Scree.tariff P X.val.1 h) b≤ d
lemma σlend (W:Raid (Dwell n))(a:ℝ): joinV Fη (a • W) = a*joinV Fη W:=by simp only [joinV,Pi.smul_apply,smul_eq_mul,mul_left_comm (Fη _) a, Finset.mul_sum]
local notation "oar"=> (↑N+1:ℝ)
local notation "ξ"=> (P.order.factorial:ℝ)
include p in
lemma oar_K : Oars P X₀ F h (oar * a):=by
 obtain ⟨b,u,hh,hk⟩:=p.worth; refine ⟨oar • b, (fun i=>mul_nonneg (show 0≤oar by positivity) (u i)),fun i g=> ⟨Eventually.of_forall fun _=> (fineShape _).allP,fun j=>?_ ⟩, ?_⟩
 · let f:= fun y:tangD n=> crumb (F (increment i (trunk P sO y))).val j; exact Rue.bare_p _ _ (skin (hh i g j)) -- ambiguous
 rw [σlend]; exact mul_le_mul_of_nonneg_left hk (by positivity)
lemma wake (u:Oars P X₀ F h d) : ∃ b:Finset (Dwell n)→ℝ,(∀ i,0≤b i)∧ (∀ U,BedP P U F X₀ b) ∧ joinV Fη b≤ ξ*d:=by
 obtain ⟨b,g,s,t⟩:=u; refine ⟨ξ • b,fun i=>mul_nonneg (Nat.cast_nonneg _) (g _),fun x p i=>Prism.skills ((s x p).haveP i).pay,?_ ⟩; rw [σlend]; exact mul_le_mul_of_nonneg_left t (Nat.cast_nonneg _)
include p in
lemma hi_p (b:a≤ d): PressB P X₀ F h d:=by obtain ⟨e,v,m,h,k,z,p,x⟩:=p; exact ⟨e,v,m,h,k,z,p,x.trans b⟩
include hv
include p q in
lemma peer_P : PressB P X₀ (F*G) h (ξ*((oar*a)*(oar*b))):=by
 refine ⟨fun x y t=>congrArg₂ (·*·) (p.term x y t) (q.term x y t),fun i=>(p.fitted i).mul (q.fitted i),p.measureV.mul q.measureV,fun i v=>(congrArg₂ (·*·) (p.gaugeV i v) (q.gaugeV i v)).trans (map_mul ..).symm,wake (P:=P) (F:=F*G) ?_ ⟩
 obtain ⟨b',g,w,v⟩:=oar_K p
 obtain ⟨U,g',s,t⟩:=oar_K q; let W:= Feu.verge_l sO h hv P
 refine ⟨_,skirtPos b' U g g',fun x pt=>?_ ,?_⟩
 · let D(x':InkD n)(y:DN):= x' (increment x (trunk P sO y)); exact (show Woody P.order ((fun y=>(D F y).val)*(fun y=>(D G y).val)) 0 (skirt b' U) from (w x pt).pairP (s x pt))
 exact (turnS W _ _ g g').trans (mul_le_mul v t (show 0 ≤ joinV Fη U from sum_nonneg fun i _=>mul_nonneg (W.fee i) (g' i)) ((show 0≤ joinV Fη b' from sum_nonneg fun i _=>mul_nonneg (W.fee i) (g i)).trans v))
omit hv
include p
lemma shore_p (d:ℕ): LocalOn sR (F^d)∧(∀ i: Pane n, Flour (camp sR) ((F^d) i).val) ∧Measurable (F^d)∧∀ (i:Pane n)(v:Xo → SU.E),(F^d) (Lattice.gauge v i)=paintR false false (tradew _ v) ((F^d) i):=by
 refine ⟨fun x y h=> by simp only [Pi.pow_apply,p.term x y h], fun i=>?_ ,p.measureV.pow_const _,fun x y=>by rw [Pi.pow_apply,Pi.pow_apply,p.gaugeV, map_pow]⟩
 rw [Pi.pow_apply]; exact (stretch_ok _).mp ((Pastry.stretch _).pow_mem ((stretch_ok _).mpr (p.fitted i)) _)
include p hv -- note p must BEFORE shore
lemma powerF (m:ℕ): PressB P X₀ (F^m) h (ξ*(oar*a)^m):=by
 obtain ⟨u,v,g,k⟩:= shore_p p m; refine ⟨u,v,g,k,wake (P:=P) (F:=F^m) ?_⟩; obtain ⟨w,c,e,t⟩:=oar_K p; let W:=Feu.verge_l sO h hv P; refine ⟨bottles w m,b_nn c _,fun i h=>?_, (brew_p W c m).trans (pow_le_pow_left₀ (show 0 ≤ joinV Fη w from sum_nonneg fun i _=>mul_nonneg (W.fee i) (c i)) t _)⟩
 let K(y:DN):= F (increment i (trunk P sO y)); exact (show Rigid (fun x=> K x^m) P.order 0 (bottles w m) from boats (X:=K) (e i h) m)
lemma ν_P : PressB P X₀ (-F) h a:=by simpa using Ione.scale_E P p (-1) -- tune
lemma ε_P : PressB P X₀ (fun u=>exp (F u)-1) h (ξ*(Real.exp (oar*a)*(oar*a))):=by
 let T:= Cipher n; letI: NormedAlgebra ℚ T:= NormedAlgebra.restrictScalars ℚ ℝ (Cipher n)
 refine ⟨fun x y t=> by rw [p.term x y t], fun i=>?_,((exp_continuous (𝔸:=T)).measurable.comp p.measureV).sub measurable_const,fun i g=>?_ ,wake ?_⟩
 · let D:= stretch (camp sR); apply (stretch_ok _).mp; exact D.sub_mem (exp_mem (R:=ℝ) (show IsClosed (D:Set T) from D.toSubmodule.closed_of_finiteDimensional) ((stretch_ok _).mpr (p.fitted i))) D.one_mem
 · rw [map_sub,map_one,p.gaugeV]; let U':=paintR false false (tradew n g); exact congrArg (·-1) (map_exp U' U'.toLinearMap.continuous_of_finiteDimensional ..).symm -- tune
 obtain ⟨w,u,v,hK⟩:=oar_K p; let F':=Feu.verge_l sO h hv P
 refine ⟨saber w 1,(saber_r 1 u Fη F').1,fun x h=> wiser (v x h),?_⟩; exact (peony 1 u F').trans (by rw [pow_one]; exact mul_le_mul (Real.exp_monotone hK) hK (sum_nonneg fun i _=>mul_nonneg (F'.fee i) (u i)) (Real.exp_pos _).le)
end YM.CF.Hope
