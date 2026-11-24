import YM.CF.Vp929.Canon.MossL
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
-- Transfer averaging. Specialized budgets. Degree 0 and 2.
set_option quotPrecheck false
open Cycle929 Larch Bake Salt Trees Push.BetaTransport
variable {n:Side}{L:ℕ}{Q:BudgetPoint}{A h a c d v α σ C Λ k β j w:ℝ}
local notation "D'"=> RegBudget n
local notation "Hz"=> Scree.Hub n
variable {X Y:RegBudget n}{Z W:Cusp n}{R:PathData SU.group}{b:Clip}
local notation "ζ"=> Cash.prominence Q
lemma mobility (p:IncX Utrue X Q h a): Sym_P X:=by
 intro s; apply funext; intro i; apply funext; intro x; change suit_Y s⁻¹ (X (moveHub s i) (flashA s x))=_; rw [show X (moveHub s i) (flashA s x)=suit_Y s _ from p.face s trivial _ (spinZ ..) i x,moon_Y,mul_inv_cancel,toon_Q]
set_option maxHeartbeats 1500000 in
lemma pusher (Q:BudgetPoint)(B'Dash: Orbit n → Cipher n)(p:∀ (s:Sweep n)(x:Orbit n),B'Dash (yellA s x)=suit_Y s (B'Dash x))(h:∀ (x:Orbit n), Rue.FleetS Q.threshold x.1→ exponentL Q X x.1+fuelV Q W x=B'Dash x): ∀ x:Orbit n,Rue.FleetS Q.threshold x.1 → exponentL Q (writ_E X) x.1+fuelV Q (writ_K W) x=B'Dash x:=by
 intro x v; rw [Ione.light_D Q X x,Ione.polar_k Q W x,←smul_add,←sum_add_distrib]
 let M(j:Sweep n):= exponentL Q X (yellA j x).1; let D(j:Sweep n):=fuelV Q W (yellA j x); have hp1(s:Sweep n) : M s+D s=suit_Y s (B'Dash x):=(h (yellA s x) (skew_V s x.1 Q.threshold v)).trans (p s x)
 have h₀(s:Sweep n):suit_Y s⁻¹ (M s)+suit_Y s⁻¹ (D s)= B'Dash x:=by rw [←map_add,hp1,moon_Y,mul_inv_cancel,toon_Q]
 change plight_C n • (∑ j:Sweep n,(suit_Y j⁻¹ (M j)+suit_Y j⁻¹ (D j)))=B'Dash x; simp_rw [h₀]; exact oath_r n (B'Dash x)
lemma fieldCare (u:Cease Q R b α v σ C Λ n)(p:PackSale Q R b X W a): PackSale Q R b (writ_E X) (writ_K W) a:=by
 apply pusher Q (fun i=>moldV n (a*kinetic R b Q i.1)) _ p; intro s x; let E:= a*kinetic R b Q x.1; rw [show kinetic R b Q (yellA s x).1= _ from tune_E Q R u.mass u.span u.rare s x.1]; change E • (1:Cipher n) = suit_Y s (E • (1:Cipher n)); rw [map_smul,map_one]
lemma anyTwoYear (p:Packed Q h d Z a)(u:Mono_W Z)(q:0≤h): Packed Q h d (writ_K Z) (pack_Q Q.order*a):=by obtain ⟨x,h,f⟩:=p; exact ⟨_,memo_P _ x Q h u q, family_Q x f _⟩
lemma stead_m (G:Cusp n): ZealQ (writ_K G):= fun s V v=> tree_y _ (spin_M G) s V
lemma zero_m:Sym_M (0:Cusp n):= fun s=> funext fun i=> funext fun _=> funext fun _=> map_zero (suit_Y s⁻¹)
lemma zero_r:Sym_P (0: D'):= fun s=> funext fun i=> funext fun _=> map_zero (suit_Y s⁻¹)
/-- Exact degree projection. These two versions of the swept transfer are the only
 ones needed; use wages 0 and 2. Their charges are still uniform. -/
def GSingle (X:D'):Prop:=head_L X=0
lemma paid0 : GSingle X ↔∀ i:Hz,∀ V:Pane n,cut_V (X i V)=0:= ⟨fun v i V=> congr_fun (congr_fun (show head_L X=0 from v) i) V,fun v=>funext fun i=>funext (v i)⟩
lemma scalar_sweep (p:IncX primeU X Q h a)(v:GSingle X)(q:0≤h): IncX Utrue (writ_E X) Q h (cone_D Q.order Q.power*a):= lake_X Q X p (Eq.symm (show head_L X=0 from v) ▸ zero_r) q
lemma packed_scalar (p:Packed Q h d Z a)(s:veil_M Z=0)(q:0≤h): Packed Q h d (writ_K Z) (a+tray_H Q.order*a):=by obtain ⟨x,u,w⟩:=p; refine ⟨_,yarn_R Q _ x u (s.symm ▸ zero_m) q, fun i=>?_⟩; rw [Larch.tall_add]; exact add_le_add (w i) (strait_G x w Q.order i)
lemma keys : veil_M Z=0↔∀ i:Aura n,∀ D:Support (More n),∀ V:Orbit n, cut_V (Z i D V)=0:=⟨fun h i D V=> congr_fun (congr_fun (congr_fun h i) D) V, fun h=>funext fun i=>funext fun D=>funext (h i D)⟩
lemma plus_single (g:GSingle X)(h:GSingle Y):GSingle (X+Y):=paid0.mpr (fun i V=> by simp only [Pi.add_apply,map_add,paid0.mp g,paid0.mp h,add_zero])
lemma plus_veil (v:veil_M Z=0)(t:veil_M W=0):veil_M (Z+W)=0:=keys.mpr (fun i D V=>by simp only [Pi.add_apply,map_add,keys.mp v,keys.mp t,add_zero])
variable {F: Scree.Hub n→ Scree.Hub n}(p:Extension L Q n F)
lemma scalar_warp (t:GSingle X): GSingle (warp_E F X):=paid0.mpr (fun i V=>by unfold warp_E sunY; simp only [Finset.sum_apply,map_sum,paid0.mp t,sum_const_zero])
lemma budTwo (u:∀ i:Hz,∀ V:Pane n,wage_Q 2 (X i V)=X i V): numbD (warp_E F X) =0∧ Mono_W (ridge_Q Q L F X):=by
 refine ⟨funext (fun i=> funext (fun x=>?_)), Ione.aura_T _ _ _ _ _ (fun i _ V=>u i V.1)⟩; unfold numbD warp_E sunY; simp only [Function.comp_apply,Finset.sum_apply,Pi.zero_apply]; change deadP (∑ j∈ (univ.filter fun x:Hz=> F x=i),X j x)=0;
 rw [darn_K]; exact sum_eq_zero fun j _=> sub_eq_zero.mpr (u j x).symm
lemma warp_veil (t:GSingle X): veil_M (ridge_Q Q L F X)=0:=by
 apply keys.mpr; intro i D V; unfold ridge_Q soot_T; simp only [Finset.sum_apply,map_sum]; apply sum_eq_zero; intro j _; unfold stroke chasmR; simp only [Function.comp_apply]
 by_cases h:i=lagE (F j)
 · subst i; rw [Pi.single_eq_same]
   unfold Vow.flick; simp_rw [Pi.sub_apply,map_sub]; split<;>split<;> simp [oV, paid0.mp t]
 rw [Pi.single_eq_of_ne h]; exact map_zero _
include p
lemma enroll (hp:PackSale Q R b X Z w): PackSale Q R b (warp_E F X) (ridge_Q Q L F X+Z) w:=by
 intro t u; rw [Vow.toast t,←add_assoc,p.settle X t u]; exact hp t u
lemma brewNo (w:IncX Utrue X Q h a): ∀ x:Orbit n,Rue.FleetS Q.threshold x.1 → exponentL Q (writ_E (warp_E F X)) x.1 +fuelV Q (writ_K (ridge_Q Q L F X)) x= exponentL Q X x.1:= pusher Q (fun x=>exponentL Q X x.1) (fun s x=> (force_r Q s X x).symm.trans (congrArg (fun R=>suit_Y s (exponentL Q R x.1)) (mobility w s))) (p.settle X)
end Test
end YM.CF.Py.Rate
