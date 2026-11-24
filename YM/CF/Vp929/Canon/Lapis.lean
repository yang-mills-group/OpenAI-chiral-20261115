import YM.CF.Vp929.Canon.Pani
import YM.CF.Vp929.Canon.Squires
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
set_option quotPrecheck false
open Cycle929 Larch Bake Salt Trees Push.BetaTransport
open AnalyticBridge.VerifiedReset.Collection
variable {n:Side}{L:ℕ}{Q:BudgetPoint}{A h a c d v α σ C Λ β j w:ℝ}
local notation "D'"=> RegBudget n
local notation "V'"=> Skye.Seat n
local notation "Gξ"=> SU.group
local notation "Px"=> Lattice.PlaqAxes
local notation "φ"=> AnalyticBridge.VerifiedReset.petals
local notation "H_"=> AnalyticBridge.VerifiedReset.heads
local notation "Z_"=> AnalyticBridge.VerifiedReset.counter
local notation "Lρ"=> Cash.prominence Q
variable {R:PathData SU.group}{b:Clip}(u:Cease Q R b α v σ C Λ n) (T:Ids n) (g:1 ≤ h)
local notation "Fr"=> c
local notation "Θ_"=> ΘK T Q R b (-1)
local notation "ℓ1"=> (lite_b n Q R b (-1))
local notation "ℓ2"=> (lit_P n Q R b (-1))
local notation "μr"=> (rate_b Q b σ C α (-1))
local notation "μp"=> (rate_h Q b σ C α (-1))
local notation "Λr"=> (rate_μ Q b σ C v (-1))
local notation "Kp"=> Push.BetaTransport.kinetic
-- scalar heads identity at threshold using true masks.
private lemma headWork (o:V')(V:Orbit n)(h:FleetS Q.threshold V.1): Vow.march Q (lagE (spotp o)) (oV (slotH o)) V +fuelV Q (chasmR (lagE (spotp o)) (copperH o)) V = moldV n (H_ Q o V.1):=by
 let S:= (spotp o).val.2; let A:= lagE (spotp o); let y:= flags Q.threshold V.1; have hp:penny o V.1= (∑ i:Px, ‖φ V.1 o i‖^2)/2:=by unfold penny AnalyticBridge.VerifiedReset.counter AnalyticBridge.VerifiedReset.quad; simp [Matrix.one_apply, ite_mul, Finset.sum_ite,real_inner_self_eq_norm_sq]
 let Z:=copperH o; unfold AnalyticBridge.VerifiedReset.heads; rw [Vow.shade_t]; have he:o∈ y↔o∈ y ∩ A.val:=(by simp [(show o∈A.val from (spotp o).property)]); have Hz: o∉ y ↔ Healthy Q.threshold {o} V.1:=(by unfold Healthy; simp [y]); have hx:o∈A.val:=(spotp o).property; rw [Vow.march_f V h]
 by_cases t:o∈ y
 · have hi:¬Healthy Q.threshold {o} V.1:= fun v'=>(Hz.mpr v') t; have hz:¬Disjoint y A.val:= Finset.not_disjoint_iff.mpr ⟨o,t,hx⟩; have hv:fuelH y A:= fun p=>hz p.symm
   rw [if_neg hz,if_pos hv,masked_ne _ _ _ _ hi,map_zero]; unfold copperH; rw [if_neg (not_not_intro (he.mp t))]; exact add_zero _
 rw [masked_eq _ _ _ _ (Hz.mp t)]; dsimp only; rw [←hp]; by_cases hx:Disjoint y A.val
 · rw [if_neg (show ¬fuelH y A from fun p=>p hx.symm),if_pos hx, add_zero]; rfl
 rw [if_neg hx,if_pos (show fuelH y A from fun p=>hx p.symm), zero_add]; unfold copperH; rw [if_pos (mt he.mpr t)]; rfl
lemma heads_H (V:Orbit n)(h:FleetS Q.threshold V.1): exponentL Q (wholeH n) V.1 + fuelV Q (mateH n) V=moldV n (∑ i:V',H_ Q i V.1):=by
 unfold wholeH mateH; rw [release_v, tunes,map_sum,←sum_add_distrib]; exact sum_congr rfl fun i _=> headWork i V h
lemma fuel_η {Q:BudgetPoint}(V:Orbit n)(x y:Cusp n):fuelV Q (x-y) V = fuelV Q x V-fuelV Q y V:=by unfold fuelV; simp only [Pi.sub_apply,sum_sub_distrib]
abbrev creditR (Q:BudgetPoint)(R:PathData SU.group)(b:Clip)(n:Side):RegBudget n:= (wholeH n+lite_b n Q R b (-1))+lit_P n Q R b (-1)
abbrev creditT (Q:BudgetPoint)(R:PathData SU.group)(b:Clip)(T:Ids n):Cusp n:=mateH n-ΘK T Q R b (-1)
local notation "CR"=> creditR Q R b n
local notation "CT"=> creditT Q R b T
abbrev accountR (Q:BudgetPoint)(b:Clip)(α σ C:ℝ):=scoreH Q α+rate_b Q b σ C α (-1)+rate_h Q b σ C α (-1)
abbrev accountT (Q:BudgetPoint)(b:Clip)(v σ C:ℝ):=trimH Q v+rate_μ Q b σ C v (-1)
private lemma grant_single_H:GSingle (wholeH n):= by apply paid0.mpr; intro i x; unfold wholeH sunY; simp only [Finset.sum_apply,map_sum]; exact sum_eq_zero fun j _=> show blind_E (slotH j x)=0 from by unfold slotH; rw [Function.comp_apply,Taxi.mon_v,oqua]
private lemma grant_veil_H : veil_M (mateH n)=0:=by
 apply keys.mpr; intro i D V; unfold mateH; simp only [Finset.sum_apply,map_sum]; apply sum_eq_zero; intro j _; unfold chasmR; by_cases h:i=lagE (spotp j)
 · subst i; rw [Pi.single_eq_same]; unfold copperH; split; next t=> change blind_E (moldV n _) = 0; rw [Taxi.mon_v,oqua]
   next t=> exact map_zero _
 rw [Pi.single_eq_of_ne h]; exact map_zero _
include u T g
/- On real data. one Unit. -/
lemma creditTune : IncX primeU CR Q h (accountR Q b α σ C)∧Packed Q h Lρ CT (accountT Q b v σ C)∧ GSingle CR∧veil_M CT=0∧PackSale Q R b CR CT 1:=by
 obtain ⟨h1,h11,h12,y1⟩:= thirst Q R u.mass α (-1) u.day u.ha u.decent u.span u.n0 g 0; obtain ⟨h2,h21,h22,y2⟩:= crown_V Q R u.mass α (-1) u.day u.ha u.decent u.span u.n0 g 0; obtain ⟨Z,i0,i1,k1,o1⟩:=Λro Q R u.mass v (-1) u.tide u.hc u.decent u.span T g u.ar
 have t:=zero_le_one.trans g; have hc:Packed Q h Lρ (Θ_) Λr:=⟨Z,⟨fun i=>(i0 i ∅).wage t,fun i D _ _=>i0 i D⟩,i1⟩
 have he:veil_M CT=0:=by apply keys.mpr; intro i D V; unfold creditT; simp only [Pi.sub_apply,map_sub,keys.mp grant_veil_H,keys.mp k1,sub_zero]
 refine ⟨ Larch.add_v Q _ _ (Larch.add_v Q _ _ (incH u) h1) h2,(priest u t).sub hc,plus_single (plus_single grant_single_H h12) h22,he,?_⟩
 intro i hU; let U:=i.1; have H₁ : HasSum (fun x:Lane n=> Vow.march Q (χx Q R x) (oV (ham x Q b R (-1))) i) (moldV n (layer (fade R b Q (-1)) U)):=by
        simp_rw [psips Q R i u.decent _ (-1) hU]; apply (moldV n).hasSum; have he:= fade_sum (n:=More n) u.mass Q (-1); rw [layer_total _ U he]; exact (stack_series _ _ he).hasSum
 have H₂: HasSum (fun x:Reign n=> Vow.march Q (ωx Q R x) (oV (gustH x Q b R (-1))) i) (moldV n (layer (upperFade R Q 0 (-1)) U)):=by
        simp_rw [pTime Q R u.mass i u.decent _ (-1) hU]; apply (moldV n).hasSum; let he:= high_fade_sum (n:=More n) u.mass Q 0 (-1); rw [layer_total _ U he]; exact (stack_series _ _ he).hasSum
 let W0:= fuelV Q (mateH n) i; let e0:=exponentL Q (wholeH n) U; let l:= layer (fun d:Low=> d.loan R b (0:Site (More n)) Q 0 (-1)) U; have hp:e0= moldV n (∑ j:V', H_ Q j U)-W0:=eq_sub_of_add_eq (heads_H i hU)
 unfold creditR creditT; rw [ripe_H Q i,ripe_H Q i,fuel_η,(y1 i).unique H₁,(y2 i).unique H₂, show fuelV Q (Θ_) i=moldV n l from (o1 i hU).unique (Taxi.toast Q R u.mass i T u.hc u.tide u.decent u.span (-1))];
 let a:= layer (fade R b Q (-1)) U; let c:= layer (upperFade R Q 0 (-1)) U; let x:= ∑ j:V', H_ Q j U
 rw [show (1:ℝ)*Kp R b Q U=x+a+c-l by have q:= path_split u.mass u.span u.decent 0 (-1) U; simp only [zero_add,zero_mul,neg_one_mul,one_mul] at q ⊢; change - _+(a+c)=-x+l at q; linarith only [q],map_sub, map_add,map_add];
 change (e0+_)+_+ (W0-_)=_; rw [hp]; unfold x; abel
end Test
end YM.CF.Py.Rate
