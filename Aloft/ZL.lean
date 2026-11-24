import Ridgetop.Gw
import Preen.Gamma
import Preen.Buckle
import Preen.Fitted
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
namespace Aloft
open Py.Dyad Keeping Py.Rate.Pitching.Focus
open _root_.YM.Preen
local notation "j0"=> (3:Axis)
variable (M:Morn P.par.K)(α:ℝ)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(p:∀ s,F ≤ s→ Accordance P M F s (C s) (D s))(u:RobeRoad P F C D x)(t:Jones P M α F C D x)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "Ω"=>P.heaven 3 ξ
local notation "Ψ"=> P.seasons 3 ξ
local notation "H"=>P.ManyF 3 ξ
local notation "ζ"=>P.wealth 3 ξ
local notation "A₀"=>paster (Ω)
local notation "U"=>P.cartage 3 ξ
-- declare paid.W
abbrev PeriodS(j:ℕ)(y:H):Prop:= Tendsto (fun i=>ζ (recoup P F C D ξ i j)) atTop (𝓝 y)∧ ∀o:Vantage,tidal P F j < o 3→pointT P F C D ξ o= (U (o-crest P F)) ((Ψ).E ((o 3-tidal P F j).toNNReal) y)
abbrev asset (k:H):Submodule ℂ (H).space:= Submodule.span ℂ (Set.range (fun t:ℝ≥0=>(Ψ).E t k))
include p u
lemma coreH(j:ℕ)(e:F ≤ j):∃ v:H, PeriodS P F C D x j v:=core_c P F C D ξ M p (rankBridge P F C D x u) j e
omit p u
-- generic cells
section
variable {X:Hilbert}{i: Axis}(E:OS.Semigroup X i)(z:X)
include E
private lemma main_in {t:ℝ≥0}{y:X}(h:y∈ Submodule.span ℂ (Set.range (fun v:ℝ≥0=>E.E v z))): E.E t y∈ Submodule.span ℂ (Set.range (fun v:ℝ≥0=>E.E v z)):=by
 induction h using Submodule.span_induction with
 | mem y hp=> obtain ⟨r,rfl⟩:=hp; apply Submodule.subset_span; exact ⟨t+r,congrFun (congrArg DFunLike.coe (E.time t r)) z⟩
 | zero=> rw [map_zero]; exact Submodule.zero_mem _
 | add a b _ _ p q=> rw [map_add]; exact Submodule.add_mem _ p q
 | smul a b h p=>rw [map_smul]; exact Submodule.smul_mem _ a p
lemma back_in {t:ℝ≥0}(K:Submodule ℂ X.space)(f:FiniteDimensional ℂ K)(h:∀ y∈K,E.E t y∈K)(y:X)(p:E.E t y ∈ K): y∈K:=by
 let F:K→ₗ[ℂ] K:= ((E.E t).toLinearMap.comp K.subtype).codRestrict K (fun x:K=>h x.val x.property)
 have hf:Injective F:=fun x y e=> Subtype.ext (E.heat_alive t (congrArg Subtype.val e))
 obtain ⟨s,hs⟩:= LinearMap.surjective_of_injective hf ⟨E.E t y,p⟩
 rw [← E.heat_alive t (congrArg Subtype.val hs)]; exact s.property
end
-- relation manyheat
lemma twin(j k:ℕ)(y z:H)(hY:PeriodS P F C D x j y)(hZ:PeriodS P F C D x k z):∃ t v:ℝ≥0,(Ψ).E t (A₀ y)=(Ψ).E v (A₀ z):=by
 let τ:= max (tidal P F j) (tidal P F k)+1
 let a:Vantage:=fun _=>τ
 have H1:tidal P F j<a 3:=(le_max_left ..).trans_lt (lt_add_one _); have H2:tidal P F k<a 3:=(le_max_right ..).trans_lt (lt_add_one _)
 let b:= (a 3-tidal P F j).toNNReal; let c:= (a 3-tidal P F k).toNNReal
 refine ⟨b,c,?_⟩
 have he: U (a-crest P F) ((Ψ).E b y)= U (a-crest P F) ((Ψ).E c z):= (hY.2 a H1).symm.trans (hZ.2 a H2)
 have hu:(Ψ).E b y=(Ψ).E c z:= eq_aid (P.cart_norm 3 ξ (a-crest P F)) he -- binder p bug
 exact (keep_heat _ (P.stone_norm 3 ξ) (Ψ) (P.heaven_hot 3 ξ) b y).trans ((congrArg (A₀) hu).trans ((keep_heat _ (P.stone_norm 3 ξ) (Ψ) (P.heaven_hot 3 ξ) c z).symm))
where eq_aid {R:Hilbert}{f:R.Op}(h:∀x:R,‖f x‖=‖x‖){x y:R}(t:f x=f y):x=y:= by apply sub_eq_zero.mp; apply norm_eq_zero.mp; rw [← h,map_sub,t,sub_self,norm_zero]
lemma incoming(j k:ℕ)(y z:H)(hY:PeriodS P F C D x j y)(hZ:PeriodS P F C D x k z)(Q:FiniteDimensional ℂ (asset P x (A₀ y))): A₀ z∈ asset P x (A₀ y):=by
 exact clan (Ψ) (A₀ y) (A₀ z) (twin P F C D x j k y z hY hZ) Q
where clan {B:Hilbert}(S:OS.Semigroup B (3:Axis))(a b:B)(h:∃ t v:ℝ≥0,S.E t a=S.E v b)(V:FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun t:ℝ≥0=>S.E t a)))): b∈ Submodule.span ℂ (Set.range (fun t:ℝ≥0=>S.E t a)):=by obtain ⟨t,v,z⟩:=h; exact back_in S (t:=v) _ V (fun _ p=>main_in S a p) _ (z ▸ Submodule.subset_span ⟨t,rfl⟩)
-- fields from Ledger; analog vergeH
set_option synthInstance.maxHeartbeats 350000
abbrev crownL(j:ℕ)(y:H):(P.ColorHil 3 ξ).space→L[ℂ](H).space:= ((asset P x (A₀ y))ᗮ.starProjection).comp (brokerM P x)
private lemma pact{B B' C': Type}[NormedAddCommGroup B][NormedSpace ℂ B][NormedAddCommGroup B'][NormedSpace ℂ B'][NormedAddCommGroup C'][NormedSpace ℂ C']{g:B'→L[ℂ] C'}{f:B→L[ℂ] B'}(t:‖g‖≤1)(p:‖f‖≤1):‖g.comp f‖≤1:=(ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_one₀ t (norm_nonneg _) p)
private lemma hux{R:Hilbert}(K:Submodule ℂ R.space):‖(Submodule.orthogonal K).starProjection‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z=>by rw [one_mul]; exact Submodule.norm_starProjection_apply_le _ _)
lemma crown_charge(j:ℕ)(y:H): ‖crownL P x j y‖ ≤1:= pact (hux (R:=H) (asset P x (A₀ y))) (pact (pasted_cost (X:=(H)) Ω) (P.enter_wealth 3 ξ)) -- check binder
-- projection. use generic
private lemma lowest{R:Hilbert}(K:Submodule ℂ R.space){f:ℕ→R}{x:R}(u:x∈K)(h:Tendsto f atTop (𝓝 x)):Tendsto (fun i=>(Submodule.orthogonal K).starProjection (f i)) atTop (𝓝 0):=by
 have hx:= (Submodule.orthogonal K).starProjection.continuous.continuousAt (x:=x) |>.tendsto.comp h; rw [Submodule.starProjection_orthogonal_apply_eq_zero u] at hx; exact hx
lemma crown_zero(j k:ℕ)(y z:H)(hY:PeriodS P F C D x j y)(hZ:PeriodS P F C D x k z)(Q:FiniteDimensional ℂ (asset P x (A₀ y))):Tendsto (fun i:ℕ=> crownL P x j y (recoup P F C D ξ i k)) atTop (𝓝 0):= lowest (R:=H) (asset P x (A₀ y)) (incoming P F C D x j k y z hY hZ Q) (show Tendsto (fun i=>A₀ (ζ (recoup P F C D ξ i k))) atTop (𝓝 (A₀ z)) from (A₀).continuous.continuousAt.tendsto.comp hZ.1)
include p u t
set_option maxHeartbeats 450000 in
lemma post(j:ℕ)(y:H)(hY:PeriodS P F C D x j y)(Q:FiniteDimensional ℂ (asset P x (A₀ y))): ∀ᶠ d:ℕ in atTop,∀ k:ℕ, ‖crownL P x j y (sparrow P F ξ (hikeV d+k) (hikeV d))‖ ≤ thresholdU P M α d k:=by
 let A:=crownL P x j y
 filter_upwards [annihilates P M F C D ξ (jBridge P M α F C D x t) (V:=(H).space) (fun s h=> (p s h).1),_root_.YM.Preen.goes_town.eventually_ge_atTop F] with d he hd k
 apply he A (crown_charge P x j y) _ k
 exact (coreH P M F C D x p u (hikeV d) hd).elim fun z hz=> crown_zero P F C D x j _ y z hY hz Q
#print axioms post
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
