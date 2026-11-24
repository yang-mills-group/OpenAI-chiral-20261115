import YM.SU5.FiniteGaugeData.Jadot.Nigra
import YM.SU5.FiniteGaugeData.Jadot.Loyd
import YM.SU5.FiniteGaugeData.Jadot.Solan
/-! # Inside price on paid stamps. Halos and masks _actually lease the corrected L_ in BraWeight_. -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 550000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Cuprite.Spirit
open Function NormedSpace Filter Finset MeasureTheory Lattice RG Wilson AnalyticBridge Metric Pressure Galope CF CF.Pastry CF.Py CF.Py.Rate
open SU Fock Reduction Reduction.Jersey Reduction.Drama Reduction.Drama.Pack Reduction.Hutch Cube Lat Window Presidio Tenant Skye Scree Graph CF.Buffered Window.Brique Next.Rank Nacre -- amb.Supply
open Rush Scroll Peaks Tap Tulip Fir Cascade Dial Spire Paige Vault
open Avenue RouteM Spindle
open Rhythm Pilot PhaseM Steve VolumeRate
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Reduction.Dinar Reduction.Dijon Reduction.Rheims Fock.Brique Reduction.Dijon.Currency Reduction.Celeste Window.Presidio
open Reduction.Loyd Reduction.Loyd.Art Window.Presidio.Nigra Window.Presidio.Gato Fock.Relief Turnist
namespace Moorend
variable {N:Side}{P Q M D A X:Op (Single N)}{T S U:Support (More N)}{r v:ℕ} {μ a e s w w' k b σ ε t c:ℝ}{X':FC (Single N)}
local notation "uid"=> Single N
local notation "Θ"=> tickA N
local notation "ℓ"=> modesIn N
lemma Ram_visit (p:Lattice.halo r S ⊆ T)(x:Ket uid)(q:Neighbor r P)(v:Ram (ℓ S) x):Ram (ℓ T) (acts P x):=by
 let A:=cutM (ℓ T); let B:=cutM (ℓ S); have he:B*star P *A=B*star P:=Window.Brique.Neighbor.adj q _ _ p; have hx:=congrArg star he; have hp:A*(P*B)=P*B:=by rwa [star_mul,star_mul,star_star,(show star A=A from (cutM_idp _).2.star_eq),(show star B=B from (cutM_idp _).2.star_eq)] at hx
 change acts A _=_; nth_rw 1 2 [←v]; rw [←act_mul,←act_mul,←act_mul _ _ x,mul_assoc,hp] -- check
-- usage. norm bounds.
abbrev Muse(c s:ℝ):=(3*c+2)*s -- B0
abbrev Bar(c s:ℝ):=6*(1+Muse c s)
abbrev Shill(c s t p e:ℝ):ℝ:=2*(s*p)+ t*e*(1+Muse c s)
lemma barOne(h:0≤ c)(p:0≤ s):1≤ Bar c s :=by
 unfold Bar; have hp:0≤ Muse c s:=by unfold Muse; positivity
 linarith
lemma shillZero(p:0≤ c)(h:0≤ s)(t_:0≤t)(l:0≤a)(r:0≤e):0≤Shill c s t a e:=by unfold Shill Muse; positivity
-- Hail identity lower
private lemma lifeline(p0:IsStarProjection Q)(p:Spear Q D)(l:Milieu Q M)(x:Ket uid)(e:Upt (1-Q) x):acts (star (Hail M D)) x=x+acts D x:=by rw [Pall.hailV l p p0,act_add]; nth_rw 1 [←e]; rw [←act_mul,l.invM.lowerV,e]
private lemma Era(p:Spear Θ D)(l:Milieu Θ M)(h:(ℓ S).card≤ s)(he:0≤ c)(v:cellU univ M (3*c+2))(w:‖D‖≤5): Marge (Bar c s) (tickA N) M D (ℓ S):=by
 have hs:0≤ s:=(Nat.cast_nonneg _).trans h; have hm:0≤ Muse c s:=by unfold Muse; positivity
 constructor; exact l; exact p
 intro x ℓu v'; have hx: ‖acts M x‖≤ Muse c s *‖x‖:= Loyd.Ram.cost (cellU.trim v (subset_univ _)) (by positivity) h x v'
 unfold Pall; rw [act_mul]; refine (Flare.opy _ _).trans ?_; apply le_trans (b:=6*(Muse c s*‖x‖)); · exact mul_le_mul ((norm_sub_le ..).trans (by rw [norm_star,norm_one]; linarith)) hx (norm_nonneg _) (by norm_num)
 unfold Bar; nlinarith only [norm_nonneg x]
 intro x ℓu l'; rw [lifeline (plus_P _) p l x ℓu]; refine (norm_add_le ..).trans ?_; have he : ‖acts D x‖ ≤ 5*‖x‖ := (Flare.opy _ _).trans (mul_le_mul_of_nonneg_right w (norm_nonneg _)); unfold Bar; nlinarith only [he,hm,mul_nonneg hm (norm_nonneg x)]
variable (B:Currency (tickA N) P μ a e w c M D)(p:Standing (tickA N) P)
variable {r' v':Finset (Single N)}
local notation "σL"=> stageL r' (tickA N) P μ M
local notation "σZ"=> stageZ v' (tickA N) P μ D
local notation "χ"=> Lemp (tickA N) P
local notation "Υ"=> Zemp (tickA N) P
local notation "ϕ"=> Fock.Reduction.Loyd.Art (Bar c s) -- argument take.t
include B
lemma invoice (t:(ℓ S).card≤ s)(he:0≤ c): Marge (Bar c s) (tickA N) (stageL r' (tickA N) P μ M) (stageZ v' (tickA N) P μ D) (ℓ S):=by refine Era (B.buildZ (T:=v') (monograph v'|>.symm)) (B.buildL (S:=r') (monograph r'|>.symm)) t he ?_ (B.zNormL (T:=v')); intro i _; exact B.cellC (S:=r') i
omit B
include p
lemma cost_zero (B:Currency Θ P 0 a e w c M D)(t:(ℓ S).card≤ s)(he:0≤ c): Marge (Bar c s) (tickA N) (Lemp Θ P) (Zemp Θ P) (ℓ S):= Era (Cardio.heart p) (Cardio.warm p) t he (cellU.mono B.trueC (by linarith)) ((revenueZZ B.topE B.tLive le_rfl).trans (by norm_num))
include B
lemma cutDoctor (G:Currency Θ P 0 a e w' c M D)(H:Lattice.halo r S⊆T) (g:(ℓ S) ⊆ r')(F:(ℓ T) ⊆ v')(A:Neighbor r M)(h:(ℓ S).card≤ s)(k0:(ℓ T).card ≤ t)(hC:0≤ c)(V:Art (Bar c s) Θ (ℓ S) false X' k): ‖Celeste.cost (stageL r' (tickA N) P μ M) (stageZ v' (tickA N) P μ D) X'-smut (tickA N) P X'‖ ≤ Shill c s t a e * k:=by
 let L:= σL; let D':=σZ; let Y:=Shill c s t a e; have hs:0≤ s:= (Nat.cast_nonneg _).trans h; have hj:0≤t:=(Nat.cast_nonneg _).trans k0; have hp:0≤Y:=shillZero hC hs hj B.tinyA B.tinyB
 let lT:=(invoice (r':=r') (v':=v') B h hC); let lB:=cost_zero p G h hC; have h0:=barOne hC hs; let W:=Muse c s; have hw:0≤W:=by unfold W Muse; positivity
 have hz: (ℓ S) ⊆ ℓ T:=modes_monotone (Subset.trans (halo_subset ..) H)
 have hr(x:Ket uid): Y*‖x‖ ≤ Y*Bar c s*‖x‖:= mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hp h0) (norm_nonneg _)
 apply Art.humane (M:=L) (Z:=D') V hp lT lB
 · intro x u v; let y:=acts L x; have ht:y=acts M x:=reforge.forA (Ram.incl v g) _ _; have hy:Ram (ℓ T) y:= ht ▸ Ram_visit H x A v -- eq direction?
   have hx:‖y‖ ≤ W*‖x‖:= Ram.cost (A:=L) (c:=3*c+2) (fun i _=>B.cellC i) (by positivity) h x v
   have he:‖acts (star D'-star Υ) y‖ ≤e*t*‖y‖:=by
      have he:acts (star D') y=acts (star D) y:=by unfold D' Currency.stageZ; rw [reforge.ocean]; exact reforge.forA (Ram.incl hy F) _ _
      rw [act_sub,he,←act_sub,←star_sub]; exact Ram.cost (cellU.trim G.zRow (subset_univ _)) G.tinyB k0 y hy -- order notation
   have hv:‖acts (L-χ) x‖≤ a*s*‖x‖:=by rw [act_sub,show acts L x= acts M x from ht,←act_sub]; exact Ram.cost (cellU.trim G.mQ (subset_univ _)) G.tinyA h x v
   have hh:‖1-star Υ‖≤2:= (norm_sub_le ..).trans (by rw [norm_one,norm_star]; have he:‖Υ‖ ≤1:= revenueZZ G.topE G.tLive le_rfl; linarith only [he])
   apply (hr x).trans'; rw [show Pall L D'-Pall χ Υ=(1-star Υ)*(L-χ)-(star D'-star Υ)*L from by unfold Pall; noncomm_ring,act_sub,act_mul,act_mul]; change ‖acts (1-star Υ) _ - acts (star D'-star Υ) y‖ ≤_
   apply (norm_sub_le ..).trans; refine (add_le_add ((Flare.opy _ _).trans (mul_le_mul hh hv (norm_nonneg _) zero_le_two)) he).trans ?_; unfold Y Shill; nlinarith only [mul_le_mul_of_nonneg_left hx (mul_nonneg (B.tinyB) hj),mul_nonneg (mul_nonneg (B.tinyB) hj) (norm_nonneg x)] -- hz W syntax
 intro x p v; let x':= Ram.incl v hz; have he:‖acts (D'-Υ) x‖ ≤ e*t*‖x‖:=by
    rw [act_sub,show acts D' x=acts D x from reforge.forA (Ram.incl x' F) _ _,←act_sub]; exact Ram.cost (cellU.trim G.zCol (subset_univ _)) G.tinyB k0 x x'
 rw [act_sub, lifeline B.topE lT.root lT.live x p, lifeline G.topE lB.root lB.live x p, add_sub_add_left_eq_sub, ←act_sub]; refine he.trans (le_trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) (hr x)); unfold Y Shill; nlinarith only [mul_nonneg B.tinyA hs,mul_nonneg (mul_nonneg hj B.tinyB) hw]
omit p
-- inside post. unreg state remains Used.C.
lemma art_sector_build {b':Bool}(H:Lattice.halo r S⊆T)(J:Lattice.halo v T⊆U) (g:(ℓ S) ⊆ r')(F:(ℓ T) ⊆ v')(A:Neighbor r M)(Q0:Neighbor v D)(h:(ℓ S).card≤ s)(hC:0≤ c)(V:Art (Bar c s) (tickA N) (ℓ S) b' X' k): Fock.Sector (ℓ U) b' (Celeste.cost (stageL r' (tickA N) P μ M) (stageZ v' (tickA N) P μ D) X'):=by
 let E:= ℓ U; let K:= ℓ T; let W:= ℓ S; have hp:K⊆E:=modes_monotone (Subset.trans (halo_subset ..) J); have he:W⊆K:=modes_monotone (Subset.trans (halo_subset ..) H)
 let D':=σZ; let P':=σL; let T':=invoice (r':=r') (v':=v') B h hC; apply Art.crux_turn V T'
 · intro i x c; let y:= acts P' i; have hy:Ram K y:=by rw [show y=acts M i from reforge.forA (Ram.incl c g) _ _]; exact Ram_visit H i A c -- let rewrite tune
   have hx:Ram E (acts (star D') y):=by rw [show star D'=reforge v' (star (Zami Θ P μ)) (star D) from reforge.ocean ..,reforge.forA (p:=Ram.incl hy F)]; exact Ram_visit J y (Window.Brique.Neighbor.adj Q0) hy
   unfold Pall; rw [act_mul,act_sub, act_one]; let t:= Ram.incl hy hp; unfold Ram Upt; rw [map_sub]; change acts (cutM E) y- _ = _; rw [t,hx] -- tune
 intro i x c; let t:= Ram.incl c he; have hx:acts D' i=acts D i:=reforge.forA (Ram.incl t F) _ _; rw [lifeline B.topE T'.root T'.live i x, hx]; have hp:= Ram.incl t hp; have ht:=Ram_visit J i Q0 t; unfold Ram Upt; rw [map_add,hp,ht]
-- use. S and halo.
include p
lemma venture (G:Currency Θ P 0 a e w' c M D)(H:Lattice.halo r S⊆T)(J:Lattice.halo v T⊆U) (g:(ℓ S) ⊆ r')(F:(ℓ T) ⊆ v')(A:Neighbor r M)(Q0:Neighbor v D)(h:(ℓ S).card≤ s)(k0:(ℓ T).card ≤ t)(hC:0≤ c)(V:Art (Bar c s) (tickA N) (ℓ S) false X' k):
  BraWeight (stageL r' (tickA N) P μ M) (stageZ v' (tickA N) P μ D) (1+X') ≤ Real.exp ((Volt Θ P X').re + Shill c s t a e * k +k^2/2):=
 harvestX p (invoice (r':=r') (v':=v') B h hC).live (invoice (r':=r') (v':=v') B h hC).root (mateK _) (tickB _) (V.leanP (invoice B h hC)) (cutDoctor B p G H g F A h k0 hC V)
end Moorend
end YM.SU5.FiniteGaugeData.Cuprite.Spirit
