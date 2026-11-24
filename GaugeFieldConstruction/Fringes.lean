import GaugeFieldConstruction.Fruit
set_option autoImplicit false
set_option maxHeartbeats 48000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
namespace BluffV
open Cauchy
-- images
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
open Phys Row
local notation "Fidx" => Matter.FlavorIndex
local notation "VFile"=> Fidx → J Row.f
abbrev figV(i:FactIx):Module.End ℂ (J Row.f):= if i.1 then onSecond (Cder true i.2) else onFirst (Cder false i.2)
lemma sideL (p:Axis)(i j: FIndex)(a b:SU.Slot): sD a b (figV (false,p) (ket (i,j)))=sunX (false,p) (sD a b (ket (i,j))):= by
 let y:=Cder false p; let Z:= Cder false p (ket i); rw [← Cauchy.takes]; change sD a b (onFirst y _)= onFirst (onFirst y) (sD a b _); rw [Cauchy.first,sD,straps,straps,Cauchy.first,Phys.here]
lemma sideR(p:Axis)(i j: FIndex)(a b:SU.Slot): sD a b (figV (true,p) (ket (i,j)))=sunX (true,p) (sD a b (ket (i,j))):=by
 let y:=Cder true p; rw [← Cauchy.takes]; change sD a b (onSecond y _)=onSecond (onFirst y) (sD a b _); rw [Cauchy.second,sD,straps,straps,Cauchy.second, Phys.here]
lemma mirth(i:FactIx)(p:J Row.f)(a:Fidx): tiap a (figV i p)=sunX i (tiap a p):=by
 unfold tiap; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]; apply sum_congr rfl; intro u _; apply sum_congr rfl; intro v _; apply congrArg; have he:(sD u v).comp (figV i)= (sunX i).comp (sD u v):=by
    apply ket_ext; rintro ⟨z,v'⟩; simp only [LinearMap.comp_apply]; rcases i with ⟨i,t⟩; cases i
    · exact sideL t z v' u v
    exact sideR t z v' u v
 exact LinearMap.congr_fun he p
abbrev single_S(i:Fidx):J Row.f→ₗ[ℂ] VFile:= LinearMap.single ℂ (fun _=> J Row.f) i -- tune
lemma scroll_S (p:Fidx)(q:J Row.f): graph_f (single_S p q)= tiap p q:=by
 rw [graph_f,LinearMap.sum_apply,sum_eq_single p]; · simp only [single_S, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply, Pi.single_eq_same]
 · intro i _ e; simp only [single_S, LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.single_apply, Pi.single_eq_of_ne e,map_zero]
 simp
lemma fig_s (p:Axis): figV (false,p)+figV (true,p)=P_f p:=rfl
lemma fig_r(p:Axis): -figV (false,p)+figV (true,p)= L p:=by unfold L splitD; change -onFirst (_)+_=onFirst (-_)+_; congr 1; apply crossing; intro a b; rw [LinearMap.neg_apply,first (Cder false p),first (-(Cder false p))]; simp
open Record
variable {α:Type}[Fintype α]
lemma memo_U {q: α→J Row.f}(i:α): q i∈ Record.space q:=by unfold Record.space; rw [Fintype.range_linearCombination]; exact Submodule.subset_span ⟨_,rfl⟩
abbrev rollF (p:Raw.F4): J Row.f:=evalTf p
lemma earn4 (i:Axis)(p:FactIx):figV p (Row.B i)∈ Record.space evalTf:=by
 rcases p with ⟨b,p⟩; let A:= Row.B i; let S:=Record.space evalTf; let F:=P_f p A; let D:=L p A; have he:F∈S:=memo_U (q:=evalTf) (i,Sum.inr p); have hp:D∈S:=memo_U (q:=evalTf) (i,Sum.inl p); let T:=figV (true,p) A; let X:=figV (false,p) A; have hv:X+T=F:= LinearMap.congr_fun (fig_s _) _; have ht:-X+T=D:=LinearMap.congr_fun (fig_r _) _
 cases b
 · have hw:F-D=(2:ℂ) • X:=by rw [← hv,←ht,two_smul]; abel
   rw [show figV (false,p) A= (2:ℂ)⁻¹ • (F-D) from (by rw [hw,inv_smul_smul₀ (by norm_num : (2:ℂ)≠0)])]; exact S.smul_mem _ (S.sub_mem he hp)
 have hx:F+D=(2:ℂ) • T:=by rw [←hv,← ht,two_smul]; abel
 rw [show figV (true,p) A= (2:ℂ)⁻¹ • (F+D) from (by rw [hx,inv_smul_smul₀ (by norm_num:(2:ℂ)≠0)])]; exact S.smul_mem _ (S.add_mem he hp)
lemma alter_f (p t: Axis) (x : J Row.f) : L p (P_f t x)=P_f t (L p x):=by
 apply Row.commuting chart_f (fun z=> z.2.val.mom p - z.1.val.mom p) (fun z=>z.1.val.mom t+z.2.val.mom t)
 · exact fun ⟨j,k⟩=> Row.l_charge _ (j.val.fermi false) (k.val.fermi true)
 exact fun ⟨j,k⟩=> Row.ph_charge _ (j.val.fermi false) (k.val.fermi true)
lemma pods_5 (p: Axis)(i:Raw.F4):P_f p (evalTf i)∈ Record.space evalF∧ L p (evalTf i)∈ Record.space evalF:=by
 obtain ⟨a,k|k⟩:=i
 · rw [← Row.eval_SL, ← Row.eval_LL]; exact ⟨memo_U _,memo_U _⟩
 change P_f p (evalTf (a,Sum.inr k)) ∈ Record.space evalF ∧ L p (P_f k _)∈ Record.space evalF; rw [← Row.eval_SS, alter_f]; exact ⟨memo_U _,memo_U (q:=evalF) (a, Sum.inr (Sum.inr (k,p)))⟩ -- tune
lemma spend5 (u:J Row.f)(h:u∈ Record.space evalTf)(p:FactIx): figV p u∈Record.space evalF:=by
 unfold Record.space at h; rw [Fintype.range_linearCombination] at h; let S:= Record.space evalF
 apply Submodule.span_induction (p:=fun i _ => figV p i∈ S) ?_ ?_ ?_ ?_ h
 · rintro i ⟨t,rfl⟩; rcases p with ⟨b,p⟩; obtain ⟨he,hp⟩:=pods_5 p t; let u:=evalTf t; let F:=P_f p u; let D:=L p u; let T:=figV (true,p) u; let X:=figV (false,p) u; have hv:X+T=F:=LinearMap.congr_fun (fig_s _) _; have ht:-X+T=D:=LinearMap.congr_fun (fig_r _) _; cases b
   · change X∈S; have hw:F-D=(2:ℂ) • X:=by rw [←hv, ←ht,two_smul]; abel
     rw [show X=(2:ℂ)⁻¹ • (F-D) from (by rw [hw,inv_smul_smul₀ (by norm_num:(2:ℂ)≠0)])]; exact S.smul_mem _ (S.sub_mem he hp)
   change T∈S; have hx:F+D=(2:ℂ) • T:=by rw [← hv,←ht,two_smul]; abel
   rw [show T=(2:ℂ)⁻¹ • (F+D) from (by rw [hx,inv_smul_smul₀ (by norm_num:(2:ℂ)≠0)])]; exact S.smul_mem _ (S.add_mem he hp)
 · rw [map_zero]; exact S.zero_mem
 · intro x y q s p1 p2; rw [map_add]; exact S.add_mem p1 p2
 intro a x v p1; rw [map_smul]; exact S.smul_mem _ p1
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
