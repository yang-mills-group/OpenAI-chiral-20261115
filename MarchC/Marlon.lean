import MarchC.Veneer
import MarchC.Item
import Crape.Creature
import Preen.Fitted
import SatinLocalChron
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
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
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
namespace Mido
open _root_.YM.Preen Cheer
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(F:ℕ)(C D:ℕ→ℕ→ℝ)(f:P.Fever F C D x)(H:Rovers P F C D x)
local notation "θ"=>crownM P x F C D
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "W"=>P.ManyF 3 (ξ)
local notation "Ω"=>P.heaven 3 (ξ)
local notation "A"=>paster (Ω)
local notation "d" j:max=>tidal P F j
local notation "K"=>dot3 P x F C D
local notation "S"=>(P.seasons 3 (ξ))
local notation "E"=> (P.seasons 3 (ξ)).E
local notation "U"=>P.cartage 3 ξ
local notation "m"=> poseMirror 3
local notation "CV"=>pointT P F C D ξ
include f H J
lemma marlon(v:W)(e:Aloft.PeriodS P F C D x F v)(a b:Vantage)(h:b-a∈mzone)(u:0 < -a 3)(r:0 < b 3): K a b=θ (b-a)-oneM P x v:=by
 let y:=b-a; obtain ⟨j,p,q,t⟩:= (((eventually_ge_atTop F).and (((recessVanish P F).eventually (gt_mem_nhds u)).and ((recessVanish P F).eventually (gt_mem_nhds r))))).exists
 obtain ⟨k,hv,_hV⟩:=f j p
 have hz:= ratioB P x F C D j k hv a b q t
 have hw:= thanks P x J F C D H j p k hv (b-a) h (show 2*d j < _ from (by change 2*(tidal P F j) < b 3-a 3; linarith only [q,t]))
 exact hz.trans (congrArg₂ (·-·) hw.symm (veneers P x F C D j k hv F v e))
omit J f H in
lemma dot3_sur (j:ℕ)(v:W)(e:Aloft.PeriodS P F C D x j v): ∃ g:Vantage→(W).space, Continuous g ∧
 (∀a,d j<a 3→CV a=g a) :=by
 exact ⟨_,P.caravan 3 ξ (fun a:Vantage=>a-crest P F) (fun a:Vantage=> E ((a 3-tidal P F j).toNNReal) v) (continuous_id.sub continuous_const) (((S).continuousE _).comp (continuous_real_toNNReal.comp ((continuous_apply 3).sub continuous_const))),e.2⟩
omit J f H in
private lemma roof_s (j:ℕ)(v:W)(e:Aloft.PeriodS P F C D x j v)(u w:Vantage)(fu:d j < -u 3)(fw:d j < w 3): ContinuousAt (fun z:Vantage×Vantage=>K z.1 z.2) (u,w):=by
 obtain ⟨g,h,v⟩:=dot3_sur P x F C D j v e; let F'(z:Vantage×Vantage):=inner ℂ (A (g (m z.1))) (A (g z.2))
 have hp:Continuous F':= ((A).continuous.comp (h.comp ((m).continuous.comp continuous_fst))).inner ((A).continuous.comp (h.comp continuous_snd))
 apply hp.continuousAt.congr -- eventuallyEq orientation? 
 let M(z:Vantage):=m z 3
 have ht:Continuous M:= (continuous_apply 3).comp (m).continuous; have hw:Continuous (fun z:Vantage×Vantage=>z.2 3):= (continuous_apply 3).comp continuous_snd
 filter_upwards [(ht.comp continuous_fst).continuousAt.tendsto.eventually (lt_mem_nhds (show d j < M u from by unfold M; rw [clock_neg]; exact fu)), hw.continuousAt.tendsto.eventually (lt_mem_nhds fw)] with z f gq
 exact congrArg₂ (fun (w v:W)=>inner ℂ (A w) (A v)) (v _ f).symm (v _ gq).symm

-- initialize point margin, from heat.
omit f J H in
lemma early (j:ℕ)(v:W)(e:Aloft.PeriodS P F C D x j v)(r:¬FiniteDimensional ℂ (Aloft.asset P x (A v)))(t:ℝ)(h:d j<t): K ((m).symm (forest t)) (forest t) ≠0:=by
 let z:=forest t
 let V:=CV z
 let q':=(t-d j).toNNReal; have h₀:z 3=t:=by unfold z forest; rw [if_pos rfl]
 let k:=U (z-crest P F)
 have hV:V=k (E q' v):= (e.2 z (h₀.symm ▸ h)).trans (congrArg (fun a:ℝ=>k (E a.toNNReal v)) (congrArg (·- d j) h₀))
 have he:A v≠0:= fun p=> r (smallW (Z:=W) (S) _ p)
 have ht':A (E q' v)≠0:=fun z=>he ((S).heat_alive q' ((keep_heat (Ω) (P.stone_norm ..) (S) (P.heaven_hot 3 ξ) _ _).trans z |>.trans (map_zero _).symm))
 have hx:A V ≠0:=by
    intro p
    have hf:k (A (E q' v))=0:= (Aloft.cartPaste P x (E q' v) (z-crest P F)).trans ((congrArg (A) hV.symm).trans p)
    exact ht' (norm_eq_zero.mp ((P.cart_norm 3 ξ (z-crest P F) _).symm.trans ((congrArg norm hf).trans norm_zero)))
 -- no rw simplification.Cost.
 exact fun p=> hx (inner_self_eq_zero.mp ((congrArg (fun y:Vantage=> inner ℂ (A (CV y)) (A (CV z))) ((m).apply_symm_apply z)).symm.trans p))
where
 smallW {Z:Hilbert}(E':OS.Semigroup Z (3:Axis))(a:Z)(h:a=0) :FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun j:ℝ≥0=>E'.E j a))):=by subst a; have he:(fun j:ℝ≥0=>E'.E j (0:Z))=Function.const ℝ≥0 (0:Z):=funext fun j=>map_zero _; rw [he]; unfold Function.const; change FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun _:ℝ≥0=>(0:Z.space)))); rw [Set.range_const]; infer_instance

-- marlon alive via continuity small region with temporal sign & spatial y'>0. u=-t, w=t.Others w displaced adding +epsilon
private abbrev mse(t c:ℝ):Vantage:=fun i=>if i=(3:Axis) then t else c
lemma wood (v:W)(e:Aloft.PeriodS P F C D x F v)(r:¬FiniteDimensional ℂ (Aloft.asset P x (A v))) :∃ p∈ mzone,(θ p -oneM P x v)≠0 :=by
 let t:= d F+1
 have ht:0<d F:=tide_price ..
 have he:d F<t:=lt_add_one _; have hp:0<t:=ht.trans he
 let u:=(m).symm (forest t); let w:=forest t; have hw:w 3=t:=by simp [w,forest] -- True issue
 have hu:u 3= -t:=by change opposeR 3 (forest t) 3=_; unfold opposeR mirrorΩ; simp [forest] -- check
 let z(c:ℝ):=mse t c
 have hk: Continuous z:=continuous_pi (fun i=>by
    by_cases h:i=(3:Axis)
    · simpa [z,mse,h] using (continuous_const : Continuous (fun _ : ℝ=> t))
    simp [z,mse,h]; exact continuous_id)
 let Pz(c:ℝ):Vantage×Vantage:=(u,z c)
 have hu': Continuous Pz:= continuous_const.prodMk hk
 have hId:Pz 0=(u,w):=rfl
 have hv:=roof_s P x F C D F v e u w (by rw [hu, neg_neg]; exact he) (by rw [hw]; exact he)
 have hy:ContinuousAt (fun c:ℝ=>K u (z c)) 0:=show ContinuousAt ((fun p:Vantage×Vantage=>K p.1 p.2) ∘ Pz) 0 from ContinuousAt.comp (g:=fun p:Vantage×Vantage=>K p.1 p.2) (f:=Pz) hv hu'.continuousAt
 obtain ⟨c,l,m₁⟩:= Filter.Eventually.exists ((show ∀ᶠ c:ℝ in 𝓝[>] (0:ℝ),0<c from self_mem_nhdsWithin).and ((hy.tendsto.eventually (isOpen_ne.mem_nhds (early P x F C D F v e r t he))).filter_mono -- precedence? nhdsWithin
    nhdsWithin_le_nhds))
 let Wc:= z c
 have hq:Wc 3=t:=by simp [Wc,z,mse]
 have hx: Wc-u∈mzone:=by
    intro i; rw [Pi.sub_apply]; by_cases g:i=(3:Axis)
    · subst i; rw [hq,hu]; linarith only [hp]
    change 0 < _-opposeR 3 (forest t) i
    simp [Wc,z,mse,g,forest,opposeR,mirrorΩ,l] -- simp maybe closes
 refine ⟨Wc-u,hx,fun p'=>m₁ ((marlon P x J F C D f H v e u Wc hx (by rw [hu, neg_neg]; exact hp) (by rw [hq]; exact hp)).trans p')⟩
#print axioms wood
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
