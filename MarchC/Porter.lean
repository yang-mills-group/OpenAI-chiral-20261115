import MarchC.Conga
import MarchC.Shader
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
variable (P:Spine)(x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=>P.otherSpectrum 3 a x
local notation "W"=>P.ManyF a ξ
local notation "U"=>P.cartage a ξ
local notation "S"=>P.seasons a ξ
local notation "E"=> (S).E
noncomputable def valley (P:Spine)(x:P.Spectrum0 3)(a:Axis)(t:ℝ)(k:Vantage)(p w:P.ManyF a (P.otherSpectrum 3 a x)):ℂ:= inner ℂ p (P.cartage a (P.otherSpectrum 3 a x) k ((P.seasons a (P.otherSpectrum 3 a x)).E t.toNNReal w))
lemma heat_lim {d:ℕ→ℝ≥0}{v:ℝ≥0}{Y:ℕ→ W}{y:W} (t:Tendsto d atTop (𝓝 v))(h:Tendsto Y atTop (𝓝 y)): Tendsto (fun i=> E (d i) (Y i)) atTop (𝓝 (E v y)):=by
 exact tightE (S) t h
where
 tightE {H:Hilbert}{j:Axis}(Q:OS.Semigroup H j){n:ℕ→ℝ≥0}{u:ℝ≥0}{X:ℕ→H}{x':H}(t:Tendsto n atTop (𝓝 u))(h:Tendsto X atTop (𝓝 x')) : Tendsto (fun k=> Q.E (n k) (X k)) atTop (𝓝 (Q.E u x')):=by
    have hA:Tendsto (fun k=> Q.E (n k) (X k)-Q.E (n k) x') atTop (𝓝 (0:H)):=by
       rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero (fun _=>norm_nonneg _) (g:=fun k=>‖X k-x'‖) (fun k=>?_) ?_
       · rw [←map_sub]; exact ((Q.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (Q.shrinks ..))
       simpa only [sub_self,norm_zero] using (h.sub_const x').norm
    simpa only [Function.comp_apply,zero_add,sub_add_cancel] using hA.add ((Q.continuousE x').continuousAt.tendsto.comp t)
lemma cart_lim {d:ℕ→Vantage}{v:Vantage}{Y:ℕ→ W}{y:W}(t:Tendsto d atTop (𝓝 v))(h:Tendsto Y atTop (𝓝 y)): Tendsto (fun i=> U (d i) (Y i)) atTop (𝓝 (U v y)):=by
 exact tightC (X:=W) (U) (fun v=>P.cart_pay ..) (P.cart_cont a (P.otherSpectrum 3 a x)) t h
where
 tightC{X:Hilbert}(F:Vantage→X.Op)(w:∀v, ‖F v‖ ≤ 1)(p:∀z:X, Continuous (fun v=>F v z)){s:ℕ→Vantage}{x:Vantage}{b:ℕ→X}{g:X}(u:Tendsto s atTop (𝓝 x))(h:Tendsto b atTop (𝓝 g)): Tendsto (fun i=> F (s i) (b i)) atTop (𝓝 (F x g)):=by
    have hz:Tendsto (fun k=> F (s k) (b k)-F (s k) g) atTop (𝓝 (0:X)):=by
       rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero (fun _=>norm_nonneg _) (g:=fun k=>‖b k-g‖) (fun k=>?_) ?_; rw [←map_sub]; exact ((F _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (w _)); simpa only [sub_self,norm_zero] using (h.sub_const g).norm
    simpa only [Function.comp_apply,zero_add,sub_add_cancel] using hz.add (show Tendsto (fun i=>F (s i) g) atTop (𝓝 (F x g)) from (p g).continuousAt.tendsto.comp u)
local notation "κ"=>valley P x a
lemma valley_lim{u:ℕ→ℝ}{z:ℝ}{d:ℕ→Vantage}{v:Vantage}{X Y:ℕ→ W}{w y:W}(e:Tendsto u atTop (𝓝 z))(t:Tendsto d atTop (𝓝 v))(hx:Tendsto X atTop (𝓝 w))(h:Tendsto Y atTop (𝓝 y)): Tendsto (fun i=>κ (u i) (d i) (X i) (Y i)) atTop (𝓝 (κ z v w y)):=hx.inner (cart_lim P x a t (heat_lim P x a (continuous_real_toNNReal.continuousAt.tendsto.comp e) h))
lemma valley_scale(t:ℝ)(v:Vantage)(p w:W)(r:ℝ): κ t v ((r:ℂ) • p) ((r:ℂ) • w)= (r:ℂ)^2 *κ t v p w :=by
 exact scalv (X:=W) (U v ∘L E t.toNNReal) ..
where scalv {X:Hilbert}(Y:X.Op)(r:ℝ)(p w:X): inner ℂ ((r:ℂ) • p) (Y ((r:ℂ) • w))= (r:ℂ)^2 * inner ℂ p (Y w):=by rw [map_smul, inner_smul_left,inner_smul_right,Complex.conj_ofReal]; ring
/- evaluate total heat in terms of prepaid setbacks. exact for lattice motion; no assumption S on other orientations. -/
lemma valley_pre(t c r:ℝ)(h:0≤c)(v:0≤r)(u:c+r<t)(p w:W)(F G y:Vantage):
 κ t y p w= κ (t-(c+r)) (y+F-G) (U F (E c.toNNReal p)) (U G (E r.toNNReal w)):=by
 refine pricey (X:=(W)) (S) (U) (fun d k z => ?_) (fun d i q=>P.warm_drive a ξ d i q) (fun a b b'=> ?_) h v u p w F G y
 · exact (DFunLike.congr_fun (P.cart_paves a ξ d k) z).symm
 · exact P.inner_pay .. -- infer ν from X?
where
 pricey {X:Hilbert}{a:Axis}(Q:OS.Semigroup X a)(V:Vantage→X.Op)(h:∀ p q (z:X), V p (V q z)=V (p+q) z)(v:∀ d i (z:X), Q.E i (V d z)=V d (Q.E i z))(u:∀d (a b:X), inner ℂ (V d a) (V d b)=inner ℂ a b){c r t:ℝ}(hc:0 ≤c)(ht:0≤ r)(hr:c+r < t)(p w:X)(F G y:Vantage): inner ℂ p (V y (Q.E t.toNNReal w)) = inner ℂ (V F (Q.E c.toNNReal p)) (V (y+F-G) (Q.E ((t-(c+r)).toNNReal) (V G (Q.E r.toNNReal w)))):=by
    have hg:c.toNNReal + ((t-(c+r)).toNNReal + r.toNNReal)= t.toNNReal:=by ext; simp only [NNReal.coe_add,Real.coe_toNNReal _ (sub_nonneg.mpr hr.le),Real.coe_toNNReal _ hc,Real.coe_toNNReal _ ht,Real.coe_toNNReal _ ((add_nonneg hc ht).trans hr.le)]; linarith only
    rw [v,h,show y+F-G+G=F+y by abel,←h,u,Q.swing,v,← ContinuousLinearMap.comp_apply (Q.E _), ← Q.time, ← ContinuousLinearMap.comp_apply (Q.E _),←Q.time,add_assoc,hg]
lemma valley_roll(t:ℝ)(v y z:Vantage)(p w:W) :κ t v (U y p) (U z w)=κ t (v+z-y) p w:=by
 let R:= v+z-y
 calc κ t v (U y p) (U z w)= inner ℂ (U y p) (U v (E t.toNNReal (U z w))):=rfl
      _=inner ℂ (U y p) (U v (U z (E t.toNNReal w))):=congrArg (fun a:W=>inner ℂ (U y p) (U v a)) (P.warm_drive ..)
      _=inner ℂ (U y p) (U y (U R (E t.toNNReal w))):= congrArg (inner ℂ (U y p)) ((DFunLike.congr_fun (P.cart_paves a ξ v z) _).symm.trans ((congrArg (fun t':Vantage=>U t' (E t.toNNReal w)) (show v+z=y+R by unfold R; abel)).trans (DFunLike.congr_fun (P.cart_paves a ξ y R) _)))
      _=_:=P.inner_pay ..
#print axioms valley_lim
#print axioms valley_pre
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
