import MarchC.Shirts
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
variable(P:Spine)(x:P.Spectrum0 3)(F:ℕ)(C D:ℕ→ℕ→ℝ)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "W"=>P.ManyF 3 (ξ)
local notation "Ω"=>P.heaven 3 ξ
local notation "A"=>paster (Ω)
local notation "E"=> (P.seasons 3 (ξ)).E
local notation "S"=>P.seasons 3 (ξ)
local notation "U"=>P.cartage 3 (ξ)
local notation "d" j:max=>tidal P F j
local notation "Cmor"=>pointT P F C D ξ
local notation "m"=>poseMirror 3
lemma ortho (p q:W): inner ℂ (A p) (A q)≠0 ↔ inner ℂ p q - star (inner ℂ (Ω) p)* inner ℂ (Ω) q≠0:= iff_of_eq (congrArg (fun x:ℂ=>x≠0) (together (Ω) (P.stone_norm 3 ξ) p q))
noncomputable def dot3 (p q:Vantage):ℂ:= inner ℂ (A (Cmor (m p))) (A (Cmor q))
noncomputable def oneM (v:W):ℂ:= star (inner ℂ (Ω) v)* inner ℂ (Ω) v
-- observer.Pane
variable (j:ℕ)(v:P.ManyF 3 (P.otherSpectrum 3 3 x))(p:Aloft.PeriodS P F C D x j v)(u w:Vantage)
include p
private lemma mean_joint (a:Vantage)(t:d j<a 3): inner ℂ (Ω) (Cmor a)=inner ℂ (Ω) v:=by
 let e:=a-crest P F; let h:=(a 3-d j).toNNReal
 exact (congrArg (inner ℂ (Ω)) (p.2 a t)).trans ((congrArg (fun k:W=>inner ℂ k (U e (E h v))) (P.cart_empty 3 ξ e).symm).trans ((P.inner_pay 3 ξ e (Ω) (E h v)).trans ((OS.Semigroup.swing (S) h (Ω) v).symm.trans (congrArg (fun k:W=>inner ℂ k v) (P.heaven_hot 3 ξ h)))))
omit p in
lemma clock_neg (u:Vantage):m u 3= -u 3:= by change opposeR 3 u 3=_; simp [opposeR,mirrorΩ]
-- omit p from clock
lemma ratio (fu:d j < -u 3)(fw:d j < w 3): inner ℂ (Cmor (m u)) (Cmor w)= valley P x 3 ((w-u) 3-(d j+d j)) (w-u) v v:=by
 let t:=m u; let t1:=(t 3-d j).toNNReal; let t2:=(w 3-d j).toNNReal; let k:=crest P F
 have hp:t 3= -u 3:=clock_neg .. -- omit
 have ht:d j<t 3:=hp.symm ▸ fu
 let x':=w-u
 let F':=x' 3-(d j+d j)
 have eqS:t1+t2=F'.toNNReal:=by
    have hx:F' = (t 3-d j)+(w 3-d j):=by unfold F' x'; rw [Pi.sub_apply,hp]; ring
    ext; rw [NNReal.coe_add,Real.coe_toNNReal F' (by rw [hx]; exact (add_pos (sub_pos.mpr ht) (sub_pos.mpr fw)).le),hx]; exact congrArg₂ (·+·) (Real.coe_toNNReal _ (sub_pos.mpr ht).le) (Real.coe_toNNReal _ (sub_pos.mpr fw).le)
 have hU:U (w-t)=U x':= of_slideP x 3 _ _ (fun i p=>by change _-(opposeR 3 u i)=w i-u i; rw [show opposeR 3 u i=u i from (by simp [opposeR,mirrorΩ,p])])
 calc inner ℂ _ _ = inner ℂ (U (t-k) (E t1 v)) (U (w-k) (E t2 v)):=congrArg₂ (inner ℂ) (p.2 t ht) (p.2 w fw)
      _=inner ℂ (E t1 v) (U (w-t) (E t2 v)):= roller (X:=W) U (fun a b g=> DFunLike.congr_fun (P.cart_paves 3 ξ a b) g) (fun a p q=>P.inner_pay 3 ξ a p q) t k w _ _
      _=inner ℂ v (U (w-t) (E (t1+t2) v)):= liner (X:=W) (S) (U (w-t)) (fun t' x'=>P.warm_drive 3 ξ _ t' x') t1 t2 v 
      _=inner ℂ v (U x' (E F'.toNNReal v)):= congrArg (inner ℂ v) (congrArg₂ (fun (f:(W).Op) (Z:ℝ≥0)=> f (E Z v)) hU eqS)
      _=_:=rfl
where
 liner{X:Hilbert}{a:Axis}(S':OS.Semigroup X a)(V:X.Op)(h:∀d' x',S'.E d' (V x')=V (S'.E d' x'))(t1 t2:ℝ≥0)(v:X): inner ℂ (S'.E t1 v) (V (S'.E t2 v))=inner ℂ v (V (S'.E (t1+t2) v)):=by rw [S'.swing,h,S'.time]; rfl
 roller{X:Hilbert}(R:Vantage→X.Op)(u:∀a b (g:X), R (a+b) g=R a (R b g))(v:∀a (p q:X),inner ℂ (R a p) (R a q)=inner ℂ p q)(b k c:Vantage)(i j:X): inner ℂ (R (b-k) i) (R (c-k) j)= inner ℂ i (R (c-b) j):= by rw [show c-k=(b-k)+(c-b) by abel,u,v] -- rw nesting issue
lemma ratioB(fu:d j < -u 3)(fw:d j < w 3): dot3 P x F C D u w= valley P x 3 ((w-u) 3-(d j+d j)) (w-u) v v - oneM P x v:=by
 let hp:(m u) 3= -u 3:=clock_neg ..
 let e:=together (Ω) (P.stone_norm 3 ξ) (Cmor (m u)) (Cmor w)
 exact e.trans (congrArg₂ (·-·) (ratio P x F C D j v p u w fu fw) (congrArg₂ (fun (a b:ℂ)=>star a*b) (mean_joint P x F C D j v p (m u) (hp.symm ▸ fu)) (mean_joint P x F C D j v p _ fw)))
lemma veneers(k:ℕ)(z:W)(e:Aloft.PeriodS P F C D x k z):oneM P x v=oneM P x z:=by
 let a:Vantage:=fun _=>max (d j) (d k)+8
 have h₀:0<(8:ℝ):=by norm_num
 have g:d j<a 3:=(le_max_left ..).trans_lt (lt_add_of_pos_right _ h₀); have h:d k<a 3:=(le_max_right ..).trans_lt (lt_add_of_pos_right _ h₀)
 exact congrArg (fun t:ℂ=>star t*t) ((mean_joint P x F C D j v p a g).symm.trans (mean_joint P x F C D k z e a h))
#print axioms ratio
#print axioms veneers
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
