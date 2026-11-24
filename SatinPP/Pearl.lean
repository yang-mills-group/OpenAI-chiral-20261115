import YM.SU5.Reconstruction.Crease.Fountain
import SatinPP.CanvasBudget
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open Anvil (Limited Pearl)
open BridgeClub (star_Limited Limit_World)

section
variable {X:Hilbert}{j:Axis}(S:OS.Semigroup X j)

abbrev Stamp (X:Hilbert):= ℝ→ℝ→X.Op

/-- Singular prices. Only accessed at positive heat parameters.
The two parameters give the wall distances bought on left and right.
The bound represents one instantaneous field in arbitrary heat clearances,
of thermal order ≤m. -/
structure Paid (m:ℕ)(c:ℝ)(A:Stamp X):Prop where
 pos:0<c
 fits {u v s t:ℝ} (a:0<s)(b:0<t)(p:s≤u)(q:t≤v):
     A u v=jacket S (u-s) (v-t) (A s t)
 le {u:ℝ}(a:0<u)(p:u≤1):‖A u u‖ ≤ c/u^m

def Turn (A:Stamp X):Stamp X:= fun u v=>star (A v u)

lemma jacket_star (A:X.Op)(s t:ℝ):star (jacket S s t A)=jacket S t s (star A):=by
    change star ((S.E _)*A*S.E _)=S.E _*(star A)*S.E _
    rw [star_mul,star_mul,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.star_eq_adjoint (S.E _),S.sym,S.sym,mul_assoc]


lemma jacket_Limited (u v:ℝ){l:Filter ℕ}{A:ℕ→X.Op}{B:X.Op}
   (h:Limited l A B): Limited l (fun i=>jacket S u v (A i)) (jacket S u v B):=
   (h.toLeft (Anvil.Pearl.still l (S.E u.toNNReal))).toRight
   (Anvil.Pearl.still l (S.E v.toNNReal))

variable {S}{A:Stamp X}{m:ℕ}{c:ℝ}
lemma Paid.turn (h:Paid S m c A):Paid S m c (Turn A):=by
 refine ⟨h.pos,fun a b p q=>?_,fun a p=>?_⟩
 · simp only [Turn,h.fits b a q p,jacket_star]
 · simpa [Turn] using h.le a p
variable {l:Filter ℕ}
lemma Limited_law [l.NeBot]{D F:ℕ→X.Op}{A B:X.Op}
   (h:Limited l D A)(p:Limited l F B)(q:D=ᶠ[l]F): A=B:=by
 apply ContinuousLinearMap.ext; intro y; apply ext_inner_left ℂ; intro x
 exact tendsto_nhds_unique ((h.confirms x y).congr' (q.mono fun i z=>by rw [z])) (p.confirms x y)
end

def finalReel:Ultrafilter ℕ:= Ultrafilter.of atTop
lemma final_reels : (finalReel:Filter ℕ) ≤ atTop:=Ultrafilter.of_le _

lemma limited_final {X:Hilbert}{F:ℕ→X.Op}{c:ℝ}(p:0<c)
  (h:∀ᶠ i in atTop,‖F i‖≤c): ∃ A, Limited (finalReel:Filter ℕ) F A:=by
 let Y(i:ℕ):= if ‖F i‖≤c then F i else 0
 obtain ⟨A,t,g⟩:=Limit_World finalReel (H:=X) (A:=Y) p.le fun i=>by
    dsimp [Y]; split_ifs; assumption; simpa using p.le

 refine ⟨A,⟨_,p.le,h.filter_mono final_reels⟩,fun x y=>?_⟩
 exact (g.confirms x y).congr' ((h.filter_mono final_reels).mono fun _ w=>by rw [show Y _=_ from if_pos w])

namespace Spine
open Aria
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
local notation "ξ"=>P.advocate 3 x j
local notation "Lock"=>P.locket j (P.advocate 3 x j)
local notation "H"=>P.ColorHil j (P.advocate 3 x j)
local notation "Y"=>P.physicalEnergy j (P.advocate 3 x j)


local notation "ω"=>P.colorZero j ξ
lemma locket_Turn (l:List Axis)(A:P.Apron)(p q:ℝ):
 Lock (A.pivot P (j::l)) p q=star (Lock (A.pivot P l) q p):=by
 unfold locket; rw [jacket_star,Apron.peer,Apron.pivot_cons]; rfl

lemma locket_empty (A:P.Apron)(p q:ℝ):
 Lock A p q ω = P.beamRaw j x A p:=by
    change (Y).E _ (A.engine P j ξ ((Y).E _ ω))=_
    rw [P.sector_hot]

variable (A:ℕ→ P.Apron)
local notation "orion"=> ∀ j:Axis,List Axis→ℝ→P.ColorHil j (P.advocate 3 x j)

abbrev Concert (P:Spine)(x:P.Spectrum0 3):=
    ∀ j:Axis,List Axis→Stamp (P.ColorHil j (P.advocate 3 x j))

local notation "F"=> (finalReel:Filter ℕ)
local notation "Ξ" j:max=> (P.advocate 3 x j)

-- no structure extend dependent unification heavy
structure ConcertPlays (B:ℝ)(D:Concert P x): Prop where
 bought: P.LocketFifth x A B
 provides(j:Axis)(l:List Axis)(p q:ℝ)(u:0<p)(v:0<q):
     Limited F (fun k=>P.locket j (Ξ j) ((A k).pivot P l) p q) (D j l p q)


lemma plays {B:ℝ}(R:P.LocketFifth x A B):∃ D,P.ConcertPlays x A B D:=by
 have a(j:Axis)(l:List Axis)(p q:ℝ)(u:0<p)(v:0<q):
     ∃ D,Limited F (fun k=>P.locket j (Ξ j) ((A k).pivot P l) p q) D:=by
    let e:=min 1 (min p q)
    have g:0<e:=lt_min zero_lt_one (lt_min u v)
    have z:=R.price j l e g (min_le_left ..)
    refine limited_final (fifth_pos R.pos g) (z.mono fun i h=>?_)

    have ht:((A i).pivot P l).realWidth P j≤e:=(Apron.pivot_w _ ..).le.trans h.1.le
    rw [P.widen_locket j _ _ ht ht ((min_le_right ..).trans (min_le_left ..)) ((min_le_right ..).trans (min_le_right ..))]
    exact (jacket_cost ..).trans h.2
 choose! D e using a
 exact ⟨D,R,e⟩
variable {P x A}{B:ℝ}{D:Concert P x}(C:P.ConcertPlays x A B D)(l:List Axis){p q:ℝ}
include C
lemma ConcertPlays.mirrors (u:0<p)(v:0<q):
    D j (j::l) p q=star (D j l q p):=by
 refine Limited_law (C.provides j (j::l) _ _ u v) (star_Limited (C.provides j l _ _ v u))
      (Eventually.of_forall ?_)
 exact fun _=>P.locket_Turn ..


lemma ConcertPlays.paid : Paid (P.physicalEnergy j ξ) 5 B (D j l):=by
 refine ⟨C.bought.pos,?_,?_⟩
 · intro u v s t a b h k
   refine Limited_law (C.provides j l _ _ (a.trans_le h) (b.trans_le k))
      (jacket_Limited _ _ _ (C.provides j l _ _ a b)) ?_
   have z(e:ℝ)(p:0<e):∀ᶠ i in F, ((A i).pivot P l).realWidth P j <e:=
      ((C.bought.price j l _ (lt_min zero_lt_one p) (min_le_left ..)).filter_mono final_reels).mono fun i w=>
        (Apron.pivot_w _ ..).le.trans_lt (w.1.trans_le (min_le_right ..))
   exact ((z s a).and (z t b)).mono fun i w=>P.widen_locket _ _ _ w.1.le w.2.le h k
 intro u v h
 exact Anvil.Limited.convertible F (fifth_pos C.bought.pos v).le (C.provides j l u u v v)
   (((C.bought.price j l u v h).filter_mono final_reels).mono fun _ h=>h.2)

lemma ConcertPlays.vacuum {V: orion}
   (R:Radiates P x A V)(u:0<p)(v:0<q):
   D j l p q ω=V j l p:=by
 apply ext_inner_left ℂ; intro z
 refine tendsto_nhds_unique ((C.provides j l p q u v).confirms z _) ?_
 simp_rw [P.locket_empty]
 exact tendsto_const_nhds.inner ((R.cash j l p u).mono_left final_reels)


#print axioms ConcertPlays.vacuum
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
