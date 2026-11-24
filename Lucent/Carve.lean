import Lucent.Cadenza
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Stationary (Gaia)
open Ballad.Twah SpinReceipt Emu Gist
open Regis Circuit
variable {I J K:Type}


/-- Wake calls are finite polynomials of pair coupons. -/
structure Votive (I:Type) where
 S: Stamp I→ Stamp I→ℂ
 G: Tint I→ Tint I→ℂ

namespace Votive
variable (Z:Votive I)
def fugue (j:List (Loop I)):ℂ:= (1/2:ℂ)^j.length * runes Z.S (anatomize j)
abbrev play:=heed Z.G Z.fugue
def quoted(S:Stencil I):ℂ:= S.quote Z.play
end Votive

def FieldPlan.aura (d:FieldPlan I) : Votive I:=⟨germRho (outside d.roles) (upstairs d.roles),fair d.hands⟩
lemma faq_call (d:FieldPlan I)(S:Stencil I):faq d S=d.aura.quoted S:=rfl
structure Vow{I:Type} (a:ℕ→Votive I)(b:Votive I):Prop where
    spin(i j): Tendsto (fun n=> (a n).S i j) atTop (𝓝 (b.S i j))
    paint(i j): Tendsto (fun n=> (a n).G i j) atTop (𝓝 (b.G i j))
#check @quote_road
#check @offer_v
#check @vellMap
#check @vellDivide
#check @rune_map

lemma Vow.quotes [Fintype I]{a:ℕ→Votive I}{b:Votive I}(h:Vow a b)(S:Stencil I):
    Tendsto (fun n=>(a n).quoted S) atTop (𝓝 (b.quoted S)):=by
 unfold Votive.quoted; simpa using
    quote_road S (h:=b.play) (G:=fun _=>1) (f:=fun n=>(a n).play) (fun j _=>by
       simp_rw [one_mul]; unfold Votive.play heed Votive.fugue

       have hp(L:List (Tint I)): L.Pairwise (fun i j=> Tendsto (fun n=>(a n).G i j) atTop (𝓝 (b.G i j))):=by induction L with| nil=>exact .nil|cons i L ih=> exact .cons (fun j _=>h.paint i j) ih
       exact (vellTendsto _ _ _ (hp _)).mul ((offer_v b.S (fun n=>(a n).S) h.spin _).const_mul _))

abbrev rebill {H:Type}(k:I→K) : I×H→K×H:=Prod.map k id
def Join.swapI (k:I→K)(x:Join I):Join K:=⟨x.flash.map (rebill k),x.loom.map (rebill k)⟩
structure Votive.part (Q: Votive K)(p:Votive I) (f:I→K):Prop where
   sameGauge(x y):Q.G (rebill f x) (rebill f y)=p.G x y
   sameSpin(x y):Q.S (rebill f x) (rebill f y)=p.S x y
def Votive.muted(Q:Votive K)(f:I→K)(g:J→K):Prop:=
 (∀ x y,Q.G (rebill f x) (rebill g y)=0) ∧ (∀ x y,Q.S (rebill f x) (rebill g y)=0)

variable {Q:Votive K}{E:Votive I}{D:Votive J}{f:I→K}{g:J→K}
lemma anatomy (f:I→K)(L: List (Loop I)) : anatomize (L.map (rebill f))=(anatomize L).map (rebill f) := by
 unfold anatomize; rw [List.flatMap_map,List.map_flatMap]; rfl
lemma parts_quote (h:Q.part E f)(p:Q.part D g)(j:Q.muted f g)(x:Join I)(y:Join J):
  Q.play ((x.swapI f).glue (y.swapI g))= E.play x * D.play y:=by
 simp only [Votive.play, heed, Join.glue, Join.swapI, Votive.fugue,List.length_append,List.length_map, pow_add]
 rw [show anatomize ((x.loom.map (rebill f))++y.loom.map (rebill g))=_ from List.flatMap_append, show (x.loom.map (rebill f)).flatMap duals=_ from anatomy f _, show (y.loom.map (rebill g)).flatMap duals=_ from anatomy g _]
 rw [vellDivide,rune_divide]
 · rw [vellMap _ _ _ h.sameGauge, vellMap _ _ _ p.sameGauge,rune_map E.S _ _ _ (fun _ _=>(h.sameSpin ..).symm),rune_map D.S _ _ _ (fun _ _=>(p.sameSpin ..).symm)]; ring
 · intro i w k v; obtain ⟨t,_,rfl⟩:=List.mem_map.mp w; obtain ⟨u,_,rfl⟩:=List.mem_map.mp v; exact j.2 t u
 intro i w k v; obtain ⟨t,_,rfl⟩:=List.mem_map.mp w; obtain ⟨u,_,rfl⟩:=List.mem_map.mp v; exact j.1 t u

lemma parts_done (h:Q.part E f)(p:Q.part D g)(j:Q.muted f g)(x:Stencil I)(y:Stencil J):Q.quoted ((x.remake f)*(y.remake g))= E.quoted x*D.quoted y:=by
 unfold Votive.quoted; rw [Stencil.mul_q,Stencil.remake_q]; simp_rw [Stencil.remake_q]
 have t(a):y.quote (fun b=> Q.play ((Join.swapI f a).glue (Join.swapI g b)))=E.play a * y.quote D.play:=by
   simp_rw [parts_quote h p j]; exact Stencil.quote_lift D.play y (fun b=>E.play a * b) (mul_zero _) (mul_add _) (fun _ _=> by rw [Algebra.mul_smul_comm])
 change x.quote (fun a=> y.quote (fun b=> Q.play ((Join.swapI f a).glue (Join.swapI g b))))=_
 simp_rw [t]
 exact Stencil.quote_lift E.play x (· * y.quote D.play) (zero_mul _) (fun _ _=>add_mul ..) (fun _ _=>by rw [Algebra.smul_mul_assoc])
lemma Votive.partial {Q:Votive I}{E:Votive I}(h:Q.part E id):Q=E:= by
 cases Q; cases E
 congr; exact funext fun i=> funext (h.sameSpin i); exact funext fun i=>funext (h.sameGauge i)
