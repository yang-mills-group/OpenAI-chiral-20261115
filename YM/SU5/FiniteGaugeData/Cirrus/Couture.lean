import YM.SU5.FiniteGaugeData.Cirrus.Rakish
import YM.SU5.FiniteGaugeData.Maypole.Piquant
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison Flute
open Mink Mink.General Vp.Folio
open scoped Topology NNReal InnerProductSpace
local notation "a"=>timeAxis
variable {H:Axis→Hilbert}(S:∀ i:Axis, OS.Semigroup (H i) i)
variable (Ω:(i:Axis)→(H i).space)(Ω':Bench (S a))(ht:Ω'.val=Ω a) (hΩ:∀ p:E4,M (S a) p Ω'.val=Ω'.val)(o:‖Ω'.val‖=1)
variable {ι:Type}(G:Canopy (H a) ι)(J K:Set ι)
open Gem
variable (V:Gem.Tribe G){r:Axis→ℝ≥0}
variable (L U: Cartouche G r)
-- no relative label coincidences when weapons estimated. Keep exact widths.
def Sewable :Prop:= ∀ t:Axis, Injective (clockV t (mingle L.points U.points))
variable (z:Sewable G L U)(x:Axis)
private lemma certified_fit {t:Axis}{n:ℕ}{p:Points n}{L:List (Fin n)}(q:-(r t:ℝ)<(r t:ℝ))(b:ProofOrder p t L)(h:∀ i,p i t∈ Ioo (-(r t:ℝ)) ((r t:ℝ))) : Sau (spire r t p) ((Sum.inl false):: L.map Sum.inr ++ [Sum.inl true]):=by
 apply List.pairwise_cons.mpr
 let f:=spire r t p
 refine ⟨fun i v=>?_,List.pairwise_append.mpr ⟨List.pairwise_map.mpr b,List.pairwise_singleton .., ?_⟩⟩
 · rcases List.mem_append.mp v with h'|d; · obtain ⟨j,v,rfl⟩:= List.mem_map.mp h'; exact (h j).1
   exact (List.mem_singleton.mp d) ▸ q
 intro x v y p; obtain ⟨j,v,rfl⟩:= List.mem_map.mp v; exact (List.mem_singleton.mp p) ▸ (h j).2
local notation "Y"=> mingle L.points U.points
include L in
lemma enables : -(r x:ℝ)<(r x:ℝ):= by
 -- include L explicitly; auction
 have h:=(Cartouche.behind L x); exact (List.pairwise_cons.mp h).1 (Sum.inl true) (List.mem_append.mpr (Or.inr List.mem_cons_self))
def stitch : Cartouche G r where
 count:= L.count+U.count
 points:= mingle L.points U.points
 chips:= Fin.append L.chips U.chips
 roll x:=(SortApp (clockV x (Y)) (z x)).choose
 perm x:=(SortApp (clockV x (Y)) (z x)).choose_spec.1
 behind x:=certified_fit (enables G L x) ((SortApp (clockV x (Y)) (z x)).choose_spec.2) (by apply Fin.addCases; · intro i; rw [M_left]; exact footprint G r x L i
                                                                                            intro i; rw [M_right]; exact footprint G r x U i) -- ts.
include ht hΩ
lemma quote : inner ℂ Ω'.val (traceB S G V r a L Ω'.val)=G.Sr (S a) Ω' L.points L.chips (L.roll a):=by
 let X:= Ω a; let R:=traceB S G V r a L; let u:=ink G a L; let d:= -(r a:ℝ); let S₀:= S a; let f:= receiptI G V a
 have v: (billBefore S₀ G.grade d 0 u).adjoint Ω'.val=Ω'.val:= ?_; swap; · -- repeat fixL
    have hx:LaneE a d u:=(readyFw G a L).1; generalize he:u=w at hx ⊢; cases w with
    | nil=> rw [billBefore]; rw [show (1:(H a).Op).adjoint= 1 from star_one _]; rfl
    | cons i w=> rw [budgetFoot, show ContinuousLinearMap.adjoint _ =_ from warm_a S₀ _ (sub_pos.mpr (hx.2 _ List.mem_cons_self))]; exact earnO _ _ hΩ _ (sub_pos.mpr (hx.2 _ List.mem_cons_self)) -- ambiguous
 let y:= G.senses L.chips; have he:R Ω'.val= face S₀ Ω'.val f G.grade d u:= ht ▸ (realPlay S G V a Ω ( ht ▸ hΩ) L).1; rw [he]; unfold face Front; change inner ℂ Ω'.val (billBefore S₀ G.grade d 0 u _) = _; rw [← ContinuousLinearMap.adjoint_inner_left (billBefore S₀ G.grade d 0 u),v]; apply congrArg (fun A : (H a).Op=>inner ℂ Ω'.val (A Ω'.val)); apply Eq.symm; apply mappingF; · intro i; exact congrArg (coreSp (S a) (L.points.ofLp i)) (usea G V (L.chips i)).symm
 intro i j; rfl
-- poly assignments
abbrev Stripe (J:Set ι)(L: Cartouche G r):=∀ i,(L.chips i).fst∈ J
variable (E:G.Earned (S a) Ω')(P:Pale (S a) Ω' G J K) (e:Ray)(W:Shelf (S a) (magnet e))
def value_κ(x:(H a).Op):= inner ℂ Ω'.val (x Ω'.val)
local notation "Q"=> value_κ S Ω'
include Ω ht hΩ E P W o
lemma contour (q:Stripe G J L)(w:Stripe G K U) : Q (traceB S G V r a (stitch G L U z))= Q (traceB S G V r a L)* Q (traceB S G V r a U):=by
 unfold value_κ; let y:= stitch G L U z; have hz(M:Cartouche G r): value_κ S Ω' (traceB S G V r a M)= G.ornate (S a) Ω' M.points M.chips:= (quote S Ω Ω' ht hΩ G V M).trans (E.realRoad _ _ _ _ (M.perm a) (PricesRoll G r a M)).symm
 change Q _= Q _ * Q _; rw [hz,hz,hz]; exact glories (S a) Ω' hΩ o G J K _ _ _ _ e P E q w W (order_in y.points a (y.roll a) (y.perm a) (PricesRoll G r a y))
#print axioms contour
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
