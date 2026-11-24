import YM.CF.BPress.Locale.Atlas
import YM.CF.BPress.Palmer.Basics
/-! Uniform contour price for the block torus's geometry. Nothing ever uses pulled-back adjacency (this map folds); projections only for bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Contour
open Lattice RG Grid Branch Finset Cube Bands Locale Palmer
open scoped Classical BigOperators
variable {s : Side}
private def meter (x: Per s) := delta1 s x 0
private lemma meter_lt (x: Per s) : meter x < s.val:=by rw [meter,delta1,sub_zero,ZMod.valMinAbs_natAbs_eq_min]; exact (min_le_left ..).trans_lt (x.val_lt)
private def fold0 (r:Side)(x: Per s): Per r:= ↑(meter x)
private lemma fold_span (r:Side)(x y: Per s) : delta1 r (fold0 r x) (fold0 r y) ≤ delta1 s x y:=by
 have he(i j:Per s)(h:meter j≤meter i):delta1 r (fold0 r i) (fold0 r j)≤ delta1 s i j:=by
    have ht:fold0 r i=fold0 r j+ ↑(meter i-meter j):=by unfold fold0; rw [Nat.cast_sub h]; abel
    rw [ht]; refine (delta_nat ..).trans (Nat.sub_le_of_le_add (d_one_triangle _ j 0)) -- tune
 rcases le_total (meter y) (meter x) with p|p; exact he _ _ p; rw [d_sym,d_sym y]; exact he _ _ p
private def sign (x:Per s) : Bool:= decide (0≤ x.valMinAbs)
private lemma folds {r:Side}(h:s≤r)(x y:Per s)(p:fold0 r x=fold0 r y)(e:sign x= sign y): x=y:=by
 have hp:=congrArg ZMod.val p; unfold fold0 at hp; rw [ZMod.val_natCast_of_lt ((meter_lt x).trans_le (show s.val≤r.val from h)), ZMod.val_natCast_of_lt ((meter_lt y).trans_le (show s.val≤r.val from h))] at hp; unfold meter delta1 at hp; simp only [sub_zero] at hp; unfold sign at e; have ht:(0≤ x.valMinAbs) ↔ 0 ≤ y.valMinAbs:=by simpa using e
 have he:x.valMinAbs=y.valMinAbs:=by omega
 rw [← ZMod.coe_valMinAbs x, ←ZMod.coe_valMinAbs y,he] -- recursive
variable {b:BandWidth}(X:Bands s b)(R:Hangar s)
lemma folio : Sole (shape X R) 16:=by
 let r:= max X.Q R.period; let f(i:SiteX X R):= event (fold0 r i.1) (fun j=>fold0 r (i.2 j)); refine ⟨r,f,fun i j h=> ?_, fun x=> ?_⟩
 · apply (delta_le (d:=4)).2; intro k; let v:= max_le_iff.mp (show _ ≤ _ from h); refine Fin.cases ?_ (fun z:Fin 3=>?_) k <;> clear k; exact (fold_span ..).trans v.1; exact (fold_span ..).trans ((delta_at i.2 j.2 z).trans v.2)
 let g(i:SiteX X R) : Fin 4 → Bool:= Fin.cases (sign i.1) (fun j=>sign (i.2 j)); suffices h:(univ.filter (fun i:SiteX X R=>f i=x)).card≤(univ:Finset (Fin 4→Bool)).card by simpa using h
 refine card_le_card_of_injOn g (fun i _=>mem_univ _) (fun i p j q v=>?_); have ht:=((mem_filter.mp (mem_coe.mp p)).2).trans ((mem_filter.mp (mem_coe.mp q)).2.symm); exact Prod.ext (folds (le_max_left ..) _ _ (congrFun ht 0) (congrFun v 0)) (funext fun k=> folds (le_max_right ..) _ _ (congrFun ht k.succ) (congrFun v k.succ)) -- tune succ defeq
end YM.CF.BPress.Contour
