import YM.CF.BPress.Slice
import YM.CF.BPress.Grid.Thin
/-!
`eq:B-mood` `eq:B-lift` and Borel label choices, tests on the actual horizontal variables. Choose the labeling section giving value at label zero **nearest to identity**. Works also if going to gauges where face tests look very different. The supportive N mark uses ALL lifts (before gauge fixes), not asserting a lift works off valid fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory Lattice SU Mag Cube Grid Filter
open scoped Topology BigOperators Classical Matrix
namespace Sheet
open Set
variable {s : Side}
abbrev Law (s : Side):= Tri s → Fin 5
-- first/second dir, for each Hue index
def first : Fin 3→ SpatialDir:=![0,0,1]
def second : Fin 3→ SpatialDir:=![1,2,2]
lemma directions (i : SpatialDir) : first i < second i:=by fin_cases i <;> decide
lemma directions_back (i j : SpatialDir)(h:i<j):∃ k, i=first k ∧ j= second k:=by fin_cases i<;> fin_cases j <;> first| decide| contradiction
lemma magnet_eval (i : Fin 3) : magnet i= group.ad (generator (first i)) (generator (second i)):=by fin_cases i <;> rfl

-- payments independent of y, periods
structure Atlas extends chord.Chart group where
  tube : ℝ
  liftK : ℝ
  narrow : ℝ
  tunnel : 0<tube
  liftK_pos : 0 < liftK
  sheet : ∀ H∈Mood tube, ∀ h k, Chosen H h → Chosen H k → ∃ i, k=center i*h
  sect : Hue → E
  borel : Measurable sect
  chosen : ∀ H, Chosen H (sect H)
  near : ∀ H, dist H magnet ≤ tube → chord (sect H) 1 ≤ liftK* dist H magnet
  sep_pos : 0<narrow
  apart : Pairwise fun i j=> narrow ≤ chord (center i) (center j)

/- take a measurable section minimizing chord over a finite CENTER shift of a Borel section. -/
lemma closest5 (φ : Hue → E)(p : Measurable φ) : ∃ f : Hue → E, Measurable f ∧ (∀ x, ∃ i, f x=center i*φ x) ∧ ∀ x i, chord (f x) 1 ≤ chord (center i* φ x) 1:=by
 open Finset in
 have h (S : Finset (Fin 5))(t : S.Nonempty) : ∃ f : Hue → E, Measurable f ∧ (∀ x,∃ i∈ S,f x=center i*φ x) ∧ (∀ x i, i∈S → chord (f x) 1 ≤ chord (center i*φ x) 1) := by
   induction S using Finset.induction_on with
   | empty=> contradiction
   | insert i S g ih=>
     let a(x:Hue):=center i*φ x; have he : Measurable a:=measurable_const.mul p
     rcases S.eq_empty_or_nonempty with rfl|v
     · refine ⟨a,he,fun x=>⟨i,by simp,rfl⟩,fun x j z=>?_⟩; rw [insert_empty,Finset.mem_singleton] at z; rw [z]
     obtain ⟨b,c,o,Q⟩:= ih v; let I:={x | chord (a x) 1 ≤ chord (b x) 1}; have hx : MeasurableSet I:= by
       have hor (f:Hue→E)(p : Measurable f) : Measurable (fun x=> chord (f x) 1):= (chord.cont (G:=group)).measurable.comp (f:=fun x : Hue=> (f x,(1:E))) (p.prodMk measurable_const)
       exact measurableSet_le (hor _ he) (hor _ c) -- tune
     refine ⟨I.piecewise a b, Measurable.piecewise hx he c,fun x=>?_,fun x j t=>?_⟩
     · by_cases p:x∈I; exact ⟨i,Finset.mem_insert_self ..,piecewise_eq_of_mem _ _ _ p⟩; rw [piecewise_eq_of_notMem _ _ _ p]; obtain ⟨i,p,h⟩:= o x; exact ⟨i,Finset.mem_insert_of_mem p,h⟩
     by_cases p:x∈I; rw [piecewise_eq_of_mem _ _ _ p]; rcases Finset.mem_insert.mp t with rfl|v; rfl; exact le_trans (show _ from (show chord (a x) 1 ≤ _ from p)) (Q x j v)
     rw [piecewise_eq_of_notMem _ _ _ p]; rcases Finset.mem_insert.mp t with rfl|v; exact le_of_not_ge p; exact Q x j v
 obtain ⟨f,k,p,Q⟩:= h Finset.univ Finset.univ_nonempty; refine ⟨f,k,fun x=>(p x).imp fun i h=>h.2,fun x i=> Q x i (Finset.mem_univ i)⟩

lemma atlas_buy (W : chord.Chart group) : ∃ T: Atlas, T.toChart=W:=by
 obtain ⟨a,b,p,t,x,y⟩:= lift_purchase; obtain ⟨g,d,e⟩:= center_price; obtain ⟨f,k,c⟩:=choice_section; obtain ⟨z,h,E,Q⟩:=closest5 f k; refine ⟨⟨W,a,b,g,p,t,x,z,h,fun H=> ?_,fun H p=>?_,d,e⟩,rfl⟩
 · obtain ⟨i,v⟩:=E H; exact (c H).shift ((shade_rel ..|>.mpr ⟨i,v⟩).symm)
 obtain ⟨h,c',v⟩:=y H p; obtain ⟨i,F⟩:= x H ⟨1,shade_one.symm ▸ p⟩ (f H) h (c H) c'; rw [F] at v; exact (Q H i).trans v

namespace Atlas
variable (T : Atlas) (y : ℝ)

def hue (U : Horiz s) (x : Tri s) : Hue:= WithLp.toLp 2 fun i=> (mA y)⁻¹ • T.logV (plaq U x (first i) (second i))
lemma hue_joint (x : Tri s) : Measurable fun U:Horiz s=> T.hue y U x:= (PiLp.continuous_toLp 2 (fun _ : Fin 3=>group.Color)).measurable.comp (measurable_pi_lambda _ (fun i=> measurable_const_smul ((mA y)⁻¹) (α:=group.Color) |>.comp (T.logV_meas.comp (plaq_cont x (first i) (second i)).measurable)))
lemma hue_adj (a : HFrame s)(U : Horiz s)(x : Tri s): T.hue y (adjust a U) x=spin (a x) (T.hue y U x):=PiLp.ext fun i=>by simp [hue, spin_at, transform_plaq,T.logV_conj]
/-- First (without label) requirements. -/
def passes (U : Horiz s)(x : Tri s) := (∀ i, group.chord (plaq U x (first i) (second i))< T.δ) ∧ T.hue y U x∈Mood (sigmaN y)
lemma passes_meas (x : Tri s) : MeasurableSet {U:Horiz s| T.passes y U x}:= by
 simp only [passes,setOf_and,setOf_forall]; apply MeasurableSet.inter (MeasurableSet.iInter fun i=> measurableSet_lt (group.continuous_chord.measurable.comp (plaq_cont x (first i) (second i)).measurable) measurable_const); exact T.hue_joint y x (mood_closed _).measurableSet
lemma Pass_g (a : HFrame s) {U : Horiz s} {x : Tri s}(h : T.passes y U x) : T.passes y (adjust a U) x:= by
 refine ⟨fun i=>?_,?_⟩; rw [transform_plaq,group.chord_conj]; exact h.1 i
 obtain ⟨k,v⟩:=h.2; refine ⟨k*(a x)⁻¹,?_⟩; rw [T.hue_adj,shade_gauge,spin_dist]; exact v
lemma picked_g (a : HFrame s){U : Horiz s} {x : Tri s}{h:E}(p:Chosen (T.hue y U x) h) : Chosen (T.hue y (adjust a U) x) (h*(a x)⁻¹):= T.hue_adj y a U x|>.symm ▸ p.gauge _

-- B-lift: test *all* assignments, not just the canonical section and its 5 constant translations. The test will include links with positive tangential orientation (inverse costs coincide).
def allowed (U : Horiz s)(V : HFrame s) := (∀ x, T.passes y U x ∧ Chosen (T.hue y U x) (V x)) ∧ ∀ x:FlatLink s, group.chord (adjust V U x)≤sigmaN y
lemma allowed_meas : MeasurableSet {x:Horiz s× HFrame s| T.allowed y x.1 x.2}:= by
 simp only [allowed,setOf_and,setOf_forall]; refine (MeasurableSet.iInter fun i=> (measurable_fst (T.passes_meas y i)).inter (((T.hue_joint y i|>.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)) chosen_closed.measurableSet)).inter (MeasurableSet.iInter fun i=>?_)
 exact measurableSet_le (group.continuous_chord.measurable.comp ((measurable_pi_apply i).comp (adj_cont.measurable.comp measurable_swap))) measurable_const
lemma allow_g (a : HFrame s){U : Horiz s} {h : HFrame s}(p : T.allowed y U h): T.allowed y (adjust a U) (h*a⁻¹):= by
 refine ⟨fun i=>⟨ T.Pass_g y a (p.1 i).1, T.picked_g y a (p.1 i).2⟩,?_⟩; rw [adjust_seq,inv_mul_cancel_right]; exact p.2
lemma allow_center (i : Fin 5){U : Horiz s} {h : HFrame s}(p : T.allowed y U h): T.allowed y U ((fun _=> center i)*h):=by
 refine ⟨fun x=> ⟨(p.1 x).1, (p.1 x).2.shift (center_shade ..)⟩,?_⟩; rw [←adjust_seq,adjust_center]; exact p.2

def give (U : Horiz s)(x : Tri s)(i : Fin 5) := center i* T.sect (T.hue y U x)
def frame (U : Horiz s)(l : Law s) (x : Tri s) := T.give y U x (l x)
lemma give_meas (x : Tri s)(i : Fin 5) : Measurable fun U:Horiz s=> T.give y U x i:= measurable_const.mul (T.borel.comp (T.hue_joint y x))
lemma frame_meas (l : Law s) : Measurable fun U : Horiz s=> T.frame y U l:= measurable_pi_lambda _ fun i=> T.give_meas y i (l i)
lemma frame_pick (l : Law s)(U : Horiz s)(x : Tri s): Chosen (T.hue y U x) (T.frame y U l x):= (T.chosen _).shift (center_shade ..)
lemma give_cost {r : ℝ}{U : Horiz s}{x : Tri s} (i : Fin 5) (p : dist (T.hue y U x) magnet ≤ r)(h : r ≤ T.tube) : chord (T.give y U x i) (center i)≤ T.liftK*r:= by unfold give; nth_rw 2 [← mul_one (center i)]; rw [chord.left]; exact (T.near _ (p.trans h)).trans (mul_le_mul_of_nonneg_left p T.liftK_pos.le)
lemma give_inj (U : Horiz s)(x : Tri s): Injective (T.give y U x):=fun _ _ e=>center_injective (mul_right_cancel e)
lemma frame_inj (U : Horiz s) : Injective (T.frame y U):= fun _ _ e=> funext fun x=> T.give_inj y U x (congrFun e x)
end Atlas
end Sheet
end YM.CF.BPress
