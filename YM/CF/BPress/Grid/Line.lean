import YM.CF.BPress.Grid.Cube
import YM.CF.BPress.Chord
/-! Plaquette discrepancy along any grid rectangle. Strides on refined lattice. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid
open Function Finset Lattice MeasureTheory
open scoped Topology Matrix BigOperators
abbrev WalkEdge (d : ℕ)(s:Side):= Space d s × Fin d
abbrev GaugeField (G:Gauge)(d : ℕ)(s:Side):= WalkEdge d s → G.El
variable {G:Gauge} {s : Side} {d : ℕ} (U : GaugeField G d s)

def line (x : Space d s)(i : Fin d) : ℕ → G.El
 | 0=>1
 | l+1=> line x i l * U (hop x i l,i)
@[simp] lemma line_zero (x : Space d s) (i) : line U x i 0=1:=rfl
lemma line_succ (x : Space d s)(i : Fin d)(k:ℕ): line U x i (k+1)=line U x i k * U (hop x i k,i):=rfl
@[simp] lemma line_one (x : Space d s)(i:Fin d):line U x i 1=U (x,i):=by rw [line_succ]; simp
lemma line_cat (x : Space d s)(i : Fin d)(k l:ℕ) : line U x i (k+l)= line U x i k * line U (hop x i k) i l:=by
 induction l with
 | zero=> simp
 | succ l ih=> rw [← Nat.add_assoc,line_succ,line_succ (x:=hop x i k),ih,hop_hop,mul_assoc] -- tune
lemma line_cont (x : Space d s)(i : Fin d)(k:ℕ) : Continuous fun U:GaugeField G d s=> line U x i k:=by
 induction k with|zero=> exact continuous_const | succ k ih=>exact ih.mul (continuous_apply (hop x i k,i))

def tension (U : GaugeField G d s)(r k : ℕ)(x : Space d s)(i j : Fin d) := chord (line U x i r*line U (hop x i r) j k) (line U x j k*line U (hop x j k) i r)
lemma tension_sym (r k : ℕ)(x : Space d s)(i j : Fin d) : tension U r k x i j=tension U k r x j i:= chord.comm ..
lemma tension_join (r l k : ℕ)(x : Space d s)(i j : Fin d) : tension U (r+l) k x i j ≤ tension U r k x i j + tension U l k (hop x i r) i j:=by
 unfold tension; rw [line_cat,line_cat,←hop_hop, ←hop_comm x i j]; -- draw middle path along r then j then l
 apply (chord.triangle _ (line U x i r*(line U (hop x i r) j k * line U (hop (hop x i r) j k) i l)) _).trans_eq; rw [mul_assoc, chord.left, ← mul_assoc _ (line U (hop x i r) j k), ←mul_assoc (line U x j k), chord.right,add_comm]

/-! Main use: global Flat on tangent input. BmoX use on cubes via extension per entity (only needs unit plaquettes; not thicker paths on that purchase). -/
structure Flat (U : GaugeField G d s)(m : ℝ) : Prop where
 positive : 0≤m
 flat (x : Space d s)(i j : Fin d): tension U 1 1 x i j≤m
variable {U m}
lemma Flat.rect {U:GaugeField G d s} {m:ℝ} (h : Flat U m)(i j : Fin d)(x : Space d s)(w v:ℕ): tension U w v x i j≤ w*v*m:=by
 have hp(i j:Fin d)(x:Space d s)(k:ℕ): tension U k 1 x i j≤ k*m:=by
    induction k generalizing x with
    | zero=> simp [tension]
    | succ k ih=> refine (tension_join U k 1 1 x i j).trans ((add_le_add (ih x) (h.flat ..)).trans_eq ?_); push_cast; ring
 induction w generalizing x with
 | zero=> simp [tension]
 | succ w ih=> refine (tension_join U w 1 v x i j).trans ((add_le_add (ih x) ((tension_sym U 1 v _ _ _).trans_le (hp ..))).trans_eq ?_); push_cast; ring
end YM.CF.BPress.Grid
