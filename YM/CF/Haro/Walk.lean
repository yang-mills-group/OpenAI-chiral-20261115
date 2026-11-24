import YM.CF.Haro.Celtic
import YM.CF.Yaw.Reef
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.Frobenius Kronecker MatrixOrder Classical

open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(j m:ℕ)(e:Even j)(h:2 ≤ j)
variable (G:Ratio c f)(ho:Odd G.count.val)
open Branch Laic
variable {t:ℝ}(Y: cro G t)(W: Meter TailB G t)(V: Meter Grave G t)
open Skye Precision
open Jet Pressure
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}
-- dyadic leagues for poly rate over M.Path canonical. pay k depth.
open Rill
variable {n k:ℕ}{K a b d:ℝ}
def reelQ (x:Seat c)(W:Lattice.Walk):= (visits x W).toFinset
lemma verseH (x:Seat c)(W T:Lattice.Walk): reelQ x (W++T)= reelQ x W ∪ reelQ (stop x W) T:=by
 induction W generalizing x with
 | nil=> rw [List.nil_append]; change _= reelQ x [] ∪ reelQ x T; rw [union_eq_right.mpr]; simp [reelQ]; cases T<;> simp [visits]
 | cons i W ih=> rw [List.cons_append]; unfold reelQ; simp only [Lattice.visits,List.toFinset_cons,stop]; unfold reelQ at ih; rw [ih]; simp
include n
lemma wand (g:Rill.Wind a (·*·) n K)(p:Rill.Wind a (fun i _=> i⁻¹) n K)(hX:1 ≤ K)(ht:0 ≤ b)(U:E→ Pane c)(x:Seat c)(W:Lattice.Walk)(k:ℕ)(hz:W.length ≤ 2^k)(hu: Rill.Cash (k+3) b K ≤ a)(hv:∀ i:Pressure.Bond (More c), ends i⊆reelQ x W→ Rill.Tender (fun y=>U y i) z b n): Rill.Tender (fun y=> travel (U y) x W) z (Rill.Cash (k+3) b K) n:=by
 induction k generalizing W x with
 | zero=> exact Yaw.travellers n le_rfl hX g p U 1 W x hz hu ht (fun i hp=>hv _ hp)
 | succ k ih=>
    let T:= W.take (2^k); let Z:=W.drop (2^k); have hx0:T++Z=W:=List.take_append_drop ..; let y:=stop x T; have hp:T.length≤2^k:=List.length_take_le ..; have hy:Z.length≤ 2^k:=by unfold Z; rw [List.length_drop]; rw [pow_succ] at hz; omega
    have h':= (Rill.take_k hX ht (show k+3≤k+1+3 by omega)).trans hu; have he:reelQ x W=reelQ x T∪reelQ y Z:=by nth_rw 1 [←hx0]; exact verseH ..
    have hm:=g.duty h' (ih x T hp h' (fun i p=>hv i (he ▸ p.trans subset_union_left))) (ih y Z hy h' (fun i p=>hv i (he ▸ p.trans subset_union_right)))
    rw [Nat.add_right_comm,← Rill.put_c]; apply hm.same (Eventually.of_forall fun v=> congrArg SU.group.mat (show travel (U v) x T* travel (U v) y Z= _ from ?_)); unfold y; rw [←travel_append,hx0]
omit n
lemma roller (x: Seat c)(T: Lattice.Walk)(y:Seat c)(v:y∈ reelQ x T): separation x y + separation y (stop x T) ≤ T.length:=by
 induction T generalizing x with
 | nil=> simp [stop,(show y=x from by simpa [reelQ,visits] using v)]
 | cons i T ih=>
    rcases List.mem_cons.mp (List.mem_toFinset.mp v) with rfl|v
    · simpa [reelQ] using Work.E04.stop_separation_le y (i::T)
    have hv:=ih _ (List.mem_toFinset.mpr v); rw [stop,List.length_cons]; have hp:= separation_triangle x (x+i.vec) y; have hu:separation x (x+i.vec) ≤ 1:=Work.E04.stop_separation_le x [i]; omega
lemma visit_p (x y o:Seat c)(d':ℕ)(hp:separation o x≤d')(ht:separation o y≤d'): reelQ x (shiftH x y)⊆ halo (5*d') {o}:=by -- trash a param
 intro i g; apply halo_spec.mpr; refine ⟨o,mem_singleton_self _,?_ ⟩; have he:=roller _ _ _ g; rw [stopH] at he; have hx:= short x y; have hv:= separation_triangle x o y; rw [separation_comm x o] at hv; have ht':=separation_triangle o y i; rw [separation_comm y] at ht'; have hu:= separation_triangle o x i; omega
-- Tensors under gauge; use same stipend l+n. Fro
variable {q:Seat f→SU.E}
include n
lemma tapG (g:Rill.Wind a (·*·) n K)(hX:1 ≤ K)(U:E→ Pane f)(q:Seat f→SU.E)(i:Bond (More f))(hv:Rill.Tender (fun y=> U y i) z b n)(hp:K*b≤a): Rill.Tender (fun y=> Lattice.gauge q (U y) i) z (K*(K*b)) n:=by
 have h:b≤K*b:=le_mul_of_one_le_left hv.price hX
 exact g.duty hp (g.duty (h.trans hp) ((Shake.holds (SU.group.mat (q i.1))).bag hv.price) hv) ((Shake.holds (SU.group.mat ((q (i.1+step i.2))⁻¹))).bag (hv.price.trans h)) -- tune
end YM.CF.Haro
