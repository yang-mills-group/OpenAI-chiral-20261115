import YM.SU5.FiniteGaugeData.Seld.Sequel
import YM.SU5.FiniteGaugeData.Celeritas.Fluxa
/-!
# Use Weaves, but buy at inverse energy scale, extending real hinge.

 Centers ALWAYS for SHRINE half widths. Dir credit ν common in all axes.
 Philos(P) property of unweighted P on strict disjoint Eu plane windows in BOTH axes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
open Function Filter Metric Complex Set MeasureTheory Lattice Mist Celeritas Land OS OS.Semigroup
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder ContDiff
variable {K:Axis→Hilbert}(W:∀ a:Axis, OS.Semigroup (K a) a)(Ω:(i:Axis)→(K i).space) {H:Hilbert} {a:Axis}
variable (S:OS.Semigroup H a)(n m:ℕ) (Y:Shrine K)
def armor (n:ℕ)(x:Shrine K) : Shrine K := {
 t:=x.t, f:= fun a=> Cache (W a) n * x.f a * Cache (W a) n }
variable (a b: Axis){σ:Type}(L:List σ)(ν:σ→ℕ)(F:σ→ Shrine K)(x:σ→ E4)
local notation "B"=> W a
local notation "O"=>Ω a
local notation "Q"=>actO W F x a
-- each leap pays both sides
abbrev coast (i j:σ):= parabola (W a) (ν i+ν j) (OS.Semigroup.duration (Hi F x a i j))
def chalk (L:List σ):= inner ℂ (O) (TapeT (actO W F x a) (coast W a ν F x) L (O))
abbrev dressed(i:σ):= armor W (ν i) (F i)
local notation "G"=> dressed W ν F
local notation "C"=> Cache (W a)
-- footprints
lemma refuge : Seers (dressed W ν F) x a=Seers F x a := rfl
lemma coastB (i j:σ)(h:Seers F x a i j): (C) (ν i)* coast W a ν F x i j*(C) (ν j)= Leap W F x a i j:= by
 let S':=W a; let p:=Hi F x a i j; have he:0<p:=Real.toNNReal_pos.mpr (sub_pos.mpr h); let A:= parabola (B) (ν i+ν j) (OS.Semigroup.duration p); have hv:Commute A ((C) (ν j)):= ((gear (B) _ (dur.mpr he) _).symm.pow_right (ν j)); rw [show coast W a ν F x i j=A from rfl,mul_assoc,hv.eq,← mul_assoc]; refine Eq.trans ?_ (K_E (B) (ν i+ν j) p he); unfold Cache; rw [pow_add]
lemma acts_leg {a:Axis}(S:OS.Semigroup H a)(i:E4): leg S i= M S (SEP a i).val:=(laneslot ..).symm
lemma frost (i:σ): actO W (G) x a i=(C) (ν i) * actO W F x a i*(C) (ν i):=by
 let z:= (C) (ν i); let S':=W a; let u:= F i; let L:= leg (B) (x i); let R':=leg (B) (-(x i)); have he(i:E4):Commute z (leg (B) i):=by rw [acts_leg]; exact (tread ..).pow_left _
 change L*(z*_ * z)* R' = z*(L*_* R')*z; let y:=u.f a; change L*(z*y*z)*R'=z*(L*y*R')*z
 rw [show L*(z*y*z)= z*(L*y*z) from (by rw [←mul_assoc,←mul_assoc,(he _).eq.symm]; simp only [mul_assoc]; rfl)]; unfold R'; simp only [mul_assoc,(he (-x i)).eq] -- L notation mismatch. tune
lemma oK {a:Axis}(S:OS.Semigroup H a)(n:ℕ)(w:H)(p:saucer S w=w): Cache S n w=w:=by induction n with | zero=> simp [Cache] | succ n ih=> rw [Cache, pow_succ']; exact (congrArg (saucer S) ih).trans p
variable (p:L.Pairwise (Seers F x a))(g:saucer (W a) (Ω a)=Ω a)
lemma index_k (p:L.Pairwise (Seers F x a))(g:saucer (W a) (Ω a)=Ω a): chalk W Ω a ν (dressed W ν F) x L= chorus W Ω F x L a:=by
 let Q0:= Q; let Q':= actO W (G) x a; let cn:= coast W a ν F x; let Q''(t:List σ) := TapeT Q' cn t; let P:=TapeT Q0 (Leap W F x a)
 cases L with
 | nil=> rfl
 | cons i t=>
    have he: Q'' (i::t) (O)= C (ν i) (P (i::t) (O)):=by
       induction t generalizing i with
        | nil=> change Q' i (O) = C (ν i) (Q0 i (O)); rw [show Q' i=(C) (ν i)*Q0 i*(C) (ν i) from frost W a ν F x i]; exact congrArg (fun q=> C (ν i) (Q0 i q)) (oK (B) (ν i) (O) g)
        | cons j t ih=>
           let Z:= P (j::t) (O); obtain ⟨u,v⟩:= List.pairwise_cons.mp p; change Q' i (cn i j (Q'' (j::t) (O)))= _; rw [ih j v,show Q' i=(C) (ν i)*Q0 i*(C) (ν i) from frost W a ν F x i]; exact congrArg (fun z=> C (ν i) (Q0 i z)) (DFunLike.congr_fun (coastB W a ν F x i j (u j List.mem_cons_self)) Z)
    change inner ℂ (O) (Q'' (i::t) (O))= _; rw [he,← ContinuousLinearMap.adjoint_inner_left (C (ν i)),show (C (ν i)).adjoint=(C) (ν i) from (saucer_sym (B)).pow _, oK (B) _ (O) g]; rfl
#print axioms index_k
variable [DecidableEq σ](X:ℕ→σ→ Shrine K) (t:∀ i:σ, Weaves (fun n=>X n i) (F i))(r:σ)(e:∀ i:σ,i≠r→∀ n,X n i= F i)
include t
lemma coast_sub (i j:σ)(p:Seers F x a i j): Tendsto (fun n=>coast W a ν (X n) x i j) atTop (𝓝 (coast W a ν F x i j)):=by
 let h:= OS.Semigroup.duration; exact ((Bokeh (W a) (ν i+ν j) (h (Hi F x a i j)) (dur.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr p)))).continuousAt.tendsto).comp (((continuous_ofReal.comp continuous_subtype_val)|> (show Continuous h from ·) |>.continuousAt.tendsto).comp (hi_limit F X x a t i j))
include p e
local notation "F0" g:max=> TapeT (actO W g x a) (coast W a ν g x)
omit t p [DecidableEq σ] in
lemma settle (y:r∉L): ∀ n:ℕ,(F0 (X n)) L = (F0 F) L := by
 intro n; have he(i:σ)(m:i∈L):= e i (fun z=>y (z ▸ m)) n; apply Hike.same_tape; intro j m; unfold actO Plot; rw [he j m]; intro i m j y; unfold coast Hi startX endX; rw [he i m,he j y]
lemma follows (h:L.Nodup) : Wot (fun n=>(F0 (X n)) L) ((F0 F) L):=by
 cases L with
 | nil=> exact .still _
 | cons i L=> induction L generalizing i with
    | nil=> exact seating W F X x a t i -- spine Wot
    | cons j L ih =>
       obtain ⟨q,v⟩:=List.pairwise_cons.mp p; obtain ⟨H,w⟩:=List.nodup_cons.mp h
       let M:=j::L; let Cab(f:σ→ Shrine K):= coast W a ν f x i j; have he: Tendsto (fun n=>Cab (X n)) atTop (𝓝 (Cab F)):= coast_sub W a ν F x X t i j (q _ List.mem_cons_self); change Wot (fun n=> actO W (X n) x a i * (Cab (X n)* (F0 (X n)) M)) (actO W F x a i * (Cab F*((F0 F) M)))
       by_cases z:i=r
       · exact (seating W F X x a t i).body (he.mul (tendsto_const_nhds.congr (fun n=> (settle W a _ ν F x X r e (z ▸ H) n).symm)))
       exact ((ih j v w).shrew he).shrew (tendsto_const_nhds.congr fun n=> by unfold actO Plot; rw [e i z n])
lemma Chalk_lim (h:L.Nodup) : Tendsto (fun n=> chalk W Ω a ν (X n) x L) atTop (𝓝 (chalk W Ω a ν F x L)) := (follows W a L ν F x p X t r e h).funds ..
#print axioms Chalk_lim
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
