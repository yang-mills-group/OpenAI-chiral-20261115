import YM.SU5.Reconstruction.Trap.Transits
import YM.SU5.Reconstruction.Trap.Mantle
/-!
# Restore operators from singular light-powers
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Multiplier
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open Complex
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {H D:Hilbert}
namespace Chirp
variable (P:PVM H X) (Q:PVM D Y) (L:X→ℝ) (M:Y→ℝ)
variable (m: Measurable L)(n:Measurable M)(p:0≤L)(q:0≤M) -- pointwise
local notation "Z"=> P.region (onboard L)
local notation "E"=> Q.region (onboard M)
include m
lemma pays_logs (u:ℝ): concern P (Real.log ∘ L) u=singers P L u:= by
 apply (current P (Real.log ∘ L) (Real.measurable_log.comp m) u).single; convert sings P L m u using 1; funext x; unfold sound sing; dsimp; congr 1; ring
lemma powered (t:ℝ) : star (singers P L t)=singers P L (-t):=by
 rw [←pays_logs P L m,←pays_logs P L m]; exact replay P _ (Real.measurable_log.comp m) t
include p
lemma full_star (t:ℝ): singers P L t= starry P L t+(1-P.region (onboard L)):= by
 apply Registers.single (sings P L m t); have e:=(payStar P L m t).add ((Registers.one P).sub (Registers.box P (arc L m))); refine e.agrees (sings P L m t|>.price) (fun x=> Eventually.of_forall fun y=>?_)
 by_cases k:y∈onboard L
 · simp [indicator_of_mem k]
 have hp:L y=0:= le_antisymm (le_of_not_gt k) (p y)
 simp [indicator_of_notMem k,hp]
lemma onDeck {F:ℝ→ℂ}(e:Tag F)(u:H.Op)(h:Registers P (F ∘ Real.exp ∘ Real.log ∘ L) u) : Registers P (F ∘ L) (Z*u+(F 0) • (1-Z)):= by
 have t := (h.mask (arc L m) (h.comm (arc L m))).add (((Registers.one P).sub (Registers.box P (arc L m))).scale (F 0)); refine t.agrees (e.port _ m) (fun x=> Eventually.of_forall fun y=>?_); by_cases k:y∈ onboard L
 · have a: 0<L y:=k; simp [k,Real.exp_log a]
 have hp: L y=0:=le_antisymm (le_of_not_gt k) (p y); simp [k,hp]
variable (A:H→L[ℂ]D)
include n p q
lemma recover (f:ℝ→ℂ)(g:Tag f)(x:A.comp Z= (E).comp A)(y:∀ t, A.comp (singers P L t)=(singers Q M t).comp A): A.comp (order P (f ∘ L))=(order Q (f ∘ M)).comp A := by
 let a:= Real.log ∘ L; let b:=Real.log ∘ M
 let d:= f ∘ Real.exp; let z:=order P (d ∘ a); let w:=order Q (d ∘ b)
 have hd : Tag d:= g.port _ Real.continuous_exp.measurable
 have h1:Measurable a:= by unfold a; fun_prop
 have h2:Measurable b:= by unfold b; fun_prop
 have e:A.comp z=w.comp A:= ballot _ _ _ _ _ h1 h2 (fun t=>by unfold a b; simp only [pays_logs P L m,pays_logs Q M n]; exact y t) _ hd
 rw [←takes_order P (onDeck P L m p g z (order_reads P (hd.port a h1))), ← takes_order Q (onDeck Q M n q g w (order_reads Q (hd.port b h2)))]
 rw [ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_sub,ContinuousLinearMap.sub_comp,x]; congr 1 -- assoc
 change A.comp ((Z).comp z)= ((E).comp w).comp A; rw [← ContinuousLinearMap.comp_assoc,x,ContinuousLinearMap.comp_assoc,e, ←ContinuousLinearMap.comp_assoc]
end Chirp
end YM.Multiplier
