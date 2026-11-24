import YM.SU5.FiniteGaugeData.Seld.Equity
import YM.SU5.FiniteGaugeData.Seld.Raft
/-!
# For the POIN reconstruction criteria: order-sensitive products (value at sh0rt sentence etc), real Mink vacuum calculus.

Early formats.Tune wrappers to reduce import dependencies. Film compared to WP formulas in Bridge. COMP order last slot closest Ω on right.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Function Filter Metric Complex MeasureTheory Set OS OS.Semigroup
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {α:Type*}{R:Type} [Monoid R] (A:α→R)(B:α→α→R) (i j:α) (L:List α)
def clip (i:α): List α→ R | []=>1 | j::_=> B i j
def Film : List α→ R | []=>1 | i::L=> A i*(clip B i L*Film L)
@[simp] lemma solitary : Film A B [i]=A i:=by simp [Film,clip]
@[simp] lemma quiet : Film A B []=1:=rfl
lemma Film_step : Film A B (i::L)= A i*(clip B i L* Film A B L):=rfl
lemma Film_map {X:Type*}(e:X→α)(x: List X) : Film A B (x.map e)=Film (A ∘ e) (fun i j=>B (e i) (e j)) x:=by
 induction x with
 | nil=> rfl
 | cons x X ih=> rw [List.map_cons,Film_step,Film_step, ih]; cases X <;> rfl
-- Fin n tickets. s1 cuts even at base n=1.Let gap support all orientations.
variable {n:ℕ}
abbrev Each (n:ℕ):List (Fin n):= List.finRange n
abbrev Bin (n:ℕ)(α:Type*):= Fin n → Fin n → α
abbrev Rail (A:Fin n→R)(B:Bin n R):=Film A B (Each n)
abbrev rump {R:Type*} (J:Bin (n+1) R):Bin n R := fun i j=> J i.succ j.succ
-- no `[Zero Fin n]` requirement.`Film_gap`
def s1 (n:ℕ) (B:Bin (n+1) R):R:= clip B 0 ((Each n).map Fin.succ)
lemma s1P (B:Bin (0+1) R) : s1 0 B=1:=rfl
lemma s1S (B:Bin (n+1+1) R) : s1 (n+1) B=B 0 (Fin.succ (0:Fin (n+1))):=by unfold s1 Each; rw [List.finRange_succ]; rfl
lemma Rail_step {n:ℕ}(A:Fin (n+1)→R)(B:Bin (n+1) R): Rail A B= A 0*s1 n B * Rail (Fin.tail A) (rump B):=by unfold Rail Each; rw [List.finRange_succ,Film_step, Film_map,mul_assoc]; rfl
-- mapping Bank with bridges. 
variable {H:Hilbert}{n:ℕ}{a:Axis}(S:OS.Semigroup H a)(y:H)
local notation "D"=> Bench S
local notation "Ω"=> M S
open Boundary Probe Fin
-- `geoduction` telescopic conjugation in position pricing. Middle gaps $T$ commute M in Wick but proof generic.Noncomm.
variable {σ:Type}(G:σ→H.Op)(J₁:σ→σ→H.Op)(x:σ→ E4)
local notation "A'"=> fun i=>optx S (G i) (x i)
local notation "G'"=>fun i j=> Ω (-(x i))* J₁ i j* Ω (x j) -- orientation later want positive ∆. algebra telescope
variable (p:∀ x:E4, S.unit.translation x y=y)
include p
lemma Into (i:σ)(L:List σ): Film (fun i=> optx S (G i) (x i)) J₁ (i::L) y= Ω (x i) (Film G (G') (i::L) y):=by
 induction L generalizing i with
 | nil=> rw [solitary,solitary]; exact congrArg (fun u:H=>Ω (x i) (G i u)) (p (-(x i)))
 | cons j L ih=> change optx S (G i) (x i) (J₁ i j (Film (A') J₁ (j::L) y))= _; rw [ih]; rfl
lemma twists (L:List σ): inner ℂ y (Film (fun i=> optx S (G i) (x i)) J₁ L y) = inner ℂ y (Film G (G') L y):= by cases L with
 | nil=> rfl
 | cons i L=> rw [Into S y G J₁ x p,tboth,p] -- p mismatch
lemma baroque (J:σ→σ→H.Op)(g:∀ p:E4,∀ i j:σ,Commute (Ω p) (J i j))(L:List σ): inner ℂ y (Film (fun i=> optx S (G i) (x i)) J L y)=inner ℂ y (Film G (fun i j=> J i j * Ω (x j-x i)) L y):=by
 rw [twists S y G J x p]; let A(i j:σ):= Ω (-x i)*J i j*Ω (x j); have he(i j:σ): A i j= _:=congrArg (·* Ω (x j)) (g (-x i) i j).eq -- define
 change inner ℂ _ (Film G A L y)=_; rw [show A=(fun i j=> _) from funext fun i=> funext fun j=> ?_] -- infer placeholder
 rw [he,mul_assoc,tgo,add_comm,←sub_eq_add_neg]
#print axioms twists
#print axioms Rail_step
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
