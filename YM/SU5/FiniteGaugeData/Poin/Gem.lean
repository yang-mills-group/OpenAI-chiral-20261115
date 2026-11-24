import YM.SU5.FiniteGaugeData.Poin.Andine
import YM.SU5.FiniteGaugeData.Poin.Velvet
/-! # MULTIVIEW tilt estimates to generate separated Eu readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set Mink Mink.General Mink.Lorentz Real Flute MeasureTheory OS OS.Semigroup
open scoped Topology BigOperators NNReal
local notation "a"=>timeAxis
variable {H:Hilbert}{n:ℕ}{ι:Type}(T:Canopy H ι)(S:OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ x:E4,M S x Ω.val=Ω.val)
variable (s:SO)(x:Points n)
namespace Gem
open scoped ENNReal InnerProductSpace ComplexOrder
variable {ι: Type}{K:Axis→Hilbert} (W:∀ a':Axis,OS.Semigroup (K a') a') (G:Canopy (K timeAxis) ι)
-- passports for all views (no separate Eu/W labels without bridging).
structure Tribe where
 legato (i:Axis)(x:ι) : colorP (G.P x).amount→L[ℂ] (K i).Op
 meets (i:ι) : legato timeAxis i=G.flash i
variable (A:Tribe G)(t:Axis→ ℝ≥0) (w:G.Chip) (u:Axis)
def useB := A.legato u w.fst w.snd
@[simp] lemma usea : useB G A w a=G.dep w:=by unfold useB; rw [A.meets]; rfl
abbrev Node(n:ℕ): Type:= Bool ⊕ Fin n
def costR (f:Fin n→ G.Chip) : Node n→ℕ:= Sum.elim (fun _=>0) (fun i=> G.grade (f i))
def cam (g:Fin n→ G.Chip) (x:Points n) (j:Node n):(K u).Op:= Sum.elim (fun _=>1) (fun i=> coreSp (W u) (x i) (useB G A (g i) u)) j
def spire (x:Points n): Node n→ℝ:= Sum.elim (fun b=> if b then ↑(t u) else -(t u:ℝ)) (fun j=>x j u)
structure Cartouche where
 count : ℕ
 points : Points count
 chips : Fin count → G.Chip
 roll (i:Axis) : Canopy.Pear count
 perm (i:Axis) : (roll i).Perm (Each count)
 behind (i:Axis): Sau (spire t i points) (( Sum.inl false):: (roll i).map Sum.inr ++ [Sum.inl true]) -- parens?
-- paid. P *strict.*
variable (M: Cartouche G t)
abbrev pipe (i:Axis): List (Node M.count):= Sum.inl false :: (M.roll i).map Sum.inr ++ [Sum.inl true]
def GapK {αT: Type}{b:Axis}{H:Hilbert}(S:OS.Semigroup H b) (c:αT→ℝ)(ν:αT→ℕ)(i j:αT):= Par S (ν i+ν j) (c j-c i).toNNReal
-- generic any axis fixing αT.S uses time → use general {b,μ}
local notation "A₀" i:max=> cam W G A i M.chips M.points -- ordering arguments cam declared A t w u.G.T?
def traceB : (K u).Op:= Film (A₀ u) (GapK (W u) (spire t u M.points) (costR G M.chips)) (pipe G t M u)
abbrev Bag := List (ℂ × Cartouche G t)
def oars (B: Bag G t) : (K u).Op := (B.map (fun x=> x.1 • traceB W G A t u x.2)).sum
-- no nonphysical orientation.Radius receipts
private lemma domino {H:Hilbert}{a':Axis}(S:OS.Semigroup H a')(Q:H.Op) (p:Commute (saucer S) Q) (z:∀ t,Commute (S.E t) Q) (f:ℝ≥0)(h:0<f)(n:ℕ): Commute (Par S n f) Q:=by ext1 x; apply cache_I S n; have V:Cache S n*Q=Q*Cache S n:=p.pow_left n; exact DFunLike.congr_fun (show Cache S n*(Par S n f*Q)= Cache S n*(Q*Par S n f) from (by rw [←mul_assoc, ←mul_assoc,V,mul_assoc Q, P_Heq S f n h]; exact z f)) x
abbrev upTime:= W timeAxis
variable (Q:(K timeAxis).Op)(p:Commute (saucer (W timeAxis)) Q)(v:∀ i, Commute ((W timeAxis).E i) Q)(q:∀ i, Commute ((W timeAxis).U i) Q)(f:∀ w, Commute (G.dep w) Q)
include p v q f
local notation "ℓ"=>W timeAxis
lemma camel : Commute (traceB W G A t a M) Q:=by
 let c:=spire t a M.points; let Z:= A₀ a; let C':=GapK (ℓ) c (costR G M.chips); have he(i:Node M.count): Commute (Z i) Q:=by
    cases i with | inl u=> exact Commute.one_left Q | inr y=>
       let z:= useB G A (M.chips y) a; let t:= SEP a (M.points y); have ht : Commute z Q:=by unfold z; rw [usea]; exact f _
       change Commute (Seld.M (ℓ) t.val *z * Seld.M ℓ (-t.val)) Q
       rw [laneslot _ t, show -t.val=(-t:Cross a).val from rfl, laneslot]; exact ((q t).mul_left ht).mul_left (q _)
 suffices hv:∀ L,Sau c L→ Commute (Film Z C' L) Q from hv _ (M.behind a)
 intro L; induction L with
 | nil=> exact fun _=> Commute.one_left _
 | cons i L ih=> intro y; rw [Film_step]; refine (he i).mul_left ((show Commute (clip C' i L) Q from ?_).mul_left (ih (List.pairwise_cons.mp y).2)); cases L with | nil=> exact Commute.one_left _ | cons j L=> exact domino (W a) Q p v _ (Real.toNNReal_pos.mpr (sub_pos.mpr ((List.pairwise_cons.mp y).1 _ List.mem_cons_self))) _
lemma hook (B:Bag G t): Commute (oars W G A t a B) Q:= by
 induction B with | nil=> exact Commute.zero_left _ | cons b g ih => exact ((camel W G A t b.2 Q p v q f).smul_left b.1 |>.add_left ih)
#print axioms hook
omit p v q f
lemma PricesRoll : ProofOrder M.points u (M.roll u):=by
 have he:=M.behind u; let L:List (Node M.count):=(M.roll u).map Sum.inr; have hp:= List.pairwise_map.mp ((List.pairwise_append.mp (List.pairwise_cons.mp (show Sau (spire t u M.points) (Sum.inl false::(L++[Sum.inl true])) from he)).2).1); exact hp -- type inference of R
lemma footprint (i:Fin M.count): M.points i u ∈ Set.Ioo (-(t u:ℝ)) ((t u:ℝ)):=by
 let J:= spire t u M.points; let D:List (Node M.count):= (M.roll u).map Sum.inr; have he: Sau J (Sum.inl false::(D++[Sum.inl true])):= M.behind u; obtain ⟨p,q⟩:= List.pairwise_cons.mp he; have H: Sum.inr i ∈ D:= List.mem_map_of_mem ((M.perm u).mem_iff.mpr (List.mem_finRange i)); exact ⟨p _ (List.mem_append.mpr (Or.inl H)), (List.pairwise_append.mp q).2.2 _ H _ List.mem_cons_self⟩
#print axioms footprint
end Gem
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
