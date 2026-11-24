import YM.SU5.SatinWard.Resolution.Andesite
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.SatinWFixed.Andesite
open Function Filter MeasureTheory Set Complex Submodule SatinRegistration LimeWave
open Boundary Probe Mink OS OS.Semigroup SatinEdge.RealSheet Analysis
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder ContDiff Classical
variable {H:Hilbert}{ι:Type*}[Fintype ι](S:OS.Semigroup H timeAxis)(L:ι→ℝ→ℝ→ H.Op)(A:ι→ℕ→ℝ→ℝ→ H.Op) {ℓ:ℕ→ℝ} {z:ℕ}
local notation "Mark"=> (ι→ℂ)
variable (W:∀ i:ι,LimeWave.Post S ℓ (L i) (A i) z)
variable (Ω:H) (T:‖Ω‖=1) (δ:∀ e:E4, S.unit.translation e Ω=Ω) (th:∀ t, S.E t Ω=Ω)
local notation "B"=> expedition S L A W Ω T δ th
/- sum atmosphere. Keep all operator errands in this phase with genuine sums.S.WP -/
local notation "N"=> bands S
local notation "𝒟"=> radial S
open UnpadTicket Finset
variable [Nonempty ι]
def worthP (v:Mark) (l r:ℝ):H.Op:=∑ i:ι, v i • L i l r
def worthV (v:Mark) (n:ℕ)(l r:ℝ):H.Op:=∑ i:ι,v i • A i n l r
local notation "τ₀"=> worthP L
local notation "τ" k:max=> worthV A k
include W
lemma laminated_limit (x:Mark): Post S ℓ (τ₀ x) (τ x) z:=by
 let i₀:=Classical.arbitrary ι; refine ⟨fun i t=>?_,fun l r x y=>?_, (W i₀).pos,(W i₀).zero,(W i₀).threshold,?_⟩ -- shadow x
 · intro a b c d f g h q; unfold worthV sand; rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; rw [(W j).credits i t f g h q, Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
 · exact tendsto_finsetSum univ (fun i _=> ((W i).lim l r x y).const_smul _)
 · choose d C y f h using (fun i=> (W i).funds)
   let U:= 1+∑ i:ι,d i; have hu(i:ι):0 ≤ d i:= zero_le_one.trans (y i); have hA:1≤U:= le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=> hu i)); have hp(i:ι):d i ≤ U:= (Finset.single_le_sum (fun j _=> hu j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
   let c(i:ι):=‖x i‖* C i; refine ⟨U,∑ i,c i,hA,Finset.sum_nonneg (fun i _=>mul_nonneg (norm_nonneg _) (f i)),fun s v p q l r hl hr=>?_⟩; unfold worthV; rw [sum_mul]; apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro i _; rw [norm_smul]; refine (mul_le_mul_of_nonneg_left (h i s v p q l r hl hr) (norm_nonneg _)).trans (le_trans (b:=‖x i‖*(C i*U^s)) ?_ (le_of_eq ?_)); exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hu i) (hp i) s) (f i)) (norm_nonneg _); unfold c; ring
omit W
set_option maxHeartbeats 180000
set_option pp.universes false
lemma brochure {S:OS.Semigroup H timeAxis} {Zq:Carton S Mark} (T:ℝ→ℝ→H.Op)(A:ℕ→ℝ→ℝ→H.Op)(v:Mark)(W:Post S ℓ T A z)(V:∀ t:ℝ≥0,0<t→Zq.bar t v=T t t) : Zq.operator v= field S _ W.soundQ W.payQ := by
 change enact S (rawBlocks S (fun t=> Zq.bar t v)) (cold_paid S _ (Zq.price _) (Zq.coherent _)) = enact S (rawBlocks S (LimeWave.image T)) (cold_paid S _ W.payQ W.soundQ); congr 1; unfold rawBlocks; congr 1; ext1 m; funext n; unfold coldAt; dsimp only; rw [V 1 zero_lt_one]
open Carton
set_option maxHeartbeats 420000
variable {Y: ℕ→ radial S}{y:radial S}
include W
lemma concert (p:(bands S).Approaches atTop Y y) (v:MarkType Mark): (bands S).Approaches atTop (fun i=> warm S (montage ℓ (τ v.1) i) v.2 (Y i)) ((B).operator v.1 v.2 y) := by
 rw [brochure (τ₀ v.1) (τ v.1) v.1 (laminated_limit S L A W v.1) (fun t e=> at_lights S L A W Ω T δ th _ e _)]
 exact Post.warmth (laminated_limit S L A W v.1) _ p
abbrev letterW (n:ℕ) (v:MarkType Mark): radial S→ₗ[ℂ]radial S:=warm S (montage ℓ (worthV A v.1) n) v.2
lemma wordsOf (p:(bands S).Approaches atTop Y y)(v:MarkWords Mark): (bands S).Approaches atTop (fun n:ℕ=> (v.map (letterW (ℓ:=ℓ) S A n)).prod (Y n)) ((B).realWork v y) := by
 induction v with
 | nil=> exact p
 | cons a v ih=> exact concert S L A W Ω T δ th ih a
#print axioms wordsOf
end YM.SatinWFixed.Andesite
