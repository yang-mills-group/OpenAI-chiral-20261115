import GaugeFieldConstruction.Ozar
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Rio
variable {n:Side}{I:Type}[Fintype I][LinearOrder I]
variable (p:BudgetPoint)(σ:I→ Seat n)(q h:ℝ)(k:ℕ)(b:ℕ)(a η ℓ Ω:ℝ)(X:Origin n)(y:Seat n)(A B:Rio I n)
-- All debit ops are parameterized so later cert premise can be along ONLY actual recursion.
abbrev advanceC (d η:ℝ):= d*4*η⁻¹
abbrev stolon (b:ℕ)(Ω η d:ℝ):= d * (2*(Cube_M b*Ω) + advanceC d η)
local notation "Υ" => advanceC ℓ η
local notation "κ"=>Paw b a η
local notation "T"=> Band b a η
local notation "sumQ"=> SumAll b a η X
local notation "Ψ"=> stolon b Ω η ℓ
local notation "Λ"=> Weighted p σ q h k
structure LevelPass (y:Seat n)(V W: CashI I n)(L:List (Site (More n))) :Prop where
 pure(i:Site (More n)): Paw b a η W L i ≤ ℓ*windPulse b y i
 mixed(i:Site (More n)): Band b a η W L i ≤ ℓ * (2*windPulse b y i* (Cube_M b*Ω)+ 4*η⁻¹*(SumAll b a η X V (y::L) i - SumAll b a η X V L i))
def markΩ (P:List (Site (More n)))(i:Site (More n)):= ℓ*(P.map (fun j=>windPulse b j i)).sum
def Adv_L (y:Seat n)(A B:Rio I n) :Prop:=∀ V, Weighted p σ q h k A V →∀ L:List (Site (More n)),Scales b a η L→ (∀ i, sumQ V (y::L) i ≤ Ω) → ∃ W, Weighted p σ q h k B W ∧ LevelPass (I:=I) b a η ℓ Ω X y V W L
-- $fold tail ⇒ first$
inductive WarpL : List (Site (More n)) → Rio I n → Prop where
| empty : WarpL [] 0
| step {V W:Rio I n}{s: Seat n}{l:List (Seat n)}: WarpL l V → Adv_L p σ q h k b a η ℓ Ω X s V W → WarpL (l ++ [s]) (V+W)
-- here step at right end! easier use $append [s]$ and chronological forward.; In Rec of $head process$ L1 recursion direction: WarpL (L ++ [s]) -> ih L Future=s::F, total trajectory names = L++[s]++F. good.
local notation "ΣL"=> WarpL p σ q h k b a η ℓ Ω X
variable (F L:List (Seat n)) (V:Rio I n) (Φ Z:ℝ) (ΩL: Z+ℓ*Φ+(advanceC ℓ η*Z+stolon b Ω η ℓ*Φ)≤Ω)
variable (ht:0≤a) (hL:0≤ℓ)(f:0<η)(t:advanceC ℓ η≤1)(m0:0≤Ω) (Q:0 ≤ X)(QS:∀ A i y,X A i≤ X (y::A) i)
include hL m0 f
lemma Sl_Pos : 0≤ Ψ:= mul_nonneg hL (add_nonneg (mul_nonneg zero_le_two (mul_nonneg (cube_M_pos _|>.le) m0)) (mul_nonneg (mul_nonneg hL (by norm_num)) (inv_nonneg.mpr f.le)))
omit f m0 hL
lemma SeasonDown (L:List (Seat n)){α:List (Seat n)}(p:Scales b a η (L++α)):Scales b a η α:=by
 induction L with | nil=> exact p | cons i L ih=> exact ih (Scales.drop i p)
include Q QS
lemma low_tide (F L:List (Seat n))(i:Seat n): X L i≤ X (F++L) i:=by
 induction F with
 | nil=> exact le_refl _
 | cons i F ih=>exact ih.trans (QS _ _ _)
include hL m0 f t ΩL
lemma pressure (w:ΣL L V)(pΩ:∀ y,X (L++F) y≤ Z)(kγ:Scales b a η (L++F))(qΓ:crewFlow b L Φ): ∃ W:CashI I n, Weighted p σ q h k V W ∧∀ i:Seat n, κ W F i≤ markΩ b ℓ L i∧ T W F i+ Υ*(X F i+κ W F i) ≤ Υ * X (L++F) i + Ψ*(L.map fun j=>windPulse b j i).sum:=by
 induction w generalizing F with
 | empty=>
    refine ⟨0, Weighted.free,fun i=>?_⟩; rw [CashI.planted,CashI.V0]; simp [markΩ]
 | @step x y S l h₀ e ih=>
    have g0: (l ++ [S]) ++ F=l++(S::F):=List.append_assoc .. -- tune
    rw [g0] at pΩ kγ
    have hp:Scales b a η F:= Scales.drop S (SeasonDown b a η l kγ)
    have pΦ :crewFlow b l Φ:=by
       intro i; have hx:=qΓ i; rw [List.map_append,List.sum_append] at hx
       exact (le_add_of_nonneg_right (by simpa using pulse_pos b S i |>.le)).trans hx
    obtain ⟨V,u,cx⟩:=ih (S::F) pΩ kγ pΦ
    have ug:∀ i, (SumAll b a η X V) (S::F) i ≤ Ω:=by
       intro i; have he: X (S::F) i≤Z:= (low_tide X Q QS l _ i).trans (pΩ i)
       have hc:0 ≤ X (S::F) i:= Q _ _; obtain ⟨x,q,Q⟩:=u.estate (a:=a) (d:=b) f.le (S::F) i
       have hx':=mul_nonneg (show 0≤Υ from (by unfold advanceC; positivity)) (add_nonneg hc x)
       obtain ⟨A,B⟩:=cx i
       refine le_trans ?_ ΩL; change X (S::F) i+ κ V (S::F) i + T V (S::F) i ≤ _
       have ht':= pΦ i; refine add_le_add (add_le_add he (A.trans (mul_le_mul_of_nonneg_left ht' hL))) ((le_add_of_nonneg_right hx').trans (B.trans (add_le_add (mul_le_mul_of_nonneg_left (pΩ i) (by unfold advanceC; positivity)) (mul_le_mul_of_nonneg_left ht' (Sl_Pos b η ℓ Ω hL f m0))))) -- tune S:: etc
    obtain ⟨W,m,H⟩:= e V u F hp ug
    refine ⟨V+W,u.merge m,fun i=>?_⟩
    have ht : 0≤Υ:=by unfold advanceC; positivity
    obtain ⟨_,_,kH⟩:=u.estate (a:=a) (d:=b) f.le F i
    have hB := (kH S).1
    have hΓ := mul_le_mul_of_nonneg_left (sub_nonneg.mpr (kH S).2) ht
    have hY := mul_le_mul_of_nonneg_right t (sub_nonneg.mpr (kH S).2)
    have hC := H.mixed i; have hP:= H.pure i; have pI:=cx i
    rw [CashI.Badd,CashI.Padd,g0,List.map_append,List.sum_append]; unfold SumAll at hC
    let Y':= Ψ
    simp only [Pi.add_apply,List.map_singleton,List.sum_singleton] at * -- tune syntax macro, affects pI not unfolded.markΩ.
    constructor
    · unfold markΩ at *; rw [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]; linarith only [hP,hB,pI.1]
    rcases pI with ⟨h1,h₂⟩; have e':= mul_le_mul_of_nonneg_left hP ht; unfold stolon advanceC at *; linarith only [hC,h₂,hY,e']
end Rio
end YM.CF.Scree.Ing
end
