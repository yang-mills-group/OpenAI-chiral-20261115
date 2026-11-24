import YM.CF.BPress.Lily.Flowers
import YM.CF.BPress.Hazel.Seers
/-! § VolumeB-phase eq:B-Jrep. Letters of species one. Explicit row convention and site localization, not diagonal approximation. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Lily
open Function MeasureTheory Filter NormedSpace Finset Fock Lattice Cube Lat Spin Spin.Paint SU SU.Pair Chalk Pf Pressure Branch Bias Dial Nacre Tulip
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{C: Op I}
open Meadow Grid Wealth Locale Tunnel Bands Branch Hazel Chrono Hazel.Letter Spin.Stride
variable {B:BandWidth}{N:Side}(X:Bands (More N) B)(A: Letter X){W:Rental}{R:Hangar (More N)}(K U:Paint (More N))
local notation "Ω"=> vacuum (Single N)
def vacancy := univ.filter (fun x:Site N=> ¬ Welkin X (node x))
-- on accepted data use only these values for Mark look and comparison rotations. At this point orientation fixed by Label.
def interest : Paint (More N):= fun x=> if p:Welkin X x then A.brush (citizen X x p) 2 x else 1
lemma invoice {i:X.Index}(x:Site (More N))(p:x∈ X.band i): interest X A x=A.brush i 2 x:=by rw [interest,dif_pos (show Welkin X x from ⟨i,p⟩), citizen_t X p]
lemma principal (h:A.Tint) : MatPlan (interest X A):=by intro x; unfold interest; split; exact (h.clock _).scheme _ _; exact ⟨Matrix.transpose_one,(unitary _).one_mem,Matrix.det_one⟩
abbrev selectP (x:Site N)(S:Support N): Bool:= decide (x∈ S)
lemma woven_as (P:Support N)(x:Site N): (woven K P).val x=heading x (K (node x)) (selectP x P):=by unfold woven merge pal selectP heading ascent; dsimp only; by_cases h:x∈P <;> simp [h]; rfl; rfl -- tune
lemma w0P {x:Site N} (P:Support N)(v:x∈P)(h:MatPlan K): acts ((woven K P).val x) Ω= punctual x:=by rw [woven_as]; unfold heading ascent selectP; rw [if_pos (decide_eq_true v)]; exact markHere x (h (node x))
lemma p_cuts (P:Support N) (x:Site N)(p:x∉P): (woven K P).val x=bloom x (K (node x)):=by rw [woven_as]; simp only [selectP,p, decide_false,heading,ascent, Bool.false_eq_true, ↓reduceIte,one_mul]

structure Vase (A B: Paint (More N))(S T W:Support N):Prop where
 t:MatPlan A
 t':MatPlan B
 dis:Disjoint S W -- reading Pbits denote clamped state. W changes don't consult reader at P bits
 match':∀ x∉W,(x∈S ↔ x∈T) ∧ (x ∉ S → A (node x)= B (node x))
-- factors are on bra side
abbrev cardP(K U:Paint (More N))(P:Support N)(x:Site N): FC (Single N):= joker x (K (node x)) (U (node x)) (selectP x P)
def byJ (P:Support N): Chalk.PanelA N:=⟨cardP K U P, fun i=> joker_even ..⟩
variable {K U} {S T' V:Support N}(p:Vase K U S T' V)
include p
lemma redeem (u: Wave (Single N)): inner ℂ (braC (Locks S true) (Locks S false) (coupling K)) (acts (tomes V (byJ K U T')) u)=inner ℂ (braC (Locks T' true) (Locks T' false) (coupling U)) u:=by
 let B:=byJ K U T'; let K0:= woven K S; let A: PanelA N:= ⟨fun i=>star (B.val i), fun i=>(B.property i).contr⟩; let J:=pal V A; have ht:star (tomes V B)=tomes univ J:=by rw [star_b]; rw [show J=pal V A from rfl,Chalk.rent,univ_inter] -- tune pal ambiguity
 rw [woven_unit,woven_unit,← act_inner,ht,← act_mul,←merge_prod]; apply congrArg (fun w=>inner ℂ w u); apply Chalk.reading; intro i _; let P:=p.match' i; by_cases h:i∈V
 · have he: i∉S:=fun a=> disjoint_left.mp p.dis a h; change acts (J.val i*((woven K S).val i)) _ = _; rw [show J.val i=star (cardP K U T' i) from if_pos h,p_cuts _ _ _ he, woven_as]; exact restoration _ _ _ _ (p.t _) -- tune binder
 unfold merge; dsimp only [Pi.mul_apply]; rw [show J.val i=1 from if_neg h,one_mul]; by_cases g:i ∈ S; rw [w0P _ _ g p.t,w0P _ _ ((P h).1.mp g) p.t']; rw [p_cuts _ _ _ g,p_cuts _ _ _ (mt (P h).1.mpr g), (P h).2 g] -- tune rw target
omit p
lemma valid_vase {K:Tiling (More N)}{S:Seal (SiteX X R)}{U:Micro (More N)}{g h q m d:ℝ}{p:Grip X W R S A U g h d}(t: Hazel.Stopped A K p q m) : Vase (Kactual W R S A K U 2) (interest X A) (Picks X R S) (vacancy X) (specialB W X R S):=by
 refine ⟨t.Kplan _, principal X A p.tint, disjoint_left.mpr (fun x u v=> Hazel.special W X R S v u),?_ ⟩; intro x h; constructor
 · refine ⟨fun g=> mem_filter.mpr ⟨mem_univ _,((mem_filter.mp g).2).1⟩,fun t'=>not_not.mp (fun b=> h (qualify W X R S b (mem_filter.mp t'|>.2)))⟩
 intro e; obtain ⟨i,u⟩:= not_not.mp (mt (Hazel.qualify W X R S e) h); rw [invoice X A _ u]; exact t.nonchange u (fun t'=> h (mem_filter.mpr ⟨mem_univ _,And.symm t'⟩))
end YM.CF.BPress.Lily
