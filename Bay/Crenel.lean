import Bay.Dagger
import YM.SU5.Exchange.Stack.Nest
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf
open Mew PowerSeries
open scoped YM.CF.Mew
variable {n:Side} {P:BudgetPoint}

open TreasuryFog Roots Py Moto


/-- insert guard halo onto every contributing tag. circumference large only
fixed (per engine); pays fixed exponent with unused rate.
-/
abbrev plankN(L:ℕ):ℕ:=11000+10*L
abbrev plank (L b:ℕ)(o:Seat n): Aura n :=
 ⟨Lattice.halo (plankN L * b) {o}, o, Lattice.halo_spec.mpr
   ⟨o,mem_singleton.mpr rfl,by rw[separation_self];omega⟩⟩
abbrev slabOK (n:Side)(L b:ℕ):Prop:=plankN L*b<n.val ∧ 0<b

def stick (L:ℕ)(o:Seat n)(b:ℕ)(V:Sour.Bag n):Sour.Bag n:=
 fun X=>∑ Y:Aura n,if αK Y (plank L b o)=X then V Y else 0
variable {L b:ℕ} {o:Seat n}
lemma distanceG (n:Side)(o:Site n)(r:ℕ)(p:2*r<n.val):∃z:Site n,separation o z=r:=by
 let g :Cover:=fun _=>r
 refine ⟨wrap n g+o,?_⟩
 rw [separation_comm,separation,add_sub_cancel_right]
 have e:lift (wrap n g)=g:=Lattice.lift_eq_iff.mpr
   ⟨rfl, fun i=>by dsimp only [g]; omega⟩
 unfold pdist
 rw [e]
 simp [g]
 exact Finset.sup_const univ_nonempty _

lemma plankOut (Y:Aura n)(s:slabOK n L P.B):
 outmint P L o (αK Y (plank L P.B o)).val:=by
 let b:=P.B; let d:=plankN L*b
 obtain ⟨z,e⟩:=distanceG _ o d (by
    change 2*d<n.val*2
    rw [mul_comm n.val]
    exact Nat.mul_lt_mul_of_pos_left s.1 (by omega))
 let A:=(αK Y (plank L P.B o)).val
 have mz : z ∈ A:= mem_union_right _ (Lattice.halo_spec.mpr ⟨o,mem_singleton.mpr rfl,e.le⟩)
 have mo:o∈A:=mem_union_right _ (Lattice.halo_spec.mpr ⟨o,mem_singleton.mpr rfl,separation_self o ▸ Nat.zero_le _⟩)
 have j:=Corona.extent A b mo mz
 rw [e] at j
 have h:1≤b:=s.2
 have g: L ≤ coverNumber b A:=by
    by_contra! k
    have hk:=Nat.mul_le_mul k.le (show 4*b+2≤ 6*b by omega)
    unfold d plankN at j
    nlinarith only [hk,j,h,Nat.zero_le (L*b)]
 refine ⟨mo,g.trans ?_,fun t=>?_⟩
 · exact Nat.le_self_pow (by omega) _
 obtain ⟨x,t,u⟩:= Lattice.halo_spec.mp (t mz)
 rw [mem_singleton.mp t,e] at u
 change d ≤10000*b at u
 unfold d plankN at u
 nlinarith
#print More

def padFee(L:ℕ):ℝ:=Real.exp (9*((plankN L+plankN L+1:ℕ)^4:ℝ))

lemma tact_lid {s:ℝ}(e:0 ≤ s)(k:s≤9)(j:0<b) (Y:Aura n)(t:o∈Y.val):
 Sour.tact s b (αK Y (plank L b o)) ≤ padFee L * Sour.tact s b Y:=by
 have m:o ∈ (plank L b o).val:=
    Lattice.halo_spec.mpr ⟨o,mem_singleton.mpr rfl,separation_self _ ▸ Nat.zero_le _⟩
 have h:= @tact_αK n b s e Y (plank L b o) ?_
 swap; · exact mem_filter.mpr ⟨mem_univ _,fun p=> disjoint_left.mp p t m⟩
 apply h.trans
 rw [mul_comm (padFee _)]
 apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
 apply Real.exp_monotone
 exact mul_le_mul k (by 
    have w:=Corona.tile o (plankN L) b j
    unfold Sour.widthK
    exact_mod_cast w) (Nat.cast_nonneg _) (by norm_num)
variable {q:ℕ}{a d s h:ℝ}

private lemma pad_le (L:ℕ)(o:Seat n){A:Support (More n)}(e:0  ≤ s)(k:s≤9)(j:0<b)
 (W:Aura n→ℝ)(p:voyageB W b s ≤a)(u:0≤W)(x:o∈ A)
 (t:∀ Y:Aura n, ¬A ⊆Y.val→W Y=0):
 (∑i:Aura n,W i*Sour.tact s b (αK i (plank L b o))) ≤ padFee L * a:=by
 apply le_trans _ (mul_le_mul_of_nonneg_left p (Real.exp_pos _).le)
 unfold voyageB
 rw [mul_sum]
 apply sum_le_sum
 intro i _
 by_cases r:A⊆i.val
 · rw [mul_left_comm _ (W i)]
   exact mul_le_mul_of_nonneg_left (tact_lid e k j i (r x)) (u i)
 rw [t i r]
 simp
lemma sticks (L:ℕ)(o:Seat n){A:Support (More n)}(V:Sour.Bag n)
 (e:0≤ s)(k:s≤9)(j:0<P.B)(x:o∈ A)
 (p:Barrage P q A h V s a d):
 Barrage P q (plank L P.B o).val h (stick L o P.B V) s (padFee L * a) (padFee L * d):=by
 obtain ⟨Q,R,F,Z,z,w⟩:=p.price
 let B:=plank L P.B o
 let I(i:Aura n):=αK i B
 let T (Y:Aura n) (X:Aura n):= if X=I Y then V Y else 0
 have m:stick L o P.B V=∑ i,T i:=by
    funext X
    rw [stick,Finset.sum_apply]
    exact sum_congr rfl fun i _=>if_congr eq_comm rfl rfl
 rw[m]

 have f(i:Aura n)(_ :i∈(univ:Finset _)):
      Barrage P q B.val h (T i) s (Q i * Sour.tact s P.B (I i)) (R i*Sour.tact s P.B (I i)):=
    Barrage.single (I i) (V i) ((F i).mantle subset_union_left)
       subset_union_right
 exact (Barrage.whole univ T (fun i=>Q i * Sour.tact s P.B (I i))
      (fun i=>R i * Sour.tact s P.B (I i)) f).bigR
   (pad_le L o e k j Q z (fun i=>(F i).tube.price) x (fun i h=>(Z i h).2.1))
   (pad_le L o e k j R w (fun i=>(F i).forms.choose_spec.1.price) x
      (fun i h=>(Z i h).2.2))
lemma stickSum (L b:ℕ)(o:Seat n)(V:Sour.Bag n):
 (∑ i,stick L o b V i)=∑ i,V i:=by
 simp only [stick];rw [sum_comm];simp
#print Swell.grooveB


/-- full retention of openings at operator sum, and of outmint -/
lemma sticksOut (L b:ℕ)(o:Seat n)(V:Sour.Bag n)(X:Aura n)
 (u:stick L o b V X ≠0):∃Y:Aura n,αK Y (plank L b o)=X:=by
 unfold stick at u
 obtain ⟨i,v,t⟩:= exists_ne_zero_of_sum_ne_zero u
 refine ⟨i, Classical.byContradiction fun k=>t (if_neg k)⟩
end YM.CF.Bay
