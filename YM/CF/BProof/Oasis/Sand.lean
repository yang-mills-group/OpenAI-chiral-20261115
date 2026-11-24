import YM.CF.BProof.Oasis.Petal
/-! eq:B-Oexpect including regular/force/insertion *same covariances*.
The heating parameter is not an argument of the history. `logs` can compare
with all force and site vertices turned off. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory Dew
open Lattice Tenant Lat Cube Tulip Scree Skye Spin
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}
abbrev Lv(N:Side):=Flame (Single N) (Dwell N)
abbrev JPick(x:Site N):= ↑(alloy (chef x))
abbrev OptionJ(N:Side):= Σ i:Site N,JPick i
def ArcJ(N:Side): Dew (OptionJ N) (Single N) where
 free i j:=i.1≠j.1
 line i:=(bkiln i.2.val).reverse
 fresh i:=List.nodup_reverse.mpr (bkiln_f _)
 even i:=by rw [List.length_reverse,bkiln_size]; exact (mem_alloy ..|>.mp i.2.property).2
abbrev OptionG(N:Side):= OptionR N ⊕ OptionF N
abbrev Options(N:Side):= OptionJ N ⊕ OptionG N
def Ark(N: Side): Dew (Options N) (Lv N):=(ArcJ N).fire ((lineR N).addD (lineF N))
-- using final C that can be any skew matrix at Pair2 here (determined on all Deck data). include G target Plant
def tokenJ (S:Support N)(Y:Pollen (Site N))(ε:ℂ)(A:Plant N)(C:Op (Single N))(i:OptionJ N):ℂ:= if i.1∈ S then ε* glow (Y i.1)* coeffJ (chef i.1) C i.2.val (A.leaf i.1) else 0
def letter (C:Op (Single N))(x:Cᵀ= -C) : Poly (Single N) (Single N):= ⟨fun i=> Double.printT (spear C i),fun i j=>by rw [show antiB (printT _) _=star (antiB (thorn C j) (thorn C i)) from ?_,thorn_anti x,star_zero]; unfold thorn antiB; rw [star_add,star_mul,star_mul,star_star,star_star]⟩
lemma letterJ(i:OptionJ N){C:Op (Single N)}(x:Cᵀ= -C): (letter C x).cook ((ArcJ N).grace i) = star (crown C i.2.val):= by
 change (letter C x).eval (word _)=_; rw [cookEven _ _ ((ArcJ N).even i),flakeJ_id]; rfl
variable (T:Plant N)(ε:ℂ)(S:Support N)(Y:Pollen (Site N)){C:Op (Single N)}(x:Cᵀ= -C)
set_option maxHeartbeats 1600000 in
lemma insertionJ(i:Site N) : (letter C x).cook (∑ j:JPick i,(ArcJ N).orts (tokenJ S Y ε T C) ⟨i,j⟩) = if i∈S then (ε*glow (Y i)) • opJ (chef i) C (T.leaf i) else 0:=by
 rw [map_sum]; by_cases d:i∈ S; · rw [if_pos d]; unfold opJ; rw [smul_sum, ← Finset.sum_attach (alloy (chef i))]; apply sum_congr rfl; intro j _; unfold orts flakeJ; rw [cookPoly, letterJ]; simp only [tokenJ,d,if_true,mul_smul]
 rw [if_neg d]; unfold orts tokenJ; simp only [d,if_false,cookPoly,zero_smul,sum_const_zero]
lemma expHollow{I:Type*}[LinearOrder I][Fintype I]{K:Type*}[Fintype K][LinearOrder K](A:Poly I K)(v:ℂ): A.cook (exp (hollow v))=Complex.exp v • 1:=by simpa using (Pastry.expReal A v 0)
lemma cookerJ (g:Plant N)(e:∀ i,i ∈ S → g.leaf i =opJ (chef i) C (T.leaf i)): (letter C x).cook ((ArcJ N).foldS (tokenJ S Y ε T C))=(optional ε Y g).prod S:=by -- typo binder
 rw [(ArcJ N).groups (fun _ _=>Iff.rfl)]; -- prod in monoid comm to noncomm output
 rw [← Finset.noncommProd_eq_prod, Finset.map_noncommProd]; -- simp dependent? need prod_congr
 let U:=(optional ε Y g).patch 1 S; have hp(i:Site N): (letter C x).cook (1+∑ j:JPick i,(ArcJ N).orts (tokenJ S Y ε T C) ⟨i,j⟩) = U.leaf i:=by
   rw [map_add,map_one,insertionJ T]; change (1+(if i∈S then _ else _))=(if i∈ S then 1+(ε*glow (Y i)) • g.leaf i else 1); by_cases h:i∈S; · rw [if_pos h,if_pos h,e i h]
   rw [if_neg h,if_neg h,add_zero]
 rw [show (optional ε Y g).prod S=U.prod univ from by unfold U; simp [Plant.prod_patch]]; exact Finset.noncommProd_congr rfl (fun i _=> hp i) .. -- tune
lemma evaporate{I V:Type}[Fintype V][DecidableEq V][LinearOrder I][Fintype I](A:Dew V I): A.foldS 0=1:=by
 unfold foldS; rw [sum_eq_single ∅]; rw [bag,if_pos (show A.mild ∅ from fun i hi _ _ _=> False.elim (notMem_empty _ hi)),prod_empty]; intro i _ k; unfold Dew.wrap; split; obtain ⟨j,h⟩:=nonempty_iff_ne_empty.mpr k; rw [prod_eq_zero (show j∈i from h) rfl, show hollow (n:=I) 0=0 from Subtype.ext (zero_smul ..),zero_mul]; rfl; simp
variable (D:GramM N)
def actionsG(v:ℝ)(F:OptionF N→ℂ)(x:Pane N):OptionG N→ℂ:=Sum.elim (FeeR D v x) F
abbrev hotA(v:ℝ)(F:OptionF N→ℂ)(x:Pane N)(J:OptionJ N→ℂ):Options N→ℂ:= Sum.elim J (actionsG D v F x)
def zoom(v:ℝ)(F:OptionF N→ℂ)(x:Pane N):= exp (foldR D v x) * (lineF N).foldS F
lemma zoomB(f:Pollen (Site (More N)))(z:Fitted D)(x:Orbit N): boardF D x f=zoom D 1 (RateF D f x) x.1:=by rw [boardF,zoom,fold_one,←readers D f z]
variable (xR:Pane N)(g:Fitted D){A:Op (Single N)} (m:IsStarProjection A)(Z:FC (Single N)→ₗ[ℂ] ℂ){Q:Op (Lv N)}{r:Lv N→Lv N→ℂ}
variable (q:Scores r (fun l=> Z (rollC (act (letter C x) (nursery A m)) l))) (u:Qᵀ= -Q)(b:∀ i j, polite i j→ r i j=Q i j)
include b q u m g in
lemma trio(v:ℝ)(J:OptionJ N→ℂ)(F:OptionF N→ℂ) : Z ((letter C x).cook ((ArcJ N).foldS J)*tank A (zoom D v F xR)) = Complex.exp (PriceR D v xR)*(∑ i:Finset (Options N), (Ark N).silica (hotA D v F xR J) Q i):=by
 rw [zoom,tank_eq A _ m,recovered D v g,mul_assoc,←phaseFold,map_mul (nursery A m).cook,expHollow, Algebra.smul_mul_assoc,one_mul,Algebra.mul_smul_comm,map_smul]; change Complex.exp _ * Z _=_; congr 1; exact Dew.relay _ _ _ _ _ _ _ q b u -- tune arguments order x curr
end YM.CF.BProof.Oasis
