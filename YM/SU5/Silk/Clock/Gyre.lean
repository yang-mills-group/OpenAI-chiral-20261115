import YM.CF.Pec.Sorrel
import YM.CF.Ione.Tick
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Ione.Clock
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
abbrev inPlane:=Pec.X (Equiv.swap 0 1)
abbrev outPlane:=Pec.X (Equiv.swap 2 3)
abbrev exchangePlane:=Pec.X (Equiv.swap 0 2 * Equiv.swap 1 3)
def Hooked : Set Signed:= Set.range Signed.mirror ∪ {inPlane,outPlane,exchangePlane}
abbrev Loomed:=Submonoid.closure Hooked
lemma mirror_l(i:Axis):Signed.mirror i∈ Loomed:= Submonoid.subset_closure (Or.inl ⟨_,rfl⟩)
lemma in_l:inPlane∈ Loomed:=Submonoid.subset_closure (by simp [Hooked])
lemma out_l:outPlane∈ Loomed:=Submonoid.subset_closure (by simp [Hooked])
lemma exchange_l:exchangePlane∈ Loomed:=Submonoid.subset_closure (by simp [Hooked])
lemma back_l(p:Signed)(hp:p∈ Loomed):p⁻¹∈ Loomed:=by
 refine Submonoid.closure_induction (motive:=fun u _=> u⁻¹∈ Loomed) ?_ (by simp) (fun x y _ _ i j=>by rw [_root_.mul_inv_rev]; exact mul_mem j i) hp
 rintro p h
 suffices v:p*p=1 by rw [show p⁻¹=p from inv_eq_of_mul_eq_one_right v]; exact Submonoid.subset_closure h
 rcases h with ⟨i,rfl⟩ | h
 · apply Signed.ext
   · rfl
   funext x; simp [Signed.mirror]
 rw [Set.mem_insert_iff,Set.mem_insert_iff,Set.mem_singleton_iff] at h; rcases h with rfl|rfl|rfl
 all_goals refine Signed.ext ?_ rfl
 all_goals ext i; fin_cases i<;>decide
/-- A little finite representation specified constructively by generators.
The spin used below need *not* be chosen along the generator words. -/
def Whirl(N:Side):Subgroup (Sweep N) where
 carrier:={x:Sweep N| x.charge=false ∧ x.s∈ Loomed}
 one_mem':= ⟨rfl, show (1:Signed)∈ Loomed from Loomed.one_mem⟩
 inv_mem':=fun {i} hi=> ⟨hi.1,back_l i.s hi.2⟩
 mul_mem':=fun {i j} a b=> ⟨show i.charge.xor j.charge=false from by rw [show i.charge=false from a.1,show j.charge=false from b.1]; rfl, mul_mem a.2 b.2⟩
lemma whirl {N:Side}(s:Sweep N) : s∈ Whirl N ↔ s.charge=false ∧ s.s∈Loomed:=Iff.rfl

def Price(s:Signed):ℝ:= ↑((Equiv.Perm.sign s.perm):ℤ)
lemma price_m(p q:Signed):Price (p*q)=Price p*Price q:=by
 unfold Price; rw [show (p*q).perm=p.perm*q.perm from rfl,_root_.map_mul]; push_cast; rfl
lemma «price_±»(s:Signed): Price s=1∨Price s= -1:=by
 rcases Int.units_eq_one_or (Equiv.Perm.sign s.perm) with h|h<;>simp [Price,h]
lemma price_n(s:Signed):‖Price s‖=1:= by rcases («price_±» s) with h|h <;> simp [h]
lemma price_o(s:Signed):Price s*Price s=1:=by rcases («price_±» s) with h|h<;>simp [h]
@[simp] lemma price_one: Price 1=1:=by unfold Price; rw [show (1:Signed).perm=1 from rfl]; simp
lemma price_rev(s:Signed):Price s⁻¹=Price s:=by
 have h:=price_m s⁻¹ s; rw [inv_mul_cancel,price_one] at h
 rcases («price_±» s) with t|t <;> rw [t] at h ⊢ <;> linarith
lemma price_swap(i j:Axis)(h:i≠j): Price (Pec.X (Equiv.swap i j)) = -1:=by unfold Price Pec.X; rw [show Equiv.Perm.sign _=(-1:ℤˣ) from Equiv.Perm.sign_swap h]; simp
@[simp] lemma price_mir(i:Axis):Price (Signed.mirror i)=1:= by unfold Price; rw [show (Signed.mirror i).perm=1 from rfl]; simp
abbrev classic :Signed:=inPlane*outPlane
lemma exch_lemma : exchangePlane=Pec.X (Equiv.swap 0 2)*Pec.X (Equiv.swap 1 3):=rfl
@[simp] lemma price_in :Price inPlane= -1:=price_swap _ _ (by decide)
@[simp] lemma price_out :Price outPlane= -1:=price_swap _ _ (by decide)
@[simp] lemma price_class :Price classic=1:=by rw [price_m,price_in,price_out]; norm_num
@[simp] lemma price_exchange : Price exchangePlane=1:=by rw [exch_lemma,price_m,price_swap 0 2 (by decide),price_swap 1 3 (by decide)]; norm_num
@[simp] lemma det_inp : detX inPlane=true:=Pec.detSwap 0 1 (by decide)
@[simp] lemma det_outp : detX outPlane=true:=Pec.detSwap 2 3 (by decide)
@[simp] lemma det_classp : detX classic=false:=by rw [det_p,det_inp,det_outp]; rfl
@[simp] lemma det_exchange :detX exchangePlane=false:=by rw [exch_lemma,det_p,Pec.detSwap 0 2 (by decide),Pec.detSwap 1 3 (by decide)]; rfl

/-- Cover split into two planes. -/
def stripe(i:Axis):Bool:= decide (i<2)
lemma color_l(p:Signed)(hp:p∈ Loomed):∀ i j, stripe i=stripe j→stripe (p.perm i)=stripe (p.perm j):=by
 refine Submonoid.closure_induction (motive:=fun p _=>∀ i j,stripe i=stripe j→stripe (p.perm i)=stripe (p.perm j)) ?_ (fun _ _ h=>h) (fun x y _ _ i j a b t=> i _ _ (j a b t)) hp
 rintro y (⟨i,rfl⟩|h)
 · exact fun _ _ q=>q
 rw [Set.mem_insert_iff,Set.mem_insert_iff,Set.mem_singleton_iff] at h; rcases h with rfl|rfl|rfl <;> decide
end YM.CF.Ione.Clock
