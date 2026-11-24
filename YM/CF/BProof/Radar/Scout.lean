import YM.CF.BProof.Radar.Knot
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 4000
set_option maxHeartbeats 720000
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard Rows
open scoped BigOperators Classical
variable {C A:Type*}{n:Side}{l k r d:ℕ}
namespace Sleet
open Crop.Native Cat Tetra
abbrev Earsa (l:ℕ)(n:Side):= (Signed → Together (2*(kSize*l)) n)×March n
abbrev Hop(l:ℕ)(n:Side): Field n (Earsa l n) Prop:= netX l (seed (2*(kSize*l)) n)
abbrev pay_l(l:ℕ):=let j:=2*(kSize*l); distD kSize l (grSize j*j+(0+j+0)+grSize j*j)
abbrev cover(l:ℕ) := 3*(kSize*l)
abbrev Tutor {l:ℕ}(f:Field n A Prop)(p:ℕ):Prop:= SplitK n f p ∧ Sym f ∧ Spotty f l (cover l) -- unused implicit l cannot infer
lemma haveH(n:Side)(l:ℕ)(p:2*(2*(kSize*l))<n.val): Nonempty (Earsa l n)∧Tutor (l:=l) (Hop l n) (pay_l l):=by
 have h:=haveP _ _ p; have V:=nonE n; have W:=together p; exact ⟨inferInstance,rangeK l _ h.2.1,sym _ _ h.2.2,area h.1⟩
-- second invariant colouring. Keep set of all displacements in each Signed orbit to some net centre.
def orbit (f:Field n A Prop)(d:ℕ) : Field n A (Finset ↑(shell d)):=fun w x=> univ.filter fun i=> ∃ s:Signed,f w (x+wrap n (s.act i.val))
variable (f:Field n A Prop)
lemma orbit_mem(x:Site n)(d:ℕ)(w:A)(i:shell d) : i∈orbit f d w x ↔ ∃ s:Signed,x+wrap n (s.act i.val)∈ crowd f w:=by simp [orbit]
lemma close(v:shell d)(s:Signed)(x:Site n):x+wrap n (s.act v.val)∈ region n x d:=by rw [reg_in,separation_comm _ _,separation,add_sub_cancel_left]; exact shell_weight _ ((shell_signed ..).2 v.property)
lemma uses (d:ℕ): Uses f (orbit f d) d:=by intro x y z p; ext j; simp only [orbit,mem_filter,mem_univ,true_and]; apply exists_congr; intro s; exact iff_of_eq (p (close j s x))
lemma senses (d:ℕ): Loyal f (orbit f d):=by
 intro s x E p w y; ext i; simp only [orbit,mem_filter,mem_univ,true_and,p,facet_apply,Signed.act_add,wrap_signed]; constructor
 · rintro ⟨t,v⟩; refine ⟨s*t,?_⟩; rw [add_assoc,Signed.act_mul]; exact v
 rintro ⟨t,v⟩; refine ⟨s⁻¹*t,?_⟩; rw [Signed.act_mul,Signed.act_inv,←add_assoc]; exact v
lemma found (t:Spotty f l d)(x:Site n)(w:A): (orbit f d w x).Nonempty:=by
 obtain ⟨y,q,h⟩:= halo_spec.mp ((t w).2 x); let g:=lift (y-x); have hp:wrap n g=y-x:=wrap_lift _; let v:shell d:=⟨g,shell_hits (y-x) h⟩; refine ⟨v,(orbit_mem ..).2 ⟨1,?_⟩⟩; rw [Signed.act_one,show wrap n v.val = y-x from hp]; simpa using q
abbrev patch (g:Field n A C)(u:A)(c:C): Support n:=univ.filter fun j=>g u j=c
@[simp] lemma on_patch(g:Field n A C)(u:A)(c:C)(x:Site n):x∈patch g u c↔g u x=c:=by simp [patch]
lemma crown (t:Spotty f (2*(kSize*l)) d) (w:A)(a: Finset ↑(shell d)):Vale (patch (orbit f d) w a) l kSize:=by
 intro s p q; rcases s.eq_empty_or_nonempty with h|h; rw [h,card_empty]; omega
 obtain ⟨x,g⟩:=h; obtain ⟨z,h⟩:= found f t x w; rw [on_patch ..|>.1 (p g)] at h; have he(i:s):z∈ orbit f d w i.val:=by rw [on_patch ..|>.1 (p i.property)]; exact h
 choose K V using (fun i:s=> orbit_mem ..|>.1 (he i)); have hp:Injective K:=by
    intro i j u; by_contra p; have ht:= V i; have hh:= V j; rw [u] at ht; have hM:= (t w).1 _ ht _ hh (fun h=>p (Subtype.ext (add_right_cancel h))); rw [separation_translate] at hM; exact hM.not_ge (q _ i.property _ j.property)
 simpa [kSize] using Fintype.card_le_of_injective K hp
end Sleet
end YM.CF.BProof.Mesh
