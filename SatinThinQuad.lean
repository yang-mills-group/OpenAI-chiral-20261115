import YM.CF.Ione.Tick
import YM.CF.Skye.Bent
import YM.CF.Pec.Sorrel
import YM.CF.Hove.Point
import Mathlib.GroupTheory.Perm.Sign

/-!
A group for projecting, restricted to D4 × D4 on the two planes.
Root-calls and chromatic sign convention in actual step usage.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.QuadClock
open Spire Ione Fock Lat Lattice Wilson Laurent Rush Drapes Fir Peaks Dial Paige Scroll Hive Cube Skye
open Function Filter Finset
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open scoped Classical
variable {n m: Side} {s t: Sweep n}

def Quad (b:Signed): Prop:= ∀ i:Axis, (b.perm i).val<2 ↔ i.val<2
lemma quad_id : Quad 1:=fun _=> Iff.rfl
lemma quad_swap_lo : Quad (Pec.X (Equiv.swap 0 1)):=by intro i; fin_cases i<;>decide
lemma quad_swap_hi : Quad (Pec.X (Equiv.swap 2 3)):=by intro i; fin_cases i<;>decide
lemma quad_mirror (i:Axis): Quad (Signed.mirror i):=fun _=> Iff.rfl
lemma Quad.mul {a b:Signed}(h:Quad a)(p:Quad b): Quad (a*b):=fun i=>(h _).trans (p i)
lemma Quad.inv {a:Signed}(h:Quad a): Quad a⁻¹:=fun i=> by simpa using (h (a.perm.symm i)).symm
lemma Quad.lo {a:Signed}(h:Quad a):
 (a.perm 0=0 ∧ a.perm 1=1) ∨ (a.perm 0=1 ∧ a.perm 1=0):=by
 have h₀:=(h 0).2 (by decide); have h₁:=(h 1).2 (by decide); have hk:= a.perm.injective.ne (by decide:(0:Axis)≠1); change a.perm 0 ≠ a.perm 1 at hk; have hx: (a.perm 0).val ≠ (a.perm 1).val:= mt Fin.ext hk; simp only [Fin.ext_iff]; omega
lemma Quad.hi {a:Signed}(h:Quad a):
 (a.perm 2=2 ∧ a.perm 3=3) ∨ (a.perm 2=3 ∧ a.perm 3=2):=by
 have h₀:= mt (h 2).1 (by decide); have h₁:= mt (h 3).1 (by decide); have hk:= a.perm.injective.ne (by decide:(2:Axis)≠3); change a.perm 2 ≠ a.perm 3 at hk; have hx: (a.perm 2).val ≠ (a.perm 3).val:= mt Fin.ext hk; simp only [Fin.ext_iff]; omega

/-- Which Sweep usages. -/
def cycleSweep (n:Side) : Subgroup (Sweep n) where
 carrier:={s| Quad s.s}
 one_mem':=quad_id
 inv_mem' {x} h:= Quad.inv h
 mul_mem' {x y} h u:= @Quad.mul x.s y.s h u
lemma cycleQ (s:Sweep n):s∈cycleSweep n ↔ Quad s.s:=Iff.rfl
lemma cycle_re (h:s∈cycleSweep n)(G:Ratio n m): reSweep G s∈cycleSweep m:=h

noncomputable def tax (a:Signed):ℝ:= ((Equiv.Perm.sign a.perm:ℤ):ℝ)
abbrev bandSign (s:Sweep n):=tax s.s
lemma tax_o : tax 1=1:=by change (↑((Equiv.Perm.sign (1:Equiv.Perm Axis)):ℤ):ℝ)=1; simp
lemma tax_m (a b:Signed): tax (a*b)=tax a*tax b:=by simp only [tax,show (a*b).perm=a.perm*b.perm from rfl,map_mul,Units.val_mul,Int.cast_mul]
lemma tax_mi (a:Axis): tax (Signed.mirror a)=1:=tax_o
lemma tax_s (a b:Axis)(h:a≠b) : tax (Pec.X (Equiv.swap a b))= -1:=by change (↑((Equiv.Perm.sign (Equiv.swap a b)):ℤ):ℝ)= -1; rw [Equiv.Perm.sign_swap h]; simp
lemma tax_cases (a:Signed):tax a=1∨ tax a= -1 := by
 rcases Int.units_eq_one_or (Equiv.Perm.sign a.perm) with p|p <;> simp [tax,p]
lemma tax_sq (a:Signed):tax a*tax a=1:=by rcases tax_cases a with p|p<;>rw [p]<;>norm_num
lemma tax_inv (a:Signed):tax a⁻¹=tax a:=by
 have h:=tax_sq a; have u:tax a⁻¹*tax a=1:=by rw [←tax_m,inv_mul_cancel,tax_o]
 exact mul_right_cancel₀ (right_ne_zero_of_mul (h ▸ one_ne_zero)) (u.trans h.symm)
lemma band_inv (a:Sweep n): bandSign a⁻¹=bandSign a:= tax_inv _
lemma band_mul (a b:Sweep n): bandSign (a*b)=bandSign a*bandSign b:= tax_m ..

/-- Earlier (a), Later (b). Under `s` want the Later arrays to be
 the orientation-costed versions of Earlier. So a compare from a to b uses Forward when pricing b on pulled inputs. -/
abbrev Earlier (s:Sweep n) (a b:Site n):Prop:= boxA s (node b)=node a
lemma node_inj (n:Side):Injective (@node n):= fun x y h=> (assembly n).embed_injective (add_right_cancel (show _+(1:Site (More n))=_+_ from h))
lemma earlier_mills (s:Sweep n)(a b): Earlier s a b ↔ (castX s).mills n b=a:=by
 unfold Earlier; rw [show (boxA s) (node b) = node ((castX s).mills n b) from (Shape.nodex ..).symm]; exact (node_inj n).eq_iff
lemma Earlier.prod {a b c:Site n}(h:Earlier s a b)(u:Earlier t b c): Earlier (s*t) a c:= by unfold Earlier; rw [←sitV,u,h]
lemma Earlier.backward {a b:Site n}(u:Earlier s a b) : Earlier s⁻¹ b a:= by unfold Earlier; rw [sitU]; exact (boxA s).symm_apply_eq.mpr u.symm
lemma earlier_id (a:Site n): Earlier 1 a a:=by unfold Earlier; rw [sitA]; change Signed.act 1 _+(assembly n).root 0=_; rw [Signed.act_one,map_zero,add_zero]
lemma earlier_translate (a b:Site n): Earlier (Sweep.mk 1 (a-b) false) a b:=by
 unfold Earlier; rw [sitA]; change Signed.act 1 _+(assembly n).root (a-b)=_; rw [Signed.act_one,map_sub,Cube.node,Cube.node]; abel
lemma poseAll (k:Signed)(a b:Site n): ∃ s:Sweep n, s.s=k∧s.charge=false ∧ Earlier s a b:=by
 let t:Sweep n:=⟨k,0,false⟩; let b':=(castX t).mills n b; refine ⟨Sweep.mk 1 (a-b') false*t,(one_mul _),rfl,(earlier_translate ..).prod ((earlier_mills ..).2 rfl)⟩
lemma embed_box (G:Ratio n m)(s:Sweep n)(x): boxA (reSweep G s) ((ratio G).embed x)=(ratio G).embed (boxA s x):=by
 rw [sitA,sitA,show (reSweep G s).s=s.s from rfl, show (reSweep G s).b=G.embed s.b from rfl,← reA]; unfold affine; rw [← Ratio.signed, ← Ratio.root_embed, ← Ratio.root_embed, ← Ratio.root_embed,← Ratio.root_embed,map_add] -- tune
lemma heel_g (G:Ratio n m)(u: Odd G.count.val)(a:Site n): node (Hove.heel G a)=(ratio G).embed (node a):=by unfold Hove.heel; rw [embed_node G u]; simp
lemma Earlier.goes (G:Ratio n m) (u:Odd G.count.val){a b:Site n}(h:Earlier s a b): Earlier (reSweep G s) (Hove.heel G a) (Hove.heel G b):=by unfold Earlier; rw [heel_g G u,heel_g G u,embed_box, h]
end YM.CF.QuadClock
