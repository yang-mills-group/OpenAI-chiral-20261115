import YM.SU5.Reconstruction.Trap.Bloom
import YM.Mink.Boost
/-!
# geometry knot
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Picket
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe
open Real
variable (a b : Axis)
abbrev rise (p:E4) (e:ℝ) := (p a+e*p b)/2
local notation "R" p:max e:max=> rise a b p e
noncomputable def lee (p:E4): E4:= p-((R p 1) • head a b 1+(R p (-1)) • head a b (-1))
noncomputable def quarter (v:E4):E4:= R v 1 • head b a (-1)+R v (-1) • head b a 1+lee a b v
noncomputable def move (t:ℝ) (v:E4):E4 := (R v 1 * Real.exp t) • head a b 1+(R v (-1) * Real.exp (-t)) • head a b (-1)+lee a b v
@[fun_prop] lemma smooth_move (t:ℝ): Continuous (move a b t):= by unfold move rise lee rise; fun_prop
lemma heft (x:E4): rise a b x 1 • head a b 1 + rise a b x (-1) • head a b (-1) + lee a b x=x:= by unfold lee; abel
variable {a b} (p:b≠a) (u:ℝ)
include p
lemma lees (x:E4): lee a b x a=0 ∧ lee a b x b=0:= by simp [lee, rise, head,p,p.symm]; constructor <;> ring
lemma eye_high (x:E4):move a b u x a=cosh u*x a+sinh u*x b:= by unfold move; rw [PiLp.add_apply,(lees p _).1]; simp [head,rise,p,p.symm,cosh_eq,sinh_eq]; ring
lemma eye_low (x:E4):move a b u x b=sinh u*x a+cosh u*x b:= by unfold move; rw [PiLp.add_apply,(lees p _).2]; simp [head,rise,p,p.symm,cosh_eq,sinh_eq]; ring
omit p
lemma others (x:E4)(i:Axis)(z:i≠a)(y:i≠b):move a b u x i=x i:= by simp [move,lee,head,y,z]
include p
lemma quarter_gear (x:E4): (quarter a b x b=x a) ∧ (quarter a b x a= -(x b)) ∧ (∀ i,i≠a→i≠b→ quarter a b x i=x i):= by
 unfold quarter; simp only [PiLp.add_apply,PiLp.smul_apply]; rw [(lees p _).1,(lees p _).2]; refine ⟨?_,?_,fun i q r=>?_⟩ <;> simp [p,p.symm,lee,head,rise, *] <;> ring
lemma dual (x y:E4): inner ℝ (move a b u x) y=inner ℝ x (move a b u y):= by
 calc
   _ = ∑ i:Axis, move a b u x i*y i:= by rw [PiLp.inner_apply]; apply Finset.sum_congr rfl; intros; simp [mul_comm]
   _ = ∑ i:Axis, x i * move a b u y i := by
     let S:Finset Axis:= Finset.univ.erase a; let A':= S.erase b; have ht:a∉ S:=Finset.notMem_erase _ _; have hv:b∈ S:= Finset.mem_erase.mpr ⟨p,Finset.mem_univ _⟩; have he(f:Axis→ℝ):∑ i:Axis,f i=f a+ (f b+(∑ i∈A',f i)):= by nth_rw 1 [←Finset.add_sum_erase _ f (Finset.mem_univ a)]; rw [Finset.add_sum_erase _ f hv]
     rw [he,he, eye_high p,eye_high p,eye_low p,eye_low p,show ∑ i∈A',move a b u x i*y i=∑ i∈A',x i*move a b u y i from Finset.sum_congr rfl (?_)]
     · ring
     intro i e; have hz:i≠a:= fun v=> ht (v ▸ (Finset.mem_of_mem_erase e)); rw [others _ _ i hz (Finset.mem_erase.mp e).1,others _ _ i hz (Finset.mem_erase.mp e).1]
   _ = _:=by rw [PiLp.inner_apply]; apply Finset.sum_congr rfl; intros; simp [mul_comm]
private lemma head_sense (t:ℝ)(x:E4): move a b u (move a b t x) = move a b (u+t) x:= by
 ext i; by_cases h:i=a
 · subst i; rw [eye_high p,eye_high p,eye_low p,eye_high p,Real.cosh_add,Real.sinh_add]; ring
 by_cases q:i=b
 · subst i; rw [eye_low p,eye_high p,eye_low p,eye_low p,Real.cosh_add,Real.sinh_add]; ring
 rw [others _ _ _ h q,others _ _ _ h q,others _ _ _ h q]
-- canonical Lor convention check exactly `boost`. any k reflected motion
omit p
open Mink
lemma boost_eq (i: SpaceAxis) (x:E4) : move timeAxis i.castSucc u x=Lorentz.act ((Mink.Ray.fromAxis i).boost u) x:= by
 rw [Mink.Ray.boost_at]; apply Mink.ext_by
 · rw [Mink.Ray.newSpace]; ext1 j
   by_cases p:i=j
   · subst j; change move timeAxis i.castSucc u x i.castSucc = _; rw [eye_low ((by exact Fin.castSucc_ne_last _)), Mink.Ray.onAxis]; unfold time; simp [Ray.fromAxis,spatial]; ring
   change move timeAxis i.castSucc u x j.castSucc=_; have hb: j.castSucc≠ i.castSucc:= by simpa using (Ne.symm p)
   rw [others _ _ j.castSucc ((by exact Fin.castSucc_ne_last _)) hb]; simp [Ray.fromAxis,spatial,p,Ne.symm p]
 change move timeAxis i.castSucc u x timeAxis=_; rw [eye_high ((by exact Fin.castSucc_ne_last _)),Mink.Ray.newClock, Mink.Ray.onAxis]; rfl
end YM.Picket
