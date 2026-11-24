import YM.CF.BProof.Shade.Stone
import YM.CF.BProof.Shade.Match
/-! Discrete material & symmetry packet (probability law imported by Shad.Later). -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option synthInstance.maxSize 4096
noncomputable section
namespace YM.CF.BProof.Mesh.Shore
open Equiv Nest Stave Gallery Function MeasureTheory Metric Filter Finset Wilson Lattice Nerve Carpet Score Regard
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {n:Side}{s l k:ℕ}{u ε d a b δ θ:ℝ}
namespace Fancy
local notation "K_"=>partK k
abbrev Ribbon(n:Side):=(Site n→Bool) × (Site n→ Axis → Bool×Bool)
abbrev PolicyW (n:Side):= Vent n × Ribbon n
abbrev Word (n:Side)(s l k:ℕ):= Board n s k ×(Board n l k × PolicyW n)
lemma bornF(n:Side)(s l k:ℕ): Finite (Word n s l k):= by unfold Word; infer_instance
abbrev π(n:Side)(s k:ℕ)(w:Board n s k):Wool n (partK k):= Wool.structureC s (netW n s k) (colours n s k) w
def read(w:Word n s l k):Score n (partK k):= ⟨π n s k w.1,π n l k w.2.1,w.2.2.1,w.2.2.2.1⟩
def signal(w:Word n s l k):StampB n:= Function.uncurry w.2.2.2.2
section sym
def μE(p q:Bool): Equiv.Perm (Bool×Bool) := {
 toFun:= RevB p q
 invFun:= RevB p q
 left_inv:= fun x=> by cases p <;> cases q <;> simp [RevB]
 right_inv:= fun x=> by cases p <;> cases q <;> simp [RevB] }
lemma flip_f (j:Signed)(x:Site n)(p:Bool):∃ E:Perm (Site n→Axis→Bool×Bool),∀ f, edge_h j x p (Function.uncurry (E f)) (Function.uncurry f):=by
 let e:Bones n≃Bones n:= Equiv.ofBijective (sendEdge j x) ⟨sendEdge_injective j x,Finite.injective_iff_surjective.mp (sendEdge_injective j x)⟩
 let r:= (Equiv.arrowCongr e.symm (Equiv.refl (Bool×Bool))).trans (Equiv.piCongrRight (fun i=>μE (j.flip i.2) p)); let g:StampB n ≃ (Site n→ Axis→ Bool×Bool):= Equiv.curry .. -- name
 exact ⟨g.symm.trans (r.trans g),fun i b=> rfl⟩
variable (pT:Bill n s k (netW n s k) (colours n s k))(pS:Bill n l k (netW n l k) (colours n l k))(pC:Note (netW n s k) (colours n s k) s a)(pF:Note (netW n l k) (colours n l k) l b)
include pT pS pC pF
theorem spun_f(j:Signed)(x:Site n)(p:Bool):∃ E:Perm (Word n s l k),∀ f:Word n s l k, Rides j x p (read (E f)) (read f) ∧ edge_h j x p (signal (E f)) (signal f):=by
 obtain ⟨E0,hE⟩:=pT.inK j x; obtain ⟨E1,hR⟩:=pS.inK j x; obtain ⟨P,hs⟩:= flip_f j x p; let e:=facet j x; let v:= arrowCongr e.symm (orderEquiv j).symm
 let Z:= (show Perm Bool from (if p then Equiv.boolNot else Equiv.refl _)); let u:= arrowCongr e.symm Z
 have he(y:Bool): Z y=p.xor y:=by unfold Z; cases p <;> simp
 let E : Perm (Word n s l k):= prodCongr E0 (prodCongr E1 (prodCongr v (prodCongr u P)))
 exact ⟨E,fun f=>⟨⟨Wool.chargeD pC hE f.1,Wool.chargeD pF hR f.2.1,fun i=>(orderEquiv j|>.apply_symm_apply _).symm, fun i=> he (f.2.2.2.1 (e i))⟩,hs f.2.2.2.2⟩⟩

def countR (s k:ℕ):= asset s k + 2*Note.receipt s (partK k)
abbrev costly(s l k:ℕ):= countR s k+countR l k
def pixels (w:Word n s l k) (i:Site n):= let z:=read w;(z.cur.mark i,z.fine.mark i,z.orderC i,z.fire i,w.2.2.2.2 i) -- associates to right
omit pS pF
lemma coatK: SplitK n (fun w:Board n s k=> (π n s k w).mark) (countR s k):= by
 refine (Mesh.Uses.epoch (Wool.use_cost pC) pT.separated).star ?_; unfold countR; omega
include pS pF
lemma picture: SplitK n (pixels (s:=s) (l:=l) (k:=k)) (costly s l k):= by
 refine SplitK.product (f:=fun i=> (π n s k i).mark) (g:=fun (i:Board n l k × PolicyW n) y => ((π n l k i.1).mark y, i.2.1 y,i.2.2.1 y,i.2.2.2 y)) ?_ ?_
 · exact (coatK pT pC).star (by unfold costly; omega)
 exact SplitK.product ((coatK pS pF).star (by unfold costly; omega)) (SplitK.product (SplitK.fresh Lattice.Order n (costly s l k)) (SplitK.product (SplitK.fresh Bool n (costly s l k)) (SplitK.fresh (Axis→ Bool×Bool) n (costly s l k))))

abbrev zone(s l:ℕ):= 1+Score.wager s l
abbrev costFull(s l k:ℕ):= zone s l+costly s l k+zone s l
variable {T:Tray (Floor (partK k)) ε}{F:Drum (rollup (partK k) T) (Floor (partK k))}
local notation "P" => make s l u T F
lemma paper_w : SplitK n (fun w:Word n s l k=>fun (x:Site n)(U:Heads n)=> Function.curry (make s l u T F (read w) (signal w) U) x) (costFull s l k):=by
 let i:= picture pT pS pC pF; apply Mesh.Uses.epoch (l:=zone s l) _ i; intro x y z h; funext U; ext j :1 -- goal equality of site result
 let A:Score n (partK k):=read y; let B:=read z; let R:= Score.wager s l
 let p: Seal A s l a b:=⟨pC.hp,Wool.inducts pC _, Wool.inducts pF _⟩; let S:=region n x (zone s l);
 have hm: localLens R (x,j)⊆ S:=by
    intro u v; obtain ⟨w,p,t⟩:= halo_spec.mp v; have hp:separation x w ≤1:=by rcases mem_insert.mp p with z|z; rw [z]; simp; rw [mem_singleton.mp z]; exact nearV x (posDir j)
    apply (reg_pay hp (show 1+R≤zone s l from le_rfl)); exact (reg_in ..).2 t
 have hz(i:Site n)(t:i∈ S): pixels y i=pixels z i:=h t; have V : Reads S A B U U:= by
    refine ⟨fun i p=> ?_,fun i p=>?_,fun i p=>?_,fun i p=>?_,fun _ _ _=>rfl⟩
    · exact congrArg (fun u=>u.2.2.1) (hz i p)
    · exact congrArg Prod.fst (hz i p)
    · exact congrArg (fun u=>u.2.1) (hz i p)
    exact congrArg (fun u=>u.2.2.2.1) (hz i p)
 exact stencil p (x,j) (V.reduce hm) (congrArg (fun t=>t.2.2.2.2 j) (hz x (by simp [S]))) -- syntax pipeline
end sym
end Fancy
end YM.CF.BProof.Mesh.Shore
