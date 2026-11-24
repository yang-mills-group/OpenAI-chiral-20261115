import YM.CF.BProof.Radar.Jest
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard Rows
open scoped BigOperators Classical
variable {n: Side}{C A:Type*}{l k r d s:ℕ}
namespace Policy
-- pack count via displacements, no geometric ties need moving. Fin bounds independent s and S.
abbrev ore(n:Side)(j:Site n)(l:ℕ) :Support n:= region _ j l
abbrev cell(S:Support n)(k:ℕ)(j:Site n):= S∩ region n j k
lemma position (S:Support n)(k r:ℕ)(d: Sparse S separation r)(h:0 < r)(x:Site n):(cell S (k*r) x).card ≤ (shell k).card:=by
 let P:= cell S (k*r) x
 let A(i:P):= lift (i.val-x)
 have ht(i:P)(u:Axis):(A i u).natAbs ≤ k*r:= (shell_in ..).1 (shell_hits _ ((separation_comm x i.val) ▸ ((reg_in x i.val).1 (mem_inter.mp i.property).2) : separation i.val x≤_)) _
 have hr:0<(r:ℤ):= by exact_mod_cast h
 let F(i:P):Cover:=fun u=> A i u/r -- int
 have hw(i:P): F i∈shell k:=(shell_in ..).2 <| by
    intro u; let z:=A i u; change (z/r).natAbs≤ _; have H:z.natAbs ≤ k*r:=ht i u; have h1:z≤ k*(r:ℤ):=by push_cast; omega -- tune cast product
    have h2:-(k*(r:ℤ)) ≤ z :=by omega
    have hz:= Int.ediv_mul_add_emod z r; have ht:=Int.emod_nonneg z (ne_of_gt hr); have hf:=Int.emod_lt_of_pos z hr; have f1:z/r ≤ (k:ℤ):=by nlinarith
    have f2:-(k:ℤ) ≤ z/r:=by nlinarith
    omega
 let G(i:P):↑(shell k) := ⟨F i,hw i⟩
 have hz:Injective G:=by
    intro i j v; have hv:F i= F j:=congrArg Subtype.val v; by_contra u; apply (d _ (mem_inter.mp i.property).1 _ (mem_inter.mp j.property).1 (fun h=> u (Subtype.ext h))).not_ge; let Z:=A i-A j; have h:i.val-j.val=wrap n Z:=by unfold Z A; rw [map_sub]; simp
    rw [separation,h]; apply shell_weight; apply (shell_in ..).2; intro a; set p':ℤ:=A i a; set q:ℤ:=A j a; have hl:p' / r=q / r:= congrFun hv a; change (p'-q).natAbs ≤ r; have hx:= Int.ediv_mul_add_emod p' r; have he:= Int.ediv_mul_add_emod q r; have h1:=Int.emod_nonneg p' hr.ne'; have h2:= Int.emod_nonneg q hr.ne'; have h3:= Int.emod_lt_of_pos q hr; have h4:=Int.emod_lt_of_pos p' hr; rw [hl] at hx; omega
 simpa using Fintype.card_le_of_injective G hz
end Policy
end YM.CF.BProof.Mesh
