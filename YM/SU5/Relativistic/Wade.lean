import YM.SU5.Relativistic.PolarRoot
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter MeasureTheory NormedSpace Metric Set
open scoped Topology Classical
private abbrev Add1:= {u:ℕ→ℕ//StrictMono u}
lemma threadSequence {A:Type*}[Countable A][Nonempty A] {P:A→(ℕ→ℕ)→Prop}(h:∀ a:A, ∀ u:ℕ→ℕ, StrictMono u → ∃ v:ℕ→ℕ,StrictMono v ∧ P a (u ∘ v))
    (e: ∀ a:A,∀ (u f g:ℕ→ℕ),Tendsto u atTop atTop→ g =ᶠ[atTop] f ∘ u→ P a f→P a g):∃ v:ℕ→ℕ,StrictMono v∧∀ a:A,P a v:=by
 obtain ⟨f,H⟩:= exists_surjective_nat A
 choose v hv U using (fun (u:Add1)(n:ℕ)=> h (f n) u.val u.property)
 let R (u:Add1) n: Add1:= ⟨u.val∘v u n,u.property.comp (hv ..)⟩
 let Z (n:ℕ) := Nat.rec (motive:=fun _=>Add1) ⟨id,strictMono_id⟩ (fun n u=>R u n) n
 let g(n:ℕ):=(Z n).val n
 have ht : StrictMono g:=by
    apply strictMono_nat_of_lt_succ; intro n; change _ < (Z n).val (v _ n (n+1)); exact (Z n).property (lt_of_lt_of_le (Nat.lt_succ_self _) ((hv (Z n) n).id_le _))
 have p(i n:ℕ)(w:i≤n)(y:ℕ) : ∃ z:ℕ,y≤z∧ (Z n).val y=(Z i).val z:=by
    induction n,w using Nat.le_induction generalizing y with
    | base=>exact ⟨y,le_rfl,rfl⟩
    | succ n w ih=> let m:=v (Z n) n y; obtain ⟨z,t,e⟩:=ih m; exact ⟨z,le_trans ((hv ..).id_le y) t,e⟩
 refine ⟨g,ht,fun a=>?_⟩
 obtain ⟨n,rfl⟩:= H a; let x:= n+1
 choose w q using (fun i:ℕ=>p x (i+x) (Nat.le_add_left ..) (i+x))
 let u(i:ℕ):=w (i-x)
 refine e _ u _ _ ?_ ?_ (U (Z n) n) -- arg order
 · apply Filter.tendsto_atTop.2; intro i; filter_upwards [eventually_ge_atTop i,eventually_ge_atTop x] with j v k; have he:= (q (j-x)).1; rw [Nat.sub_add_cancel k] at he; exact le_trans v he
 filter_upwards [eventually_ge_atTop x] with i h; have he:= (Nat.sub_add_cancel h); change (Z i).val i=(Z x).val (u i)
 have hv:= (q (i-x)).2; rw [he] at hv; exact hv
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
