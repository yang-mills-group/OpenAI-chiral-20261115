import YM.Corona.Fit
set_option autoImplicit false
set_option linter.flexible false
noncomputable section
namespace YM.Lattice.Corona
open Function Finset
open scoped BigOperators
variable {n:Side} {I:Type}[DecidableEq I]
-- cardinal packing for tour timing length.e 
lemma timings (D:Finset I)(f:I→ℕ)(N a:ℕ)(H:0<a)(p:∀ i∈D,f i≤N)(h:∀ i∈D,∀ j∈D,i≠j→ f i ≤ f j→ a ≤ f j-f i) : (D.card-1)*a≤N:=by
 suffices D.Nonempty → (D.card-1)*a≤N by
    by_cases h:D.Nonempty; exact this h; simp [not_nonempty_iff_eq_empty.mp h]
 intro he
 induction d : D.card generalizing D f N with
 | zero=> exact ( (card_pos.mpr he).ne' d).elim
 | succ k ih=>
   obtain ⟨i,hI,hi⟩:= exists_min_image D f he
   let U:= D.erase i
   have hp:U.card=k:=by rw [card_erase_of_mem hI,d]; omega
   by_cases hk:k=0; · simp [d,hk]
   have he':U.Nonempty:= card_pos.mp (by omega)
   let g(b:I):= f b-a
   have hy(j:I)(v:j∈U): a≤f j:=by obtain ⟨s,t⟩:= mem_erase.mp v; exact (h _ hI _ t s.symm (hi j t)).trans (Nat.sub_le ..)
   obtain ⟨j,hj⟩:=he'
   have hN:a ≤ N:=(hy j hj).trans (p _ (mem_erase.mp hj).2)
   have ht:= ih U g (N-a) (fun j v=> Nat.sub_le_sub_right (p j (mem_erase.mp v).2) a) (fun j s i' t e v=>?_) (show U.Nonempty from ⟨j,hj⟩) hp
   · rw [Nat.add_sub_cancel] -- D.card-1
     have hEq:k*a=(k-1)*a+a:=by conv_lhs=> rw [←Nat.sub_add_cancel (show 1 ≤ k by omega),Nat.add_mul,one_mul]
     omega
   have h1:=hy j s; have h2:=hy i' t
   have hv:= h j (mem_erase.mp s).2 _ (mem_erase.mp t).2 e (by unfold g at v; omega)
   unfold g; omega

lemma separated_read {A:Support n}{Q:Finset I}{o:I→Site n}{b:ℕ}(H:∀ i∈Q,o i∈A)(hp:4≤b)(p:∀ i∈Q,∀ j∈Q,i≠j→b^3≤ separation (o i) (o j)) : (Q.card-1)*b^2 ≤ 12*coverNumber b A:=by
 obtain ⟨D,h,hD⟩:=coverNumber_realized b A
 obtain ⟨N,e,R,hR,hE⟩:= ring_path _ (halo_ship _ h.2)
 have he(i:↥Q):∃ t≤N,separation (R t) (o i)≤b:=by
    obtain ⟨a,h,v⟩:=halo_spec.mp (h.1 (H i i.2)); obtain ⟨t,f,hz⟩:=hE a h; exact ⟨t,f,hz.symm ▸ v⟩
 choose f f₁ f₂ using he
 let K:= b^3-2*b
 have hx:2*b<b^3:=by calc
    _ < 16*b:=Nat.mul_lt_mul_of_pos_right (by decide) (by omega)
    _ ≤ b^3:=Nat.mul_le_mul_right b (Nat.pow_le_pow_left hp 2)
 have hz:= timings (univ:Finset ↥Q) f N K (by unfold K; omega) (fun i _=>f₁ _) (fun i _ j _ hi hj=>?_)
 · rw [card_univ,Fintype.card_coe] at hz; unfold K at hz; rw [←hD]; -- inequality a = b³-2b ≥ b³/2
   have h3: b^2 ≥ 16 := Nat.pow_le_pow_left hp 2
   have hu (q:ℕ):q*b^2*b ≤2*(q*(b^3-2*b)):=by
      rw [Nat.mul_assoc,←pow_succ]
      have hu:b^3≤2*(b^3-2*b):=by nlinarith only [hx.le,Nat.sub_add_cancel hx.le,Nat.mul_le_mul_right b h3,hp]
      exact (Nat.mul_le_mul_left q hu).trans_eq (by ring)
   have hd':(b+b+1)+(b+b+1) ≤6*b:=by omega
   refine Nat.le_of_mul_le_mul_right (c:=b) ?_ (by omega)
   calc _ ≤ 2*((Q.card-1)*(b^3-2*b)):=hu _
        _ ≤2*N:= Nat.mul_le_mul_left _ hz
        _ ≤2*(D.card*(6*b)):=Nat.mul_le_mul_left _ (e.trans (Nat.mul_le_mul_left _ hd'))
        _ = _:=by ring
 let I:=R (f i); let J:=R (f j)
 have hv:separation I J ≤ f j-f i:=path_span hR _ _ hj (f₁ j)
 have h1:separation I (o i)≤b:=f₂ i; have h2:separation J (o j)≤b:=f₂ j
 rw [separation_comm] at h1
 have h3:=separation_triangle I J (o j); have h4:=separation_triangle (o i) I (o j)
 have h5:b^3 ≤ separation (o i.val) (o j.val):=p i i.2 j j.2 (fun u=>hi (Subtype.ext u))
 unfold K; omega
end YM.Lattice.Corona
