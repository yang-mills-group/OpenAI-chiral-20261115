import YM.CF.BProof.Bias.Leather
/-! eq:B-tbias quantitatively over rooted nodes assigned to revenue block. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint Wick Hearth
open Fir Laurent Rush Bloch Next.Free BZ Real Tape Mapping Mapping.House Angular Hero Dream Trek
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator Hearth Classical
attribute [local instance] opCStarAlgebra
variable {N C:Side}(f:Ratio C (More N))(Y: Yard (More N))(i:Block Y C)
def CircleR (K:ℕ) := univ.filter fun x:Site (More N)=> addr Y f x=i ∧ ∃ j,Y.Vic j K (time x)
lemma circle_card (K:ℕ)(g:2*K+1< Y.long) : (CircleR f Y i K).card ≤ (Y.short+2*K+1)*f.count.val^3:= senior Y f K i g -- tune
abbrev dyads := Fin (f.count.val/2)
lemma splitZ(z:Per C): ∃ q:dyads f→Per N, Injective q ∧∀ e,block f (instant (q e))=z:=by
 let Q:= dyads f; let a(e:Q):=2*e.val; have ht(e:Q): a e+1< f.count.val:=by have :=e.isLt; unfold a; omega
 obtain ⟨q,h⟩: ∃ q:dyads f→ Per N,∀ e,∃ k:ℕ,a e≤k∧ k≤a e+1∧ instant (q e)= base f z+k:=by
    let V:=nearest (N:=N); choose q p v H using fun e:Q=>V (base f z+(↑(a e+1):Per (More N))); refine ⟨q,fun e=>⟨a e+1-p e,?_,Nat.sub_le ..,?_⟩⟩; · have := v e; omega
    apply add_right_cancel (b:=(p e:Per (More N))); rw [H,add_assoc,←Nat.cast_add,Nat.sub_add_cancel]; have := v e; omega -- tune side goal needs v
 refine ⟨q,fun e t d=>?_, fun e=>?_⟩; · obtain ⟨i,w,hx,x⟩:= h e; obtain ⟨j,H,v,y⟩:=h t; rw [d,y] at x; have he:= (add_inj_nat ((v.trans_lt (ht t)).trans_le (count_le f)) ((hx.trans_lt (ht e)).trans_le (count_le f))).1 x; unfold a at *; apply Fin.ext; omega
 obtain ⟨i,w,hx,x⟩:= h e; rw [x]; exact block_add f z (hx.trans_lt (ht e))
lemma prize (x:Per N)(R:ℕ)(h:x∈area Y (House.one Y i) R)(p:2*R+1<Y.long): ∃ F:(Fin 3→dyads f)→ Site N, Injective F∧∀ k,time (F k)=x ∧ node (F k) ∈ CircleR f Y i R:=by
 choose q t v using fun j:Fin 3=>splitZ f (House.two Y i j); let u (k:Fin 3→dyads f): Space N:= fun j=>q j (k j); let F (k:Fin 3→dyads f) := join x (u k); have he(k): time (F k)=x:=rfl
 refine ⟨F,fun a b h=>?_,?_⟩; · apply funext; intro j; apply t j; exact congrFun h j.succ
 intro k; let f₁:=F k; refine ⟨he _,mem_filter.mpr ⟨mem_univ _,?_,House.one Y i,?_⟩⟩; swap
 · rw [timed,he]; exact (areaT ..).1 h
 unfold addr hide House.col; dsimp only; rw [timed,he,Posts.vic Y (House.one Y i) _ p ((areaT ..).1 h),show Grid.elder f _=House.two Y i from ?_,place_house]; funext j; unfold Grid.elder BProof.space; rw [spell]; exact v ..
variable {a b l r δ c v η:ℝ}{j:ℕ} {P: Spin.Ready j a b l r} {K D:ℕ}(z:Fin 5)(w:ℝ){F:Core j a b l r N}(x:Loft F δ c v η)
lemma dyad_le (u:4≤ f.count.val): (f.count.val:ℝ)/4≤((f.count.val/2:ℕ):ℝ):=by
 rw [div_le_iff₀ (by norm_num : (0:ℝ)<4)]; exact_mod_cast (show f.count.val≤(f.count.val/2)*4 from by omega)
lemma shack(p:ScopeP D P δ c v w K z)(e:Portrait z Y x)(t:z≠0)(u:0≤w)(g:Honor P F δ)(y:K≤N.val)(u':2*K+1< Y.long)(k:Y.short≤D)(r':4≤ f.count.val) : ∑ o∈ CircleR f Y i K,Tape.bias x o ≤ - w / 64 * (f.count.val:ℝ)^3 := by
 obtain ⟨o,h,H⟩:= p.claim g x (House.one Y i) t y (by omega) k e; obtain ⟨d,hf,t⟩:= prize f Y i o K h u'; let A:= Fin 3→dyads f; let W:= d; let V(a:A):= node (d a); have hv:Injective V:= Tenant.needle.comp hf; let T:= univ.image V; refine le_trans (b:=∑ o∈ T,Tape.bias x o) ?_ ?_; swap; -- tune API
 -- sum signs
 · unfold T; rw [sum_image]; apply (sum_le_sum (fun i _=> H _ (t i).1)).trans; rw [sum_const,nsmul_eq_mul,card_univ,show Fintype.card A=_ from (by simp [A,dyads] : Fintype.card A=(f.count.val/2)^3),Nat.cast_pow]; have he:= dyad_le f r'; apply le_trans (mul_le_mul_of_nonpos_right (pow_le_pow_left₀ (by positivity) he 3) (by linarith)); exact le_of_eq (by ring)
   exact hv.injOn
 have hp : T ⊆ CircleR f Y i K:= by intro o hx; obtain ⟨a,-,rfl⟩:= mem_image.mp hx; exact (t a).2
 rw [←sum_sdiff hp]; exact add_le_of_nonpos_left (sum_nonpos fun i _=> bias_nonpos _ _ _ x _) -- tune
end YM.CF.BProof.Bias
