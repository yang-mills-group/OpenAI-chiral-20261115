import YM.CF.BPress.Spin.Window
/-! Row-restricted op variation comparing to free in near regions. Uses only its performance with a support budget (no smooth assumptions/injective outside). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter NormedSpace Finset Fock Branch Lattice Tenant Pledge
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
namespace Eye
variable {I D:Type}[TopologicalSpace D][Fintype I][DecidableEq I]{N:Side}{a:ℝ}{k w :ℕ}{b:Stage (Site N) I D Empty}{P:Pledge}
lemma side (X:Support N)(F:Seal (Site N)→ Raw D I)(K:Seal (Site N)→ Toll I)(h:∀ S,Ticket (solo b) (solo b) S (K S) (F S))(g:Ledger P.rate K P.price)(x y:D)(p:0≤a)
    (l:∀ i∈ X,b.eval (bay b.F i k) x y≤a) : ‖look b.home X*(lop F k x-lop F k y)‖≤a*P.price:=by
 rw [mul_comm a]; refine schur (fun i j=>saleM P.rate K i j*a) _ _ (mul_nonneg g.posP p) (fun i j=>?_ ) (fun i=>?_ ) (fun i=>?_)
 · rw [look_left]; by_cases hi:b.home i∈X; swap; · rw [if_neg hi,norm_zero]; exact mul_nonneg (sale_nn (fun i=>(h i).nonn) _ _ _) p
   rw [if_pos hi, lop,lop,Matrix.sub_apply,Matrix.sum_apply,Matrix.sum_apply,←sum_sub_distrib]; apply (norm_sum_le ..).trans
   unfold saleM; rw [sum_mul]
   apply le_trans ?_ (sum_le_sum_of_subset_of_nonneg (s:=Branch.ch (Site N) k) (subset_univ _) (fun S _ _=>mul_nonneg (mul_nonneg (rent_pos ..).le ((h S).nonn i j)) p))
   apply sum_le_sum; intro S hv; let H:= (h S).expo i j; by_cases hy: K S i j=0; · exact (H.variation x y).trans_eq (by rw [hy,mul_zero,zero_mul,zero_mul])
   obtain ⟨z,s,t⟩:= H.triggered hy; have hh: S ⊆ bay b.F (b.home i) k:= fun d hd=> bay_mem k|>.mpr ((z.lim _ s _ hd).le.trans (mem_filter.mp hv).2.le); exact (H.variation x y).trans (mul_le_mul (le_mul_of_one_le_left H.positive (rent_one P.pos.le _)) ((b.includeV hh x y).trans (l _ hi)) (b.pos ..) (mul_nonneg (rent_pos ..).le H.positive))
 · rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (g.rows i) p
 rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (g.cols i) p
lemma norm_strip (u:I→Site N)(X:Support N)(A:Op I):‖look u X*A‖≤‖A‖:= (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (look_one ..))

lemma latticeFieldEstimates_price (P:Pledge)(p:0<a) : ∃ (k:ℕ) (d:ℝ), 0<d ∧ ∀{I D:Type}[TopologicalSpace D][Fintype I][DecidableEq I]{N:Side}{b:Stage (Site N) I D Empty}{f: Raw D I}, P.Costs b f→∀x y:D,∀X: Support N,(∀ i∈X,b.eval (bay b.F i k) x y≤d)→ ‖look b.home X*(f x-f y)‖≤a := by
 let e:=a/4; have hu:0<e:=div_pos p (by norm_num); obtain ⟨k,h⟩:= (tailBuys P hu).exists
 let d:=e/P.price; have hd:0<d:=div_pos hu P.bought; refine ⟨k,d,hd,?_⟩; intro I D _ _ _ N b f w x y X L; obtain ⟨F,K,pF,uF,gF⟩:=w
 let A:=look b.home X; let B:= lop F k; have he : f x-f y=(B x-B y)+((f x-B x)-(f y-B y)):=by abel
 have ht(x):‖A*(f x-B x)‖≤e:= (norm_strip ..).trans (((lip_tail F K pF uF gF P.pos.le).boundOp (half_pos P.pos).le x).trans h)
 rw [he,mul_add,mul_sub _ (f x-_)]; apply (norm_add_le ..).trans; apply (add_le_add (side X F K pF uF x y hd.le L) ((norm_sub_le ..).trans (add_le_add (ht _) (ht _)))).trans; unfold d; rw [div_mul_cancel₀ _ P.bought.ne']; unfold e; linarith
lemma include_patch (b:Stage (Site N) I D Empty) (e:b.F=terr _) {o:Site N} (x y:D){C:ℝ}(h:b.eval (bay (terr N) o (w+k)) x y≤C): ∀ i∈ bay (terr N) o w,b.eval (bay b.F i k) x y≤ C:=by
 intro i t; apply le_trans (b.includeV _ x y) h; rw [e]; intro j u; exact bay_mem _ |>.mpr (((terr N).tri o i j).trans (Nat.add_le_add ((bay_mem _).mp t) ((bay_mem _).mp u)))
variable {G: Type}{b':Stage (Site N) I D G}
lemma gauge_norm (g:G)(S: Tag b')(t:Tag b')(X:Support N)(A:Op I) : ‖look b'.home X*((S.run g).val*A*star (t.run g).val)‖=‖look b'.home X*A‖:=by
 change ‖strip b' X*_‖=‖strip b' X*A‖; rw [←mul_assoc,←mul_assoc, strip_tag,mul_assoc _ (strip b' X)]; exact (CStarRing.norm_mul_coe_unitary _ (star (t.run g))).trans (CStarRing.norm_coe_unitary_mul (S.run g) _) -- coe star simp
end Eye
end YM.CF.BPress.Spin
