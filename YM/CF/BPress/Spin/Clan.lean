import YM.CF.BPress.Spin.Stater
/-! Lemma B-Cpass. Clans purchased with a numerical radius already including
 the margin of not belonging literally to the path. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin.Hole
open Function Filter NormedSpace Finset Lattice Fock SU Lat Cube Tenant Branch Tulip Scroll Dial Thera Nacre Laic Paint Eye Pledge Stride Quad Blank Cellar Cellar.Pass
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{c d σ κ:ℝ}{A:Raw (OpenW N d) (Single N)}{R:ℕ}{P:Pledge}
def Secret (S:Support N)(U:Paint (More N))(σ δ:ℝ)(R:ℕ): Prop:= ∃ X:Op Slot, ‖X‖≤σ ∧ ∀ x:Site N,node x∈Lattice.halo R (wings S)→ ‖U (node x)-X‖≤ δ -- tune ambiguity
-- Clan expressed as one matrix for each p in marked bits.
def Census (S:Support N)(U:Paint (More N))(σ r:ℝ)(R:ℕ):Prop:=∀ x:Site (More N),x∈wings S→∃ X:Op Slot,‖X‖≤σ∧∀ i:Site N,i∉S→separation x (node i)≤R→ ‖U (node i)-X‖≤ r
lemma news_norm (X:Support (More N)): (news X).card≤ X.card:=by rw [←card_image_of_injective _ (needle (N:=N))]; exact card_le_card (image_subset_iff.mpr fun i p=> (mem_filter.mp p).2)
lemma compare (x y: Painted A c σ)(i:Site (More N))(k:ℕ){ε:ℝ}(v:2*k < (More N).val)(p:x.p=y.p)(t:0≤ε)(u:chord.Close x.val.1.val y.val.1.val (bay (terr _) i k) ε)(H:∀ j:Site N, separation i (node j)≤ k→ ‖x.path (node j)- y.path (node j)‖≤ε) : let S:=bay (terr _) i k; (Painted.turn A c σ).eval S x y ≤ (5*ν k^4)*ε:=by
 intro S; have he(S:Support (More N)):(∑ j∈ news S,if decide (j∈ x.p) ≠ decide (j∈y.p) then (1:ℝ) else 0)=0:=by simp [p]
 dsimp only [Painted.turn]; rw [he,add_zero]
 have hk:(S.card:ℝ)=ν k^4:=by unfold S ν; rw [volume _ v]; push_cast; ring
 apply (add_le_add (invitation.size (S:=S) t u) (sum_le_sum (g:=fun _=>ε) (fun j (hj:j∈news S)=> H j ((bay_mem _).mp (mem_filter.mp hj).2)))).trans; rw [sum_const,nsmul_eq_mul]; apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_right (show ((news S).card:ℝ) ≤S.card by exact_mod_cast news_norm S) t) _); rw [hk]; exact le_of_eq (by ring)
lemma smooth_zero {x:OpenW N d} (p:IsStarProjection (A x)) (u:ℝ): smoothP (pos (∅:Support N)) (neg ∅) (loose ∅) (A x) u=A x:=by
 obtain ⟨a,b,t⟩:= (none (N:=N)); unfold smoothP; rw [a,b,t]; let W:= A x; have he: Cellar.Pass.slide 0 0 1 W u=W:=by
    unfold Cellar.Pass.slide; have hm: rent1 0 W=0:= by simp [rent1,Trans.beam]
    unfold rent0 coeff0; rw [hm]; simp
 rw [he]; exact (Trans.Ready.atSelf p).2
variable (K: Painted A c σ)
-- Near case alternatives
inductive Duty (x:Painted A c σ)(t δ ρ:ℝ)(R:ℕ):Prop
 | upfront : Secret x.p x.path σ δ R→ Duty x t δ ρ R
 | ended : t=0→Census x.p x.path σ ρ R→ Duty x t δ ρ R

namespace Lease
variable {Q: Raw (OpenW N d) (Single N)} {U:Form N (Painted A c σ)} {κ η δ t r:ℝ}
lemma erase (p:∀x,IsStarProjection (A x))(h:‖wash K.trueA (coupling K.path)‖≤ r) {v:ℕ} (f:∀ z w: Painted A c σ,∀B:Support (More N),(∀ i∈ B,(Painted.turn A c σ).eval (bay (terr _) i v) z w≤δ)→ ‖look (home N) B*(z.tease t-w.tease t)‖≤η)(u:0≤δ)(x:Site (More N))(l:ℕ)(g:Disjoint (bay (terr _) x (l+v)) (wings K.p)):
 ‖eye (home N) x l*K.tease t‖≤ η+r:=by
 let Y: Painted A c σ:= ⟨(K.val.1,∅,K.path),meets0 _ _,K.property.2⟩; let B:= eye (home N) x l; let S:=bay (terr (More N)) x (l+v)
 have hx: ‖Y.tease t‖≤r:=by unfold Painted.tease; change ‖leak (smoothP (pos (∅:Support N)) (neg ∅) (loose ∅) (A (K.val.1)) _) K.path‖≤_; rw [smooth_zero (p _)]; exact leak_bound (p _) _ _ h
 apply (norm_le_norm_sub_add _ (B*Y.tease t)).trans; change ‖B*K.tease t-B*Y.tease t‖+_ ≤ _; rw [←mul_sub]; refine add_le_add (f K Y _ (include_patch (Painted.turn A c σ).stage (w:=l) (k:=v) (o:=x) rfl K Y ?_)) ((norm_strip ..).trans hx)
 have hk i (p:i∈news S): i∉K.p:=fun k=> disjoint_left.mp g (mem_filter.mp p).2 (mem_image_of_mem node k)
 have he (i) (p:i∈news S): i∉Y.p ∧ decide (i∈K.p)=decide (i∈Y.p):= by rw [decide_eq_false (hk i p)]; change i∉ (∅:Support N) ∧ false = _; simp [Y,Painted.p] -- spacing
 change (Painted.turn A c σ).eval S K Y ≤ _; dsimp only [Painted.turn]; rw [invitation.agrees (fun i _=> rfl),show Y.path= K.path from rfl, zero_add, Finset.sum_eq_zero (f:=fun _=>_) (?_)] -- tune
 · rw [zero_add, Finset.sum_eq_zero (fun i hi=>by rw [(he i hi).2]; simp)]; exact u
 intro i hi; simp
set_option maxHeartbeats 360000 in
lemma rise (p:∀x,IsStarProjection (A x))(x₀:OpenW N d)(q:x₀.val=1)(hB:Boots (A x₀))(s0:Meets c K.p (A x₀))(hc:0<c)(hC:c≤1){v:ℕ} (f:∀ z w: Painted A c σ,∀B:Support (More N),(∀ i∈B,(Painted.turn A c σ).eval (bay (terr _) i v) z w≤δ)→ ‖look (home N) B*(z.tease t-w.tease t)‖≤η)(u:0≤κ)(s:0≤r)(x:Site (More N))(l:ℕ)(ht:‖t‖≤1)(hk:(5*ν (l+v)^4)*κ ≤ δ)(H:2*(l+v)< (More N).val)(h:2*(l+v)≤R) (W:Uprice R κ K.p K.val.1.val)(g: Duty K t κ r R)(w:¬Disjoint (bay (terr _) x (l+v)) (wings K.p)):
 ‖eye (home N) x l*K.tease t‖≤ η+r:=by
 let S:=bay (terr (More N)) x (l+v); obtain ⟨o,b,hP⟩:=Finset.not_disjoint_iff.mp w; have he i (hi:i∈ S):separation o i≤R:= (separation_triangle o x i).trans ((Nat.add_le_add ((separation_comm ..).le.trans ((bay_mem _).mp b)) ((bay_mem _).mp hi)).trans (by omega))
 have hv:S ⊆ Lattice.halo R (wings K.p):=fun i hi=> halo_spec.mpr ⟨o,hP,he i hi⟩; let F:=eye (home N) x l
   -- moving
 have attempt (L:Paint (More N))(tL: MatLite L σ)(uL:∀ i:Site N,node i∈ S→ ‖K.path (node i)- L (node i)‖ ≤ κ) (uA: ‖leak (smoothP (pos K.p) (neg K.p) (loose K.p) (A x₀) t) L‖≤r) : ‖F*K.tease t‖≤ η+r:=by
    let Y:Painted A c σ:=⟨(x₀,K.p,L),s0,tL⟩
    have hy:(Painted.turn A c σ).eval S K Y≤δ:= (Hole.compare K Y _ _ H rfl u (by change chord.Close _ x₀.val _ _; rw [q]; exact chord.Close.smaller _ _ hv W) (fun i hi=> uL i (bay_mem _|>.mpr hi))).trans hk
    apply (norm_le_norm_sub_add _ (F*Y.tease t)).trans; rw [←mul_sub]; exact add_le_add (f K Y _ (include_patch (Painted.turn A c σ).stage (w:=l) (k:=v) (o:=x) rfl K Y hy)) ((norm_strip ..).trans uA)
 have hX:= passed (p _) hc hC s0; cases g with
 | upfront E=> obtain ⟨J,h,H⟩:=E; exact attempt (fun _=>J) (fun _=>h) (fun i p=>H i (hv p)) (le_trans (by rw [hole_free hB hX J t ht, norm_zero]) s)
 | ended hk g=>
    obtain ⟨J,I,K₀⟩:=g o hP; let Y(i: Site (More N)):= if i∈S then K.path i else J; have hy i (p:node i∈S): ‖K.path (node i) - Y (node i)‖≤κ:=by rw [show Y (node i)=_ from if_pos p,sub_self,norm_zero]; exact u
    have hd:∀i:Site N,i∉K.p→ ‖Y (node i)-J‖≤r:=by
       intro i p; unfold Y; split; exact K₀ i p (he _ ‹_›); rw [sub_self,norm_zero]; exact s
    have hu:= back_cost (A:=A x₀) (S:=K.p) (c:=c) hX hB Y J r s hd
    apply attempt Y _ hy _
    · exact fun i=>by unfold Y; split; exact K.property.2 i; exact I
    rw [hk]; exact hu
end Lease

theorem clan_control (P:Pledge) (s:0<c)(v:c≤1)(σ:ℝ)(a:ℝ)(p:0≤a)(q:a<1) : ∃ (d δ:ℝ)(R n:ℕ), a<d∧d<1 ∧ 0<δ ∧ ∀{N:Side} (e:ℝ)(A: Raw (OpenW N e) (Single N)), n≤ N.val→(∀x,IsStarProjection (A x))→(AtW N e).Comes P A→ ∀ x: Painted A c σ,‖wash x.trueA (coupling x.path)‖≤ a→ ∀ x₀: OpenW N e,x₀.val=1→Boots (A x₀)→ Meets c x.p (A x₀)→ Uprice R δ x.p x.val.1.val→ ∀ t:ℝ, ‖t‖≤1→ Duty x t δ a R→ ‖x.tease t‖≤d := by
 obtain ⟨d,u,h⟩:= exists_between q; let r:=(d-a)/2; have hr:0<r:=half_pos (sub_pos.mpr u); let τ:=r+a; have e:τ<d:=by unfold τ r; linarith; -- semicolon
 obtain ⟨T,t⟩:= leak_budget P s v σ; obtain ⟨w,m,H⟩:= (pledge_lift T (show 0≤τ from add_nonneg hr.le p) e).exists; obtain ⟨k,c',C,g⟩:= latticeFieldEstimates_price T hr
 let b:=5*ν (w+k)^4; let δ:= c'/b; have hb:0<b:=mul_pos (by norm_num) (pow_pos vol_pos _); have hc:0<δ:=div_pos C hb
 refine ⟨d,δ,2*(w+k),2*(w+k)+m+1,u,h,hc,?_⟩; intro N e A L n p' x M z z' B X Y v' l q'; let U:=Painted.turn A c σ; have hm:(More N).val=N.val*2:=rfl; let E:= fun y:Painted A c σ=>y.tease v'
 have hg:= t n p' v' l; apply H (More N) (by omega) (b:=U.stage) rfl E hg x; intro o; by_cases h:Disjoint (bay (terr (More N)) o (w+k)) (wings x.p)
 · exact Lease.erase x n M (g hg) C.le _ _ h
 exact Lease.rise x n z z' B X s v (g hg) hc.le p _ _ l (mul_div_cancel₀ c' hb.ne' |>.le) (by omega) le_rfl Y q' h
end YM.CF.BPress.Spin.Hole
