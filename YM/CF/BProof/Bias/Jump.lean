import YM.CF.BProof.Bias.Hive
/-! AP magnetization rigidity in any admissible aperture. Exercises both directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint
open Fir Laurent Rush Bloch Next.Free BZ Real
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}
def hopV (N:Side)(i:Axis): UNI (Single N):=⟨axisShift N i,wing_unit _⟩
lemma relic_comm (i:Axis)(F: Globe N): Commute (axisShift N i) (relic F):=by rw [relic_shift]; unfold Commute SemiconjBy; rw [relic_mul,relic_mul]; apply congrArg; funext k; simp only [Pi.mul_apply,Algebra.smul_mul_assoc,one_mul, Algebra.mul_smul_comm,mul_one]
lemma slice_move (p:Per N): slice ht p * axisShift N 0=axisShift N 0 * slice ht (p+1):=by
 ext i j; rw [timeL,timeS,axis_shift]; dsimp only; by_cases g:advance 0 (fsite i)=fsite j; rw [if_pos g]; have he: ht j=ht i+1:=by unfold ht; rw [←g]; simp [advance]
 simp [he]
 simp only [if_neg g, ite_self] -- tune
lemma same_shift (x y:Per N){T:Op (Single N)}(g:Commute (axisShift N 0) T): ‖slice ht x*T*slice ht y‖=‖slice ht (x+1)*T*slice ht (y+1)‖:=by
 let U:=hopV N 0; rw [← CStarRing.norm_mul_coe_unitary _ U, ← CStarRing.norm_coe_unitary_mul U (slice ht (x+1)*T*slice ht (y+1))]; congr 1; change _*U.val=U.val*(_*_); rw [mul_assoc _ _ U.val]; dsimp only [U,hopV]; rw [slice_move,mul_assoc, ←mul_assoc T, g.symm.eq,←mul_assoc,←mul_assoc,slice_move]; simp_rw [mul_assoc]; -- tune
variable {R J:Finset (Per N)}{x y:Per N}{j t r n:ℕ}(M:Male)(w:Per N){e b v δ:ℝ}
lemma shifts (k x:Per N)(u:‖slice ht x*AngleZ j M w*slice ht (x+k)‖≤e): ‖swipe ht k (AngleZ j M w)‖≤e:=by
 let T:=AngleZ j M w; have he: Commute (axisShift N 0) T:=(relic_comm 0 _).mul_right (relic_comm 0 (thinK (Label 1 w))) -- tune
 let f(t:Per N):= ‖slice ht t * T * slice ht (t+k)‖; have htA(t:ℕ): f (x+t)=f x:=by
    induction t with
    | zero=> simp
    | succ t ih=> rw [Nat.cast_add,Nat.cast_one,← add_assoc]; refine Eq.trans ?_ ih; unfold f; rw [same_shift (T:=T) (x+(t:Per N)) (_+k) he,add_right_comm (x+(t:Per N)) 1] -- tune
 apply swipe_small Bias.ht ((norm_nonneg _).trans u) -- ht shadow
 intro t; change f _≤_; exact (show f t=f x from by rw [← htA (along x t),add_along]).trans_le u
-- layout allows both D side orders
structure Vent (R J X:Finset (Per N))(t r n:ℕ): Prop where
    owns(k: Per N)(p:k∈ young N t r) : ∃ x∈ R, x+k∈ R ∧ ((x∈ J ∧ x+k∉ J)∨ (x∉ J∧ x+k∈J)) ∧ cent (x+k) n ⊆ X
variable (h:1≤j)
lemma comm_flip : commP j M R Jᶜ= -commP j M R J:=by unfold commP; rw [timeN]; noncomm_ring
lemma seat_norm {X Y:Finset (Per N)}(h:X⊆ Y)(A:Op (Single N)): ‖A*Seat X‖≤‖A*Seat Y‖:=by apply le_trans ?_ (timeUB (N:=N) ht X (A*Seat Y)); rw [mul_assoc,time_sub ht h]
-- No need a strong cost on T ε. call Budget with prechoice exogenous.
variable (p: Stint.Pay)
include h
private lemma dialog (q:0≤v)(s:ℝ)(e:0<s): ∃ u:ℝ,0<u∧ (v+2)*dialect u u v ≤ s:=by
 let f(u:ℝ):=(v+2)*dialect u u v; have he:Continuous f:=by unfold f dialect; fun_prop
 have hs:∀ᶠ x in 𝓝[>] (0:ℝ), f x < s:=he.continuousWithinAt.eventually (gt_mem_nhds (show f 0 < s by simpa [f,dialect])); exact (hs.and (show ∀ᶠ x in 𝓝[>] (0:ℝ),0<x from self_mem_nhdsWithin)).exists.imp (fun i p=> ⟨p.2,p.1.le⟩)
lemma broken (p:Stint.Pay)(t:ℕ):∃ r n k:ℕ,∃ u:ℝ,0<u∧ t≤r ∧∀ {N:Side},k≤N.val → ∀ (R J X:Finset (Per N))(F:Vent R J X t r n)(M:Male) {δ:ℝ}(b:Free δ j M R), (∀ i:ℕ, Near ht i (tailPay p i) (redP j M N))→ u < ‖commP j M R J*Seat X‖:= by
 obtain ⟨b,v,k,g,f,e,P⟩:= bankable h t p; obtain ⟨r,s,hR,hS,H⟩:= accessible p t g f e (show 0<(1:ℝ) by norm_num) 1 (by norm_num); -- tune purchase initially large
 obtain ⟨u,x,w⟩:= dialog h e s hS; obtain ⟨n,m,-,-,Q⟩:=accessible p r g f e (e:=1) (by norm_num) u x; refine ⟨r,n,k,u,x,hR,?_⟩; intro N f R J X V M δ D W; obtain ⟨w',hP⟩:=P f; obtain ⟨h,H'⟩:= hP M W; -- h clash
 by_contra! hu; apply H'; apply (H h).2; intro i y; obtain ⟨z,a,b',l,t⟩:= V.owns i y; apply shifts M w' i z; have hl:‖AngleZ j M w'‖≤v:=by obtain ⟨A,B,h,t,U,b⟩:=h.leg; exact U
 have hb:= (Q h).1; have he:= (seat_norm t _).trans hu; apply le_trans _ w; rcases l with ⟨p,f⟩|⟨p,f⟩; exact sailG M (by assumption) D w' b' a f p hl hb he; apply sailG M (by assumption) D w' b' a (notMem_compl.mpr f) (mem_compl.mpr p) hl hb ; rw [comm_flip,neg_mul,norm_neg]; exact he -- tune
end YM.CF.BProof.Bias
