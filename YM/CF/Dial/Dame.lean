import YM.CF.Dial.Dome
import YM.CF.Dial.Chair
/-! Threshold binder and special operation kit. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
abbrev Ego:=∀ {N P:Side}, Ratio N P→ Sew N P → Prop
def Still (L:Side)(H:Ego):= ∃ e:ℝ,0<e ∧ ∃ k:ℕ,∀{N P:Side}(G:Ratio N P), G.count=L→ k≤N.val→∀ U:Sew N P,Gild G U e→ H G U
abbrev VoteK:=∀ {N P:Side}, Ratio N P→ Bale N P → Prop
def Tills (L: Side)(H:VoteK):= ∃ e:ℝ,0<e∧∃ k:ℕ,∀ {N P:Side}(G: Ratio N P),G.count=L→ k≤N.val→ ∀ U:Bale N P,U∈zoneP G e→H G U
variable {N P:Side}{L : Side}{ι:Type*}{H B:Ego}{F X:VoteK}
lemma Still.plus (p: Still L @H)(h:Still L @B):Still L (fun G x=> H G x ∧ B G x):=by
  obtain ⟨a,p,r,A⟩:=p; obtain ⟨b,h,s,K⟩:=h
  exact ⟨min a b,lt_min p h,max r s, fun G he hg x hy=>⟨A G he ((le_max_left ..).trans hg) x (hy.breadth G (min_le_left ..)),K G he ((le_max_right ..).trans hg) x (hy.breadth G (min_le_right ..))⟩⟩ -- explicit lambdas with implicit binder
lemma Still.forward(p:Still L @H)(g:∀ {N P:Side}(G:Ratio N P), G.count=L→∀ x,H G x→ B G x): Still L @B:= by obtain ⟨a,p,t,A⟩:=p; exact ⟨a,p,t,fun G he hv x h=> g G he x (A G he hv x h)⟩
lemma Tills.plus (p:Tills L @F)(h:Tills L @X):Tills L fun G x=> F G x∧X G x:=by
  obtain ⟨a,p,r,A⟩:=p; obtain ⟨b,h,s,K⟩:=h
  exact ⟨min a b,lt_min p h,max r s,fun G he hg x hz=>⟨A G he ((le_max_left ..).trans hg) x (portland G hz (min_le_left ..)), K G he ((le_max_right ..).trans hg) x (portland G hz (min_le_right ..))⟩⟩
lemma Tills.forward (p:Tills L @F)(g:∀ {N P:Side}(G:Ratio N P), G.count=L →∀ x,F G x→ X G x): Tills L @X:=by obtain ⟨a,p,t,A⟩:=p; exact ⟨a,p,t,fun G he hv x h=>g G he x (A G he hv x h)⟩
lemma Tills.gilded(p:Tills L @F): Still L (fun G x=> F G (post x)):=by obtain ⟨a,p,t,A⟩:=p; exact ⟨a,p,t,fun G he hv x h=>A G he hv _ ⟨x,h,by simpa⟩⟩
lemma Still.stamp(p:Still L @H):∃ k:ℕ,∀ {N P:Side}(G:Ratio N P),G.count=L→ k≤N.val→H G (1,vacuumW P,vacuumW N):=by obtain ⟨a,h,k,T⟩:=p; exact ⟨k,fun G he hv=> T G he hv _ (tone G a h)⟩
variable {A: Chop ι}{u v:AxisT}
lemma interest_g (p: Interest L A): Tills L (fun G x=> ∀ i,IsUnit (A i G x)):=by obtain ⟨a,h,k,T⟩:=p; exact ⟨a,h,k,fun G he hv x p i=>T i G he hv x p⟩
lemma BoxD.assets (h:BoxD L u v A): ∃ c:ℝ,0<c ∧ Tills L (fun G x=>∀ i, ‖A i G x‖≤c):=by obtain ⟨a,c,e,p,q,d,n,H⟩:=h; exact ⟨c,q,e,d,n,fun G he hv x h i=> (H i G he hv).lib.boundOp p.le ⟨x,h⟩⟩
-- interpolation log analytic on vacuum centers. telescope on real values where needed.
lemma ink (h:BoxD L u u A) {c:ℝ}(p:0<c)(g:c<1)(H:Still L (fun G x=>∀ i,‖A i G (post x)‖ ≤ c)): BoxD L u u (fun i _ _ G x=> pencil (A i G x)):=by
  obtain ⟨l,W⟩:=H.stamp
  obtain ⟨a,C,e,ha,hC,he,v,H⟩:=h
  obtain ⟨d,m,K,t,q,r,-,hK,hT,ht,n,F⟩:= awaken (A:=A) (k:=max v l) (fun i _ _ G h hx=> H i G h ((le_max_left ..).trans hx)) ha hC he p g (fun i _ _ G h hv=> W G h ((le_max_right ..).trans hv) i)
  let f (n:ℕ):= K*t^(n+1); have hf:Summable f:=((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hT.le ht)).mul_left K
  apply boxify (C:=∑' j,f j) (k:=n) ?_ q r; intro i N P G hU hV
  have hy : ∀ k:ℕ,Crown (badge (zoneP G m)) (rope G u m) (rope G u m) d (f k) (fun x=> bcoef k • A i G x.val^(k+1)):=by
    intro k
    have ht(y:Op (Iota G)): bcoef k • y=(↑(bcoef k):ℂ) • y:=by ext; simp [Complex.real_smul]
    have hb:= (F (k+1) i G hU hV).scale (↑(bcoef k):ℂ); -- explicit k tune
    simp_rw [ht]; exact hb.books (show _≤f k by rw [Complex.norm_real]; exact mul_le_of_le_one_left (by positivity) (bc_norm k)) -- ht x?
  exact Crown.tsK f hy q.le hf
end YM.CF.Dial
