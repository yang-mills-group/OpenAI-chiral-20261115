import YM.CF.BProof.Hero.X
/-! Enter X reach on connected support upgrades. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Hero
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Grid
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {c s:Side}(g:Ratio c s)

-- cost plaquette
lemma corner (x:Site s)(U:Bkg s)(i j:Axis)(h:i<j): cd SU.group (U (x,i)*U (x+step i,j)) (U (x,j)*U (x+step j,i))= SU.group.chord (faceValue U (x,⟨(i,j),h⟩)):=by
 let V:=U (x,i)*U (x+step i,j); let W:=U (x,j)*U (x+step j,i); rw [price_eq]; change cd SU.group V W=_; rw [←cd_mul_right SU.group W⁻¹,mul_inv_cancel,cd_symm,cd_one]; unfold Mag.curl V W; group
lemma Flat_of_cell (S:Set (Site s))(U:Bkg s)(d:ℝ)(p:0≤d)
 (h: ∀ (x:Site s) (i j:Axis) (p:i<j), x∈ S→x+ step i∈ S→ x+step j∈ S →x+step i+step j∈ S → group.chord (faceValue U (x,⟨(i,j),p⟩)) ≤ d): Wire.Flat SU.group U S d:=by
 intro x i j hx hi hj hh; simp only [slide4] at *; rcases lt_trichotomy i j with k|k|k
 · rw [corner x U i j k]; exact h x i j k hx hi hj hh
 · subst i; rw [cd_self]; exact p
 rw [cd_symm,corner x U j i k]; rw [add_right_comm] at hh; exact h x j i k hx hj hi hh
lemma protectedX (U:Bkg s){d:ℝ} (p:0≤d)(h: Guard U d): Wire.Flat SU.group U Set.univ (xm*d):=by
 apply Flat_of_cell Set.univ U _ (mul_nonneg xm_p.le p); intro x i j e _ _ _ _; rw [← cd_one]; let V:=faceValue U (x,⟨(i,j),e⟩); apply (scenic _ _).trans; rw [Spin.seen]; refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) xm_p.le
 · rw [cmp_sym]; unfold Cube.cmp; rw [map_one]; exact h.2 x i j e.ne
 rw [cmp_sym]; unfold Cube.cmp; rw [map_one]; exact h.1 x i j e.ne
lemma flat_m (U:Wire SU.group 4 s){r u:ℝ}{S T:Set (Site s)}(h:Wire.Flat SU.group U S r)(v:T⊆S)(p:r≤u): Wire.Flat SU.group U T u:= fun a i j h' x y z=> (h a i j (v h') (v x) (v y) (v z)).trans p
lemma calf (a:Per s)(l:ℕ)(U:Bkg s)(v:l+1<s.val)(d:ℝ)(p:0≤d)(h:Angular.Calm a l U d): Wire.Flat SU.group U (↑(BProof.strip a l)) d:=by
 let S:Set (Site s):= ↑(BProof.strip a l); have he(x:Site s)(i j:Axis)(v:i<j):True:=trivial
 apply Flat_of_cell _ U _ p; intro x i j ht hx hh hi hq; change group.chord _≤_; let z:Lattice.Face (Per s):= (x,⟨(i,j),ht⟩); have hp(k:Lattice.Face (Per s))(u:k=z) : k.1∈ S ∧ k.1+step k.2.val.1∈ S:= u ▸ ⟨hx,hh⟩
 change SU.group.chord (faceValue U z)≤_; rcases whichFace z with ⟨w,y,j,h'⟩|⟨w,y,j,h'⟩
 · rw [h']; apply h.1; exact (wet_v a l v).1 (show Wet a l (vert w y) from hp _ h'.symm)
 rw [h']; exact h.2 _ _ _ (by simpa using mem_strip.mp (show (join w y)∈BProof.strip a l from (hp _ h'.symm).1))

-- all top cells. Selection useful if preserving templates outside costs independently here.
def stack(S:Set (Site s)):= {p:Grid.Entity 4 c|∀ x,p.Mem g x→ x∈ S}
abbrev Platform(z:Cubic 4 c): Entity 4 c:= Entity.mk z Finset.univ
lemma settleS(e:4≤c.val)(S:Set (Site s)): Settle (stack g S):= fun p h q t x hx=> h x (t.sites g e hx)
lemma purePin(U:Set (Site s))(e:4≤c.val) : Settle {p : Entity 4 c | ∃ z,p.Under (Platform z)∧ Platform z∈ stack g U}:=by
 intro p v q h; obtain ⟨z,t,w⟩:= v; exact ⟨z,h.trans t,w⟩
def pin (S:Set (Site s)):Set (Entity 4 c):= {p|∃ z,p.Under (Platform z)∧Platform z∈stack g S}
-- Under entity distance with constant factor
lemma Fence (p:Entity 4 c)(x y:Site s)(hx:p.Mem g x)(hy:p.Mem g y) : separation x y≤2*g.count.val:=by rw [←Way]; exact ((Grid.triangle x (p.first g) y).trans (Nat.add_le_add (p.diameter g x hx) ((Grid.dist_symm ..).trans_le (p.diameter g y hy)))).trans (by omega)
lemma dwell (x:Site s)(hc:4≤c.val): ∃ t:Cubic 4 c,(Platform t).Mem g x:=by
 obtain ⟨z,h,v⟩:= Grid.Entity.entire (n:=4) g hc x 0; exact ⟨z,h⟩ -- name & c shadow
lemma pin_safe (S:Set (Site s))(x:Site s)(p:4≤c.val)(h:∀ y,separation x y≤2*g.count.val→ y∈ S) : Grid.Entity.chief g x∈ pin g S:=by
 obtain ⟨z,hz⟩:= dwell g x p; refine ⟨z,Grid.Entity.chief_sub g (Platform z) p x hz,fun y hy=> h _ (Fence g _ x y hz hy)⟩ -- tune
lemma cover_cost (U:Bkg s)(v:ℝ)(h:can v g.count)(A:Site s→ Ballot)(F:Set (Site s))(s:4≤c.val)(p:PaceX F U A (prie g.count))(q:Wire.Flat SU.group U Set.univ (tip g.count)):PaceX Set.univ U (expandX g (pin g F) A U) v:=by
 let V:=expandX g (pin g F) A U; have he(x:Entity 4 c):PaceX {y|x.Mem g y} U V v:= by
    apply entersX g (pin g F) A U v h Set.univ s (purePin g F s) (fun _ _ _ _=> trivial) (fun x hx=>?_) (fun x hx=>flat_m U q (Set.subset_univ _) le_rfl) x trivial; obtain ⟨z,k,u⟩:= hx; exact pace_sub A U p (fun y hy=>u _ (k.sites g s hy)) le_rfl -- tune ℕ `s : proof` shadows type s causing errors
 intro x i hx z; obtain ⟨v,t,k⟩:= Grid.Entity.entire g s x i; exact he (Platform v) x i t (by rw [←slide4]; exact k) -- tune `membership`
end YM.CF.BProof.Hero
