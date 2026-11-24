import YM.CF.BProof.Single.Port
import YM.CF.BProof.Single.Gravel

/-! B-Lspeed: locality comparison -> global. Uniform costs/order of purchases. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Spin
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Stint SU.Pair
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
-- utility corners
variable {N : Side}
lemma coverBay {x y:Site N}{w r:ℕ}(p:x∈bay (terr N) y w): bay (terr N) x r⊆bay (terr N) y (w+r):= fun i h=> (bay_mem _).mpr (((terr N).tri ..).trans (Nat.add_le_add ((bay_mem _).mp p) ((bay_mem _).mp h)))
def Air (N:Side)(a d:ℝ) := HScope.palette (iron N a d) 1
def cloudT (d:ℝ)(C:HScope N 1)(X:Bkg (More N))(h:Guard X d): Counter (More N) d × HScope N 1:= (⟨X,h⟩,C)
def cloud (Q:HScope N 1)(z:Site (More N)) : HScope N 1:=⟨fun _=> Q.val z,fun _=>Q.property z⟩ -- def change
variable {a d δ t ε:ℝ} {Q:HScope N 1}{X:Bkg (More N)}{o o':Site (More N)}
def profit (a:ℝ)(w r:ℕ) :ℝ:= let M:= (16:ℝ)*((r:ℝ)+1)^4; M* (4*priceF (w+r) 1/|a| +4*((w+r:ℕ):ℝ))
lemma profit_pos (a:ℝ)(w r:ℕ): 0≤profit a w r:=by unfold profit priceF; dsimp only; positivity
lemma fares {w r:ℕ} (g:o'∈bay (terr (More N)) o w) (hp:2*(w+r)+2<(More N).val) (h:0≤d)(q:0<a)(k:Guard X d)(e:Speed X Q.val d) :
 let v:= hue X o; let D:=cloud Q o; let b:= Air N a d; b.st.eval (bay b.st.F o' r) (b.st.drive v (cloudT d Q X k)) (cloudT d D 1 (guard0 h)) ≤ profit a w r*d := by
 intro v D b; let S:= bay (terr (More N)) o' r; let M:ℝ:=16*((r:ℝ)+1)^4; have hM: (S.card:ℝ)≤M:= Tenant.reach _ _; let W:=w+r
 have ht:0≤priceF (w+r) d:=by unfold priceF; positivity
 have he(i)(t:i∈leaks S):scenery ((gauge v X) i) ((1:Bkg (More N)) i)≤ priceF W d:= hue_wall X o hp h k i (leaks_up (coverBay g) t) -- parse
 let J:= g; have hy: fa (gauge v X) 1 S ≤ M*4*priceF W d:= fa_bay ht he
 change fa _ _ _ / |a|+ (∑ i∈ S, ‖motion (v i) (Q.val i)- Q.val o‖) ≤ _
 refine le_trans (add_le_add (div_le_div_of_nonneg_right hy (abs_nonneg a)) ((sum_le_sum fun i (hx:i∈S)=> hue_staff e o i _ (coverBay g hx)).trans ?_)) (le_of_eq (show M*4*priceF W d/|a| + M*(4*(W:ℝ)*d)=profit a w r*d from by unfold profit M W priceF; ring)); rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hM (by positivity)

def errorC (M:Male)(j:ℕ)(X:Bkg (More N))(F:Quilt N):= spar j M X * pair F - pair F * cc (spar j M X)
lemma commute_crop_norm {D:Type}[TopologicalSpace D](b: Feet N D){t v:Tag b.st}{p:Pay}{A:Raw D (Single N)}(h:Earn p t v A)(g:Geometry N)(x:D)(S:Seal (Site (More N))): ‖A (b.st.drive g x)*strip b.st S‖=‖A x * strip b.st S‖:=by rw [h.cov.frame]; rw [mul_assoc (t.run g).val,mul_assoc _, mul_assoc (A x),←strip_inv v g S]; let V:= star (v.run g); change ‖(t.run g).val*(A x*(_*V.val))‖=_; rw [CStarRing.norm_coe_unitary_mul,←mul_assoc,CStarRing.norm_mul_coe_unitary]
variable {l r c:ℝ}{j:ℕ}(P:Ready j a c l r)
include P
lemma streetPrice : ∃ m:Pay, ∀ {N:Side}, P.minN≤N.val→ ∀ d:ℝ, d≤P.hT→∀ M:Male, let b:= Air N P.hT d; Earn m b.mark b.mark.reverseV (fun x=>errorC M j x.1.val x.2.val):=by
 obtain ⟨q,Y⟩:= HScope.buys (le_refl (1:ℝ)); refine ⟨(P.hP.mul q).add (q.mul P.hP),?_⟩; intro N hp d ht M b; let f:=iron N P.hT d; have he:= (HScope.skid f 1).mark (P.mat N hp M d ht); have hy:=Y f; exact (he.times hy).minus (hy.times he.ccUp)
/-- uniformly for all Guard at any d'≤δ and any H‖≤1 with speed ≤δ, threshold on N. -/
lemma roofLine (hp:1≤j)(v:0<ε): ∃ d:ℝ,0<d∧d≤P.hT∧∃ n:ℕ, ∀ {N:Side}, n≤N.val→∀ (X:Bkg (More N))(B:HScope N 1), Guard X d→Speed X B.val d→∀ M:Male, ‖errorC M j X B.val‖≤ ε:=by
 let a:=ε/2; have hx:= half_pos v; obtain ⟨m,p⟩:= streetPrice P; obtain ⟨K,T⟩:= purchases hx.le (half_lt_self v) m; obtain ⟨s,h⟩:= ((tailPaid m).eventually (gt_mem_nhds (show 0<a/4 by unfold a; positivity))).exists; let F:= profit P.hT K s; let L:=max 1 F; have hg:= zero_lt_one.trans_le (le_max_left 1 F); let d:= min P.hT (a/(2*m.cash*L)); have hm:=m.funding; have hd:0<d:=lt_min P.hTpos (by unfold L a; positivity); have hP:d≤P.hT:= min_le_left ..; have he:F≤L:=le_max_right ..; have ht:= profit_pos P.hT K s
 refine ⟨d,hd,hP,K+s+P.minN+2,?_⟩; intro N n X B U k M
 let b:= Air N P.hT d; let V:=cloudT d B X U; let Φ(z: Counter (More N) d × HScope N 1):=errorC M j z.1.val z.2.val; have hh:Earn m b.mark b.mark.reverseV Φ:= p (by omega) _ hP M
 refine T hh rfl V (fun i=>?_); let D:= hue X i; let y:=b.st.drive D V; rw [←commute_crop_norm b hh D]; let W:=cloudT d (cloud B i) 1 (guard0 hd.le); let S:= bay (terr (More N)) i K; have heq:Φ W=0:= sub_eq_zero.mpr (freeAnti j hp M _)
 change ‖Φ y*strip b.st S‖≤_; apply le_trans (b:=2*tailPay m s+F*d*m.cash); · rw [←sub_zero (Φ y),←heq]; refine cap_compare hh s S (mul_nonneg ht hd.le) ?_; intro z z'; exact fares z' (by change 2*(K+s)+2<N.val*2; omega) hd.le P.hTpos U k
 have hv:2*m.cash*L*d ≤ a:= by rw [mul_comm _ d]; apply (le_div_iff₀ (mul_pos (by positivity) hg)).1; exact min_le_right ..
 change 2 * tailPay m s + _ ≤ a; nlinarith only [h, hv, mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hd.le) hm.le]
end YM.CF.BProof.Spin
