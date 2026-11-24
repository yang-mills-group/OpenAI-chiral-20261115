import GaugeFieldConstruction.Fiero
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc Py Py.Riant
open Pastry Grotto
variable {n:Side}{I:Type}[Fintype I][LinearOrder I]
section
variable {α γ d E:Type}[Fintype α] [NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
variable (X:Cornea α d E n)(F:Finset I→ α→d→ E)(L:dues I α→ℝ)(s:Finset (Finset I))(b:ℕ)(a r V:ℝ)
lemma preissue(x:Site n):
 (∑ i∈s,r^i.card*(∑ j∈ univ.filter (fun j=>x∈X.Φ j), dra_k b a (X.Φ j)*L (i,j)))= postG (zoneD X.Φ) (fun i:dues I α=> if i.1∈s then r^i.1.card*L i else 0) (March b a) x:=by
 unfold postG postY dues zoneD Lattice.Corona.Hive.beam; rw [sum_filter (p:=fun i=> x∈_), Fintype.sum_prod_type]; -- tune rhs
 let f(i:Finset I)(y:α):= if i∈s then r^i.card * L (i,y) * March b a (X.Φ y) else 0
 let g(i:Finset I):= ∑ y:α with x ∈ X.Φ y,f i y
 calc _ = ∑ i∈ s,g i :=by
              apply Finset.sum_congr rfl; intro j p'; unfold g; rw[mul_sum]; apply sum_congr rfl; intro w _; unfold f; rw[if_pos p']; change r^j.card*(March b a (X.Φ w)* _)=_; ring
      _ = ∑ i,g i:= sum_subset (subset_univ _) (fun i _ h=>Finset.sum_eq_zero (fun j _=>by unfold f; rw[if_neg h]))
      _= _:= by apply Finset.sum_congr rfl; intro i w; unfold g; rw[sum_filter]; apply Finset.sum_congr rfl; intro j q; dsimp only; split_ifs <;> simp_all only [ite_false,ite_true,f,zero_mul,if_true, if_false]
lemma reissue (u:0≤ r)(p:∀ i∈s,∀ x,X.Lux x (F i x) (L (i,x))) (t:∀ y:Site n,postG (zoneD X.Φ) (fun i:dues I α=> if i.1∈s then r^i.1.card*L i else 0) (March b a) y ≤ V): BookT X F b s a r V:=by
 refine ⟨fun i x=> L (i,x),p,?_⟩
 intro x; specialize t x; exact (preissue X L s b a r x).trans_le t
-- reverse direction.Law extraction transform on positive support.Tick
end
section prem
variable (p:BudgetPoint) (σ:I→ Seat n) (q h:ℝ)
local notation "Ωp"=>SecX (KeyUp p) (h:=h)
local notation "M"=> cloudP (n:=n)
open Taxi Push.AbsoluteSums Nor
lemma tx_P (x:Hub n)(V:InkD n)(c:ℝ)(T:Ids n) (u:0≤h)(m:Medal p x.val.2 ∅ (oV V) h c): PressB (KeyUp p) x V h (fareX p.B (KeyUp p) x.val.2*c):=by
 have ht:Medal (KeyUp p) x.val.2 ∅ (oV V) h c:=by
    obtain ⟨T0,A,L,B⟩:= m.pays; refine ⟨m.toThemeR,T0,A,?_,B⟩; intro l h U u; exact L l h u
 exact (show Medal (KeyUp p) x.val.2 ∅ (oV V) h c from ht).preservesE T u p.B
lemma tx_F (x:dues I (Force n))(W:Copy n)(c:ℝ)(u:0≤h)(v:ℕ)(t:PitF p h q (Rill.cipherK v) x W c): ForceB p x.2 W h (fareX p.B p x.2.val.1.val.2 * (Bplain x.1.card c q)):=by
 apply t.1.preserves _ u p.B
 constructor
 · intro H; by_contra ht; have he:¬∀ u,W u=0:=fun h=>ht (funext h); push Not at he; obtain ⟨i,v⟩:=he; exact H ((Yaw.touchK _).trans ((Corona.halo_mono (by unfold Rill.cipherK; omega) le_rfl).trans (t.2 _ v).2)) -- halo include
 intro k h; exact (t.2 k h).1
-- weighted offerings
private lemma interest (P:BudgetPoint)(D:Support (More n))(a:ℝ): March P.B a D* (fareX P.B P D) ≤ March P.B (a+ζd) D * reserveT P.power P.order P.B ζd:=by
    refine (mul_le_mul_of_nonneg_left (coinPay P D ζd ζdp (k:=P.B)) (Real.exp_pos _).le).trans_eq ?_; change March P.B a D*(reserveT _ _ _ _ * March P.B ζd D)= _; unfold March; rw[add_mul,Real.exp_add]; ring
variable (u:0≤h)(s:0 < q)(a V κ:ℝ)
open Floral
include u s
lemma pawBook (T:Ids n)(F: XE I (InkD n) n)(C:XE I ℝ n)(t:BillX p σ h q C F)(w:∀ y:Seat n,pointX M C (March p.B (a+ζd)) y≤ V) :BookT (SecX (KeyUp p) u _) (fun i j=>F (i,j)) p.B (realm_C σ) a q (reserveT (KeyUp p).power p.order p.B ζd*V):=by
 let b:= realm_C σ; let U(x:dues I (Hub n)):=fareX p.B (KeyUp p) x.2.val.2 * Bplain x.1.card (C x) q
 let K:=reserveT (KeyUp p).power p.order p.B ζd; have hK:0≤K:=by unfold K reserveT coin_n stilK ζd; positivity
 refine reissue (SecX _ _ _) _ U _ _ _ _ _ s.le (fun i _ j=> tx_P _ _ _ _ _ T u (t.lit (i,j))) (fun y=>?_)
 apply le_trans _ (mul_le_mul_of_nonneg_left (w y) hK)
 rw[←pointX_π]; unfold postG postY; rw [mul_sum]; refine Finset.sum_le_sum (fun i _=>?_); let H:= March p.B a (M i.2); let N:= March p.B (a+ζd) (M i.2); change (if _ then q^_ * U i else 0)*H ≤ K*(C i*N); split
 next v =>
    have h:=interest (KeyUp p) i.2.val.2 a; change H * _ ≤ N * K at h
    apply le_trans (le_of_eq (b:= H * (fareX p.B (KeyUp p) i.2.val.2)*C i) ?_);
    · exact (mul_le_mul_of_nonneg_right h (t.gist i)).trans_eq (by ring)
    unfold U Bplain; field_simp
 rw[zero_mul]; exact mul_nonneg hK (mul_nonneg (t.gist i) (Real.exp_pos _).le)
lemma forceBook (k:ℕ)(F:KK I (Copy n) n)(C:KK I ℝ n)(t:BillF p σ h q (Rill.cipherK k) C F)(w:∀ y:Seat n,pointX cloudK C (March p.B (a+ζd)) y≤ V) :BookT (SecK p u _) (fun i j=>F (i,j)) p.B (realm_C σ) a q (reserveT p.power p.order p.B ζd*V):=by
 let B:= realm_C σ; let U(x:dues I (Force n)):=fareX p.B p (cloudK x.2) * Bplain x.1.card (C x) q
 let K:=reserveT p.power p.order p.B ζd; have hK:0≤K:=by unfold K reserveT coin_n stilK ζd; positivity
 refine reissue (SecK _ _ _) _ U _ _ _ _ _ s.le (fun i _ j=> tx_F _ _ _ (i,j) _ _ u _ (t.lit (i,j))) (fun y=> ?_)
 apply le_trans _ (mul_le_mul_of_nonneg_left (w y) hK)
 rw[← pointX_π]; unfold postG postY; rw[mul_sum]; refine Finset.sum_le_sum fun i _=>?_ ; let H:=March p.B a (cloudK i.2); let N:=March p.B (a+ζd) (cloudK i.2); change (if _ then q^_* U i else 0)*H ≤ K*(C i*N); split
 next v =>
    calc _=H * fareX p.B p (cloudK i.2)*C i:=by unfold U Bplain; field_simp
         _≤ _:= (mul_le_mul_of_nonneg_right (interest p (cloudK i.2) a) (t.gist i)).trans_eq (by change N*K*C i=_; ring)
 rw[zero_mul]; exact mul_nonneg hK (mul_nonneg (t.gist i) (Real.exp_pos _).le)
end prem
end YM.CF.Scree.Ing
end
#print axioms YM.CF.Scree.Ing.Rio.pressure
#print axioms YM.CF.Scree.Ing.Rio.vintage
#print axioms YM.CF.Scree.Ing.pawBook
#print axioms YM.CF.Scree.Ing.forceBook
