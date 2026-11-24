import YM.CF.Prism.Homic
set_option autoImplicit false
noncomputable section
namespace YM.CF.Prism
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset SU Fock Lat Spire Scroll MeasureTheory Skye Scree Cube RG PhysicalNext.JointLoad Next.Foundations
open MultiNext.SignedSource Lyre Banjo Analysis Push.Local AnalyticBridge.VerifiedReset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.Frobenius
variable {n:Side}{a b r C d:ℝ}{k p j m:ℕ}{B:BudgetPoint}{X:Support (More n)}{o:Seat n}{F: Pane n→ℂ}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma ora (k:ℕ)(hp:2≤k)(u:ℝ)(p:1≤u): ∃ C:ℝ,1≤C∧∀ {n:Side}(B: BudgetPoint)(X:Support (More n))(o:Seat n)(v:E→tangD n)(F:Pane n→ℂ)(c r:ℝ)(R:E→Prop)(x:E), Nonwrapping X o → k ≤ B.order → 4 ≤ (More n).val → Roman r u B X o F c → 0 ≤ r → r ≤ 1 → Proofs B X o v x R k u r → ContDiffAt ℝ k (F ∘ (increment 1 ∘ v)) x∧∀ m:ℕ,m ≤ k → ∀ l: Fin m → E, (∀ i,R (l i)) → ‖iteratedFDeriv ℝ m (F∘ (increment 1 ∘ v)) x l‖ ≤ C*r^2*c:=by
 obtain ⟨A,g,h⟩:= hoped k hp u p; obtain ⟨T,w,hT⟩:=Siete.factorial k; refine ⟨T*A,one_le_mul_of_one_le_of_one_le w g,@fun n B X o v F c r R x z y q e f t l=>?_⟩
 have ht:pingS B.threshold X (increment 1 (v x)):=by simpa using l.sails 1 (by simp)
 have hz:Proofs B X o v x R k u r:=l; have hg : ContDiffAt ℝ (k:ℕ∞ω) (F ∘ increment 1) (v x):=(stirring (1:Pane n) (v x) e.depends c (e.track _ ht)).of_le (Nat.cast_le.mpr y)
 refine ⟨hg.comp x l.flow,fun m hv L hl=>?_⟩; let f0: Fin 0→E:=fun i=> Fin.elim0 i
 have hh : Promise 2 u r B o X (v x):=by simpa using l.grade 0 (by omega) f0 (fun i=>Fin.elim0 i)
 have he:0≤c:=(e.track _ ht).grade
 refine (advances k _ _ _ hg l.flow (h n X B o (v x) F c r z y q e hh f t l.mark l.sails) R (fun i _ h=> l.grade i h) m hv L hl).trans ?_
 rw [show T*A*r^2*c=T*(A*r^2*c) by ring]; exact mul_le_mul_of_nonneg_right (hT m hv) (by positivity)
abbrev mirth (X:Hub n)(B:BudgetPoint)(r C:ℝ):Prop:= (Fintype.card Axis:ℝ)*((Fintype.card SU.Slot:ℝ)*((Fintype.card SU.Slot:ℝ)*(2*fence (X:=X) (B:=B) (C*r))))≤ 2*C*r^2
variable {F':InkD n}
lemma dawnT (A:tangD n→ℂ)(h: Signs B o A a)(c:ℂ)(k:‖c‖ ≤ a): Signs B o (fun x=>A x-c) (2*a):=by
 have ht:=h.grade; refine ⟨by positivity,h.paid.sub contDiffAt_const,fun i g l q=>?_⟩; have hv:=h.token i g l q
 change ‖iteratedFDeriv ℝ i (A-fun _=>c) 0 l‖ ≤ _; rw [iteratedFDeriv_sub_apply (h.paid.of_le (Nat.cast_le.mpr g)) contDiffAt_const]; by_cases hi:i=0; subst i; simp only [iteratedFDeriv_zero_apply] at hv ⊢; exact (norm_sub_le ..).trans ((add_le_add hv k).trans_eq (two_mul _).symm)
 rw [iteratedFDeriv_const_of_ne hi]; change ‖_ - (0:ℂ)‖ ≤_; simp only [sub_zero]; exact hv.trans (by linarith only [ht])
lemma esther (X:Hub n)(x y:Rock n)(i l:SU.Slot)(kp:Finset (Dwell n)→ℝ)(H: PressB B X F' a b)(ht:∀ i,0≤kp i)(p:∀ U,BedP B U F' X kp)(hw: Nonwrapping X.val.2 X.val.1)(hn:4 ≤ (More n).val)(hx:node x.1∈X.val.2)(hy:node y.1∈X.val.2)(s: mirth X B r C): let f:=crib F' x y i l; Roman r C B X.val.2 X.val.1 (fun V=>f V-f 1) (2*crack kp x y):=by
 dsimp only; let A:=crib F' x y i l; let Q:=crack kp x y
 have he:=sent 1 kp x y (p 1) (ping_f B X.val.2) ht i l; have hk:‖A 1‖ ≤ Q:=by simpa [Work.G07.at_zero_increment,Q,A] using sig0 he
 refine ⟨fun U u=>dawnT _ (sent U kp x y (p U) u ht i l) _ hk, sub_self _,fun u m v =>?_,fun V W h=> congrArg (fun z : Cipher n=>mileT x y true false z i l-A 1) (H.term V W h)⟩
 have hx':= B.order_ge; change ‖fderiv ℝ (A∘ increment 1 - fun _=>A 1) 0 u‖ ≤ _; rw [fderiv_sub (f:=A∘increment 1) (x:=0) (g:=fun _=>_) (he.paid.differentiableAt (by simp; omega)) (differentiableAt_const (A 1)),fderiv_fun_const, Pi.zero_apply,sub_zero]; apply (yarn H i l x y kp ht p _ u v m hw hn hx hy).trans; have hP:=mul_le_mul_of_nonneg_right s he.grade; change _≤C*r^2*(2*Q); unfold mirth at hP; change _*Q ≤ _*Q at hP; linarith -- tune nf
end YM.CF.Prism
