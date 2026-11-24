import YM.CF.Spire.Dais
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Phase.Sample Broc Branch Jet MeasureTheory
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
section
variable {A D F J:Type}[Fintype A][DecidableEq A][TopologicalSpace D]{n:ℕ}{b:Light A D F}{q:Draw D}{x K:ℝ}{W:J→D→ℂ}
lemma screen_z:Screen b q n (fun _=>0) x 0:=by
 refine ⟨fun _ _=>0,fun _=>0,fun i=> ⟨Peak.emptyB,fun E _ _ _ B g H t x l=> allows_const x norm_zero.le⟩,fun i=> ?_, by simp⟩; simp [hitE]
lemma records(v: Finset J)(p:∀ i∈v, Screen b q n (W i) x K) : Screen b q n (fun x=>∑ i∈v,W i x) x (v.card*K):=by
 classical
 induction v using Finset.induction_on with
 | empty=> simp only [sum_empty,card_empty,Nat.cast_zero,zero_mul]; exact screen_z
 | @insert i v h H=> simp only [h,not_false_eq_true, sum_insert,card_insert_of_notMem,Nat.cast_add_one, add_mul,one_mul]; rw [add_comm (_*K)]; exact (p _ (by simp)).plus (H (fun i g=>p _ (by simp [g])))
end
variable {L B:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)} {e:ℝ}(P:Grasp Y B e) (n:ℕ)
lemma pay_he(b:Bool) :∃ F: ℂ→L[ℝ]ℂ, ‖F‖≤1 ∧ ∀ x,F x=cSignX b x:=by
 cases b; exact ⟨ContinuousLinearMap.id ℝ ℂ,(by simp),fun _=>rfl⟩; refine ⟨Complex.conjCLE.toContinuousLinearMap,?_,fun i=>rfl⟩; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i; change ‖star i‖≤_; simp
lemma launder (K:ℝ)(h:1≤K):∃ C:ℝ,0≤C∧ ∀ (m:Side), P.roundZ≤(CSide m B).val→∀ M:Tulip.Male, Screen (pWorks m B e P.p) (partQ m B e P.p n K) n (fun x=> hum m B (P.cost m M) x.val.1 x.val.2) (radF P) C:=by
 obtain ⟨a,ta,H⟩:=tutor K n h; obtain ⟨C,p,L⟩:= savings P n (h.trans ta)
 refine ⟨C,p,fun m q M=>?_⟩; let N:= Sweep (CSide m B); let v:ℝ:= Fintype.card N; have ht:0<v:=by unfold v; positivity
 let Q:= pWorks m B e P.p; let f:=P.cost m M; let l (S:N)(x:↑(Brace.Chord m B e P.p)):= payZ S (song m B f (flashA S x.val.1) (fireA S x.val.2))
 have hz(A:N): Screen Q (partQ m B e P.p n K) n (l A) (radF P) C :=by
    let Z:=castX A; let F:= ripple Z A.charge m B e P.p; let X:= pWorks m B e P.p
    have hx:Screen Q (partQ m B e P.p n K) n (fun i=> song m B f (F i).val.1 (F i).val.2) (radF P) (1*C):=by
      apply Screen.leaps (Φ:=roarD (CSide m B) Z) (Ω:=partQ m B e P.p n K) (b:=X) (c:=Q) (v:=1) (w:=1) (L m q M) (prow _ _) F (ripple_c ..) p (rad_pos P).le (by simp) (ripple_r Z A.charge m B e P.p) ?_ ?_
      · intro x y; obtain ⟨u,V⟩:=siren A.charge Z (CSide m B) x.val.1 x.val.2 y; exact ⟨fun i=>polarT A.charge (y (Z.anon _ i)),Subtype.ext (Prod.ext u V)⟩ -- tune
      intro E _ _ _ V h f g x hx; exact H (CSide m B) Z A.charge E (fun i=>(f i).val.1) x (fun i=>(f i).val.2) (g x hx).1 (g x hx).2
    obtain ⟨V,hV,hE⟩:=pay_he (wageZ A); let P':=hx.lin V hV; rw [one_mul,one_mul] at P'; convert P' using 1; funext i; exact (hE _).symm
 have he:=records (@univ N _) (fun i _=>hz i)
 let F:= v⁻¹ • ContinuousLinearMap.id ℝ ℂ
 have hv: ‖F‖ ≤ v⁻¹ := by apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr ht.le); intro i; change ‖v⁻¹ • i‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
 have hp:=he.lin F hv; rw [card_univ,show v⁻¹ * _=C by change v⁻¹*(v*C)=_; rw [←mul_assoc, inv_mul_cancel₀ ht.ne',one_mul]] at hp
 convert hp using 1; funext i; simp only [Function.comp_apply,l,F,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply, Complex.real_smul,v, Complex.ofReal_inv,map_natCast]; rfl
lemma mis_work(K:ℝ)(h:1≤K):∃ C:ℝ,0≤C∧∀ (m:Side), P.roundZ ≤(CSide m B).val→∀ M:Tulip.Male, Screen (pWorks m B e P.p) (partQ m B e P.p n K) n (fun i=> Spire.zen (hum m B (P.cost m M) i.val.1 i.val.2 - song m B (P.cost m M) i.val.1 i.val.2)) (radF P) C :=by
 obtain ⟨u,hp,U⟩:= launder P n K h; obtain ⟨v,hV,V⟩:=savings P n h
 refine ⟨_,mul_nonneg (norm_nonneg folio') (add_nonneg hp hV),fun m k M=>?_⟩; have he:= ((U m k M).plus (V m k M).minus).lin folio' le_rfl; simpa only [sub_eq_add_neg,Function.comp_def, Spire.zen,Broc.folioT] using he
end YM.CF.Spire
