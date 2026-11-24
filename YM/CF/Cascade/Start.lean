import YM.CF.Cascade.Sow
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Push.Uniform Planned.JetPort
lemma tick_pay (p:0<a)(k:ℕ)(n:Side): HoldX id place_x (fun _:Air n => tickA n) a 1 k:=by
 refine ⟨contDiffAt_const, ledger (fun i j=>contDiffAt_const) ?_,zero_lt_one⟩
 rw [touchP]; intro i j; apply ((allows_const (n:=k) 0 (le_refl ‖cutM (Tset n) i j‖)).beacon (r:=0) (s:=Set.univ) (fun _ _ _ _ _=>rfl) univ_mem p.le).mono; rw [cutM,Matrix.diagonal_apply]; split; next h=>rw [h]; simp only [Decay,separation_self,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul,mul_one]; split <;> simp
 simp; apply Push.Uniform.decay_pos ..|>.le -- tune
lemma rakeCost (u:CoreX)(p:‖u‖=1)(x b:ℝ)(v:0<x)(g:0<b)(k j:ℕ):∃ a C:ℝ,0<a∧0<C ∧∀ n: Side,∀ G:Toy j n, (∀ i,balance x G i≤ b)→ HoldX id place_x (sumU (cavil G) ∘ represent ∘ pour n u) a C k:=by
 obtain ⟨y,h,H⟩:= hotCost k; obtain ⟨a,D,hA,hD,V⟩:= savoy x y k j 2 v h
 refine ⟨a,_,hA,mul_pos g hD,fun n T g=>?_⟩
 obtain ⟨e,x⟩:= V (fun i=> lagY (B:=1) i (yokeL n u)) (by unfold Function.comp; rw [map_zero,link_one]) (H n u p) T b (by positivity) g; exact ⟨e,x,by positivity⟩
lemma relent {P:Air n→Op (Single n)}(h:HoldX id place_x P a b t)(p:0<a): HoldX id place_x (fun x=>star (P x)) (slip t a) b t:=by
 refine ⟨(starL ℝ|>.contDiff|>.contDiffAt|>.comp _ h.glow), inkC (Nacre.tort.mp h.glow) h.law p h.funds.le,h.funds⟩
lemma holdJ (k:ℕ)(p:1≤j)(u:CoreX)(g:‖u‖=1)(l r a b:ℝ)(hv:0<l)(hp:0<r)(hu:0<a)(hz:0<b):∃ v C:ℝ,0<v ∧ 0<C∧∃ i:ℕ,∀ n:Side,i≤n.val→∀ (M:Male) (U:Aim n),U.toll l a r b→ let V:= grace j M U.den ∘ pour n u; HoldX id place_x V v C k ∧ HoldX id place_x (Zoom n ∘ V) v C k:=by
 obtain ⟨a₁,b₁,h1,p1,D⟩:= rakeCost u g l r hv hp k 1; obtain ⟨a₂,b₂,h2,p2,E⟩:= rakeCost u g a b hu hz k 2
 obtain ⟨a₃,b₃,h3,p3,n,J⟩:= certU k j p; let w:= min (min a₁ a₂) a₃; let d:= slip k w; let c:=slip k d; let e:=slip k c; let f:=slip k e; let z:=slip k f; let Y:= slip k z
 have hw:0<w:=lt_min (lt_min h1 h2) h3; have hd:0<d:=slip_pos k hw; have hc:0<c:=slip_pos k hd; have he:0<e:=slip_pos k hc; have hf:0<f:=slip_pos k he; have hq:0<z:=slip_pos k hf; have hY:0<Y:=slip_pos k hq
 let H:=Fintype.card (SpinIdx × Slot); let A:=2*((1+b₃)*(b₁+b₂)* Planned.JetPort.conductor k H w); let B:=2*(A*b₃*Planned.JetPort.conductor k H d); let K:=2*(1*(1+B)*Planned.JetPort.conductor k H c); let L:=2*(K*b₃*Planned.JetPort.conductor k H e); let G:= 2*(L*L*Planned.JetPort.conductor k H z) + (1+1)
 have hC(v:ℝ)(p:0<v):0<Planned.JetPort.conductor k H v:= Planned.JetPort.conductor_pos k H p -- tune
 have hL:0<L:=by have ht:=hC w hw; have hx:= hC d hd; have hy:= hC c hc; have h:=hC e he; unfold L K B A; positivity
 have hG:0<G:=by have ht:=hC z hq; unfold G; positivity
 refine ⟨Y,L+G,hY,add_pos hL hG,n,fun N hN M U P=>?_⟩; intro T'; obtain ⟨U1,U2⟩:=P; have ht:= yokeL N u; let H':=represent ∘ pour N u; let T:=spar j M ∘ H'; let V:=tickA N
 have hK := ringM (f:=N) _ Function.injective_id
 have hdw : d≤ w:= slip_le k hw.le; have hew:e≤w:=(slip_le k hc.le).trans ((slip_le k hd.le).trans hdw)
 have hT: HoldX id place_x T w b₃ k:=(J _ hN M u g).drop (min_le_right ..)
 have hl :HoldX id place_x (U.den∘ H') w (b₁+b₂) k:= ((D N U.x U1.2.2).drop ((min_le_left ..).trans (min_le_left ..))).opP ((E N U.y U2.2.2).drop ((min_le_left ..).trans (min_le_right ..))) -- tune min
 have hv:HoldX id place_x (Crops j M U.den ∘ H') c B k:= ((((HoldX.blank hw).opP hT.minus).times hl hw hK).times (hT.drop hdw) hd hK)
 have hh:HoldX id place_x T' f L k:= (((tick_pay hc k N).times ((HoldX.blank hc).opP hv) hc hK).times (hT.drop hew) he hK)
 let W:=hh.drop (slip_le k hf.le)
 exact ⟨((W.drop (slip_le k hq.le)).lift (le_add_of_nonneg_right hG.le)),(((W.times (relent hh hf) hq hK).opP ((HoldX.blank hY).opP (tick_pay hY k N).minus)).lift (le_add_of_nonneg_left hL.le))⟩ -- matrix complement
end YM.CF.Cascade
