import YM.CF.BPress.Spin.Pact
/-! Supply inputs to prop:B-Pproj/ B-bra; no estimate yet on realizations of the Mark integration here. Phase estimator P and path terms have to see the real Gauge/Loom field at their named geometric hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter NormedSpace Finset Lattice SU Lat Cube Tenant Branch Tulip Scroll Dial Thera Nacre Laic Stride Quad Blank Paint Cellar Cellar.Pass Hole Pf Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker BigOperators
attribute [local instance] opCStarAlgebra
variable {N:Side}{A B W:Pledge}{j w v n:ℕ}{d e ε r ρ q r' σ δ:ℝ}{width:Side}

-- C¹ needed, e.g. on constructed smooth interpolations; explicitly retain H'(v) as distinct argument of kernel price.
structure Looks (x:Bkg (More N))(P:Support N)(C C':ℝ → Paint (More N))(v:ℕ)(ρ σ q δ:ℝ):Prop where
 support : Uprice v δ P x
 guards  t : t∈ Set.Icc (0:ℝ) 2→ MatPlan (C t) -- tune
 frisky (t): t∈Set.Icc (0:ℝ) 2→ Bend (C t) x q
 stop : Secret P (C 1) σ δ v
 end_me x' : x'∈Set.Icc (1:ℝ) 2→ Census P (C x') σ ρ v
 dP x' : x'∈ Set.Icc (0:ℝ) 2→ HasDerivAt C (C' x') x' -- pi
 smooth: ContinuousOn C' (Set.Icc (0:ℝ) 2)
lemma binding {C C':ℝ→Paint (More N)} (v:ℝ)(h:HasDerivAt C (C' v) v): HasDerivAt (Paint.coupling ∘ C) (Paint.coupling (C' v)) v:=by
 let F: Paint (More N)→ₗ[ℂ] Op (Single N) := {
     toFun:= Paint.coupling
     map_add' x y:= by have he:= coupe_sub (x+y) y; rw [add_sub_cancel_right] at he; exact (eq_add_of_sub_eq (he.symm)).trans rfl -- tune
     map_smul' a x:=by ext i j; simp only [Matrix.smul_apply,smul_eq_mul,RingHom.id_apply,atX]; split <;> simp [nodeC, mul_left_comm]
 }
 exact (F.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt _ h

lemma outage (S:Support N): Disjoint (Locks S true) (Locks S false):=by apply disjoint_left.mpr; intro i h p; simp [locks,cup] at h p; tauto

variable {Q:Worthy A B W j e q r w}(D:Voucher Q width ρ σ r' v n ε δ)
include D
lemma point (k:n≤N.val)(t:0<d)(h:d≤e)(M:Jill.Male)(R:Aim N)(g:R.toll B.rate W.rate B.price W.price)(x:OpenW N d){G:BandWidth}{X:Bands (More N) G}(l:G.D=width.val) (P:Support N)(m:Dark X P)(C C':ℝ → Paint (More N))(T: Looks x.val P C C' v ρ σ q δ):
 let A':=spar j M x.val; Issued (Locks P true) (Locks P false) A' (Ts R A' x.val) (Paint.coupling ∘ C) (Paint.coupling ∘ C') r' ε:=by
 intro A'; let B':=Ts R A' x.val; obtain ⟨p₁,u⟩:= Q.speed N t h (D.ok.trans k); have v₁:= p₁.proj M x; obtain ⟨z,H⟩:=u x M R g; obtain ⟨xM,xt⟩:= D.self N d x l k t h P m R g M T.support
 have hz:= plusMinus P; let S:=mood A' B'; have hL: Pf.shun (Single N) (Locks P true) (Locks P false)=loose P:= hz.l0.symm; let U:= P
 have ht(v) (p:v∈Set.Icc (0:ℝ) 2)(i:ℝ)(h:‖i‖≤1) : Bore (tilt A' B' i) (coupling (C v)) r':= by
    let E:=T.guards v p; have hx: IsStarProjection (tilt A' B' i):= (tiltR v₁ (tag_g (R.den x.val) v₁) i).starP
    refine ⟨hx, Paint.unit _ E, Paint.skew _ E,?_ , D.grant⟩; exact (Hole.leak_bound hx _ _ (H _ E (T.frisky v p) _ h)).trans D.supportK
 refine ⟨v₁,tag_g (R.den x.val) v₁,z,by rw [hL]; exact passed (Hole.shadow_live p₁ M R x) D.alive D.small xM, outage P, ?_, Paint.coupling_cont.comp_continuousOn T.smooth, fun i p=>binding i (T.dP i p), fun s p=> ht 0 (by norm_num) s (tiny_t p), fun s p=> ht s (Set.Icc_subset_Icc_right (by norm_num : (1:ℝ)≤2) p) 1 (by simp), ?_,?_⟩
 · rw [hL]; exact ⟨hz,cut_real _,cut_real _,Eq.symm (coupling_lock _ _), Eq.symm (coupling_lock _ _)⟩
 · intro i p; rw [traceM,hL]; exact xt (C 1) (T.guards 1 (by norm_num)) (T.frisky 1 (by norm_num)) i (tiny_t p) (Or.inl T.stop)
 intro i p; rw [traceM,hL]; have hh:i∈Set.Icc (0:ℝ) 2:= Set.Icc_subset_Icc_left zero_le_one p; exact xt (C i) (T.guards _ hh) (T.frisky _ hh) 0 (by simp) (Or.inr ⟨rfl,T.end_me i p⟩)
end YM.CF.BPress.Spin
