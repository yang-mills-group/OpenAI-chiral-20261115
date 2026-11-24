import YM.CF.Reflect.Regular

/-! Gauge reflection apparatus finite existence. Does not assert continuum physical reconstruction or uniform ratios. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {A D d e β : ℝ} {W : Scroll m B c}
def nextG (p : Geometry (CSide m B)) (x : Pack m B) := (Lattice.gauge p x.1,partner m B p x.2)
def colorW (p : Geometry (CSide m B)) : UNI (Finset (Xmind m B)) := quantU (n:=Xmind m B) (conjG matter (p ∘ node))
def rideG (m B : Side) (p) (F : Test m B) (x : Pack m B) := twist (star (colorW (m:=m) (B:=B) p)) (F (nextG p x))
lemma inspect (p : Geometry (CSide m B)) : MeasurePreserving (nextG (m:=m) (B:=B) p) (wheel m B) (wheel m B) := (Wilson.prior_gauge (G:=SU.group) p).prod (rain_g ..)
lemma cruise (p : Geometry (CSide m B)) : Continuous (nextG (m:=m) (B:=B) p) := by
  refine Continuous.prodMk (f:=fun x:Pack m B=> Lattice.gauge p x.1) ?_ ((pass m B p).continuous.comp continuous_snd)
  refine continuous_pi (fun i=>?_); unfold Lattice.gauge; fun_prop
lemma repeat_g (p : Geometry (CSide m B)) (x : Pack m B) : nextG p⁻¹ (nextG p x)=x := by
  apply Prod.ext
  · funext i; simp [nextG,Lattice.gauge,mul_assoc]
  exact (pass m B p).left_inv x.2
lemma appoint (p : Geometry (CSide m B)) : MeasurableEmbedding (nextG (m:=m) (B:=B) p) := by
  let F : Pack m B≃ₜ Pack m B :=
    { toFun := nextG p
      invFun := nextG p⁻¹
      left_inv := repeat_g p
      right_inv := fun _=>by nth_rw 1 [←inv_inv p]; exact repeat_g ..
      continuous_toFun := cruise p
      continuous_invFun := cruise p⁻¹ }
  exact F.measurableEmbedding
lemma net_price (p : Geometry (CSide m B)) (x : Pack m B) (v) : net m B v (nextG p x)=net m B v x := by
  unfold net nextG top massR; dsimp only; rw [law_g, Wilson.bare_gauge]
lemma anew (p : Geometry (CSide m B)) (x : Pack m B) : nextG p x∈ TallyR m B e β ↔ x∈ TallyR m B e β := by
  have he (p : Geometry (CSide m B)) x (u:x∈TallyR m B e β) : nextG p x∈TallyR m B e β := ⟨Guard.cov u.1 _, by have v:=net_price p x β; exact fun k=> u.2 (v.symm.trans k)⟩
  refine ⟨fun g=>?_,he p x⟩; have ht := he p⁻¹ _ g; rw [repeat_g] at ht; exact ht
variable (U : ScaleK A D W) (g : Budget B e d)
include U g
lemma ceremony (t a : ℝ) (p : Foot m B) (v : Geometry (CSide m B)) (f : Test m B) : rawE W e β t a p (rideG m B v f)=rawE W e β t a p f := by
  unfold rawE; nth_rw 2 [← (inspect (m:=m) (B:=B) v).integral_comp (appoint v)]; apply integral_congr_ae; apply Eventually.of_forall; intro x; unfold ratioR
  by_cases k:x∈ TallyR m B e β
  · have hp := tallyP k; let S := nextG v x
    let Y := v ∘ node (N:=CSide m B); let V := conjG matter Y; let A := quantU (n:=Xmind m B) V
    have hA : acts A.val (linearB _)=linearB _ := ref_frame Y
    have he : pairWave (n:=Xmind m B) (pair m B S.1 S.2)=acts A.val (pairWave (pair m B x.1 x.2)) := by
      have ht := pair_g x.1 x.2 v; rw [show pair m B S.1 S.2= congrC V _ from ht,congrC, ← pair_cov]; rfl
    let H := wiel m B p S.1
    have hH : H=twist V (wiel m B p x.1) := by unfold H wiel; rw [show links S.1=Lattice.gauge Y (links x.1) from links_g ..]; exact twistH ..
    let F := rideG m B v f
    have hF : f S= twist A (F x) := by
      have he := twist_inv (star A) (f S); rw [star_star] at he; exact he.symm
    change (TallyR m B e β).indicator _ _ = (TallyR m B e β).indicator (amplitude W p β t a f) (nextG v x)
    rw [Set.indicator_of_mem k, Set.indicator_of_mem ((anew ..).mpr k)]; unfold amplitude; rw [net_price, show cabin W (nextG v x)=_ from cabin_g U g hp v]
    apply congrArg; change _=inner ℂ _ (acts (f S*quant (n:=Xmind m B) (grow H _)) (pairWave (pair m B S.1 S.2)))
    rw [hF,hH,he,←quant_flow]; change _=inner ℂ _ (acts (twist A _*twist A _) (acts A.val _)); rw [←map_mul]; exact (bra V hA _ _).symm
  simp only [Set.indicator_of_notMem k]; rw [Set.indicator_of_notMem (fun z=>k ((anew v x).mp z))]
omit U g
-- simultaneous theorem; pack readers include arbitrary even / twisted odd cylinders.
structure Reg (β e : ℝ) (B : Side) where
  c : ∀ m, Foot m B
  W : ∀ m, Scroll m B (c m)
  time : ℕ →ℝ
  knob : ℝ
  charges k : k < time k ∧ time k< k+1
  Z (m : Side) (k : ℕ) : 0 < rawE (W m) e β (time k) knob (c m) (emptyF m B)
namespace Reg
def schwinger (Y : Reg β e B) (m : Side) k (f : Test m B) := rawE (Y.W m) e β (Y.time k) Y.knob (Y.c m) f / rawE (Y.W m) e β (Y.time k) Y.knob (Y.c m) (emptyF m B)
lemma one_value (Y : Reg β e B) (m k) : Y.schwinger m k (emptyF m B)=1 := div_self (Y.Z m k|>.ne')
structure Works (Y : Reg β e B) : Prop where
  integrates (m k f) (h : Continuous f) : Integrable (ratioR (Y.W m) e β (Y.time k) Y.knob (Y.c m) f) (wheel m B)
  normal (m k) : Y.schwinger m k (emptyF m B)=1
  gauge (m k p f) : Y.schwinger m k (rideG m B p f)=Y.schwinger m k f
  mirror (m n f₁ b i v) (h : OfferedF m B i f₁ b) : 0≤ Y.schwinger m n (squareR m B v (Y.c m) i f₁ b)
lemma supplied (Y : Reg β e B) (u v d : ℝ) (h : ∀ m, ScaleK u v (Y.W m)) (p : Budget B e d) : Works Y := by
  refine ⟨fun m n f g=> sojourn (h m) p g _ _ _ _,one_value Y,fun m k p' f=> ?_,fun m n f b i V g=>?_⟩
  · unfold schwinger; rw [ceremony (h m) p]
  apply div_nonneg (displacement (h m) p _ _ _ _ _ ((Nat.cast_nonneg _).trans (Y.charges _).1.le) _ _ g) (Y.Z ..).le
end Reg
lemma regulated (ω ε : ℝ) (p:0<ω) (v:0<ε) : ∃ u c:ℝ, 0<u ∧ 0<c ∧ ∃ n:ℕ, ∀ B:Side,n≤B.val → ∃ k:ℝ,0<k∧∀ e:ℝ,0<e → e≤k→∀ β:ℝ,∀ r>0, ∃ R:Reg β e B, 1-r<R.knob ∧ R.knob<1 ∧ (∀ m:Side,RunsB m B (R.c m) (R.W m) u c (quantile u B) e ω ε) ∧ R.Works := by
  obtain ⟨u,c,g,h,N,H⟩ := schedule ω ε p v; refine ⟨u,c,g,h,N,fun B e=>?_⟩; obtain ⟨k,f,M⟩ := H B e
  refine ⟨k,f,?_⟩; intro e p g β r t
  let c₀ (m : Side) : Foot m B := 0; choose W L using fun m:Side=> M e p.le g m (c₀ m)
  let P := (L 1).budget
  obtain ⟨a,hA,T,S⟩ := covered B u c _ _ β _ P p c₀ W (fun i=>(L i).scaleK) t -- tune
  choose F hf hV Z using S
  let R : Reg β e B := ⟨c₀,W,F,a,fun i=> ⟨hf i,hV i⟩, fun i j=> Z j i⟩
  exact ⟨R,hA,T,L,R.supplied _ _ _ (fun i=>(L i).scaleK) P⟩
end YM.CF.RP
