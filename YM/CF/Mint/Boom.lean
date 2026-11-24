import YM.CF.Mint.Nove
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mint
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {x y A:ℕ→ℝ}{c b w η r a e K b' v C' l s' γ μ τ H m L':ℝ}{S T:ℕ→Side}{β θ V L1 δ L:ℕ→ℝ}{J B:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
-- nonuniform sequences. loop exponent update tracks budget. 
namespace Roe
variable {N:ℕ→Side} (D:Pic.Span hP K b' v C' l s' k) {I:∀ i,GramM (mid (N i) B)} {C Q h:ℝ}
local notation "NP"=> (fun i=> mid (N i) B)
variable (Z:WindS B N x h C r μ L' w γ c b V θ L I)
include D Z
abbrev bloom(M:ℕ→Side)(r:ℝ)(X:ℕ→ℝ)(i:ℕ):ℝ:=tame X i+2*Real.exp (-(r*eur (More∘M) i))
omit D
lemma teal:Aqua (eur NP) (bloom NP r x):=by
 let A:=eur NP; have hx:= damp Z.path.rank; have h:= hx.through (tc Z.path.rank) Z.vol; have he:=Z.wind; let f(i):= Real.exp (-(r*eur (More∘NP) i)); refine Aqua.panel h (Aqua.fed (F:=f) ?_ (Gray.coef Z.tend 2) Z.tend); exact (Aqua.exp_neg Z.tend r he).clip Z.tend (Eventually.of_forall fun i=> by change 0≤f i ∧ f i ≤ _; refine ⟨(Real.exp_pos _).le,Real.exp_le_exp.mpr ?_⟩; rw [neg_mul]; apply neg_le_neg; gcongr; unfold eur; exact_mod_cast (show (NP i).val ≤ ((More∘NP) i).val from Nat.le_mul_of_pos_right _ (by change (0:ℕ)<2; decide))) -- tune
lemma surge (k:ℝ): let M:=NP; let G:=bloom M r x; Aqua (eur M) (fun i=> baton (M i) (V i) (G i) C k)∧ (∀ᶠ i in atTop, pittance (M i) (G i) C ≤1∧ 0 ≤ G i):=by
 intro M G; let F:=Aqua (eur M); have h:Aqua (eur M) G:= teal Z; have he:= Z.tend; let H:= fun k=>Gray.coef he k; have hx:=damp Z.path.rank
 have hb :∀ᶠ i in atTop,0 ≤ G i:= Z.path.infl.mono fun i v=> (v.2.2.1.trans_le (le_add_of_nonneg_right (by positivity))).le
 have hp : Gray (eur M) (eur M):=Gray.arg he; have hu:Aqua (eur M) (fun i=> G i ^2) := by simpa [sq] using (h.pays (Gray.thin he h.shrinks) he)
 let L(i):= pittance (M i) (G i) C; have ht:Aqua (eur M) L:= ((hu.pays (H C) he).pays (hp.powG he 4) he)
 have hw:Gray (eur M) (fun i=> lark (M i)):= (H 180).mul (hp.powG he 4)
 let X(i):= doorF (M i) (G i) C; have hg:Aqua (eur M) X:= Aqua.fed (Aqua.fed ((by
   show Aqua (eur M) (fun i=> (G i + G i^2)*C); exact ((h.panel hu).pays (H C) he))) (H 45) he) hw he
 let U(i):=axle (M i) (V i)+X i*lark (M i)^2*k^2; have hl:Aqua (eur M) U:=by
    have hy : Gray (eur M) (eur (More ∘ M)):=by apply Gray.eqK (hp.mul (H 2)); exact Eventually.of_forall fun i=>by change eur M i*2=eur (More ∘ M) i; unfold eur; norm_num [More]; done
    exact Aqua.panel ((Z.loc.panel Z.loc).pays (hy.powG he 4) he) ((hg.pays (hw.powG he 2) he).pays (H _) he)
 have hL:Tendsto (fun i=>Real.exp (L i)) atTop (𝓝 (Real.exp 0)):= (Real.continuous_exp.continuousAt.tendsto.comp ((show Aqua (eur M) L from ht).shrinks)); have hz: ∀ᶠ i in atTop,0≤U i:=by
    filter_upwards [Z.support,hb] with i ℓ p; have hg:=ℓ.2.2.2.2.2; have hx:=Z.size; unfold U axle X doorF lark; positivity
 exact ⟨Aqua.panel ((show Aqua (eur M) L from ht).fed (H 2) he) (Aqua.fed (Aqua.rise hl he hz) (Gray.thin he hL) he),(ht.shrinks.eventually (ge_mem_nhds one_pos)).and hb⟩ -- infer ht issue
end Roe
end YM.CF.Mint
