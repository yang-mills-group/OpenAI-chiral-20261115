import YM.CF.Maize.Closer
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Maize
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace RG Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B L N:Side}
local notation "Λ" => CSide m B
local notation "ξ" => Domain m B
open Gloss Floe Ave Phase.Sample Jet Pastry Drapes Gas
variable {H e p a d r K D θ δ G c A:ℝ}{n:ℕ}
variable {W:Scroll m B (northZ m B)}{V:Stamp m B→ Train m B e→Ewe m B}{v:Stamp m B→ℝ}{b P α:ℝ}{hp:1≤ H}
private def Payer (m:ℕ)(A:ℝ)(j:ℕ):= A*(1+j:ℝ)^(2*m)
private def χn (m:ℕ)(A:ℝ)(j:ℕ):= (1+m*Payer m A j)⁻¹
lemma τn {m:ℕ}(h:0≤ A):Apert (χn m A):=by
 have he(j):1≤1+m*Payer m A j:= le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (by unfold Payer; positivity)); refine ⟨fun j=>inv_pos.mpr (zero_lt_one.trans_le (he j)),fun i=>inv_le_one_of_one_le₀ (he i),?_,?_⟩
 · intro i j v; unfold χn; apply inv_anti₀ (zero_lt_one.trans_le (he i)); unfold Payer; gcongr
 refine ⟨2*m,1+m*A,by positivity,fun i=>?_⟩; unfold χn Payer; rw [inv_inv,add_mul,one_mul,mul_assoc]; gcongr; exact one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) i])
lemma clamp_c (p:0≤ A)(v:0≤c) (l:ℕ){E Y:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup Y][NormedSpace ℝ Y]{f:E→Y}{x:E}(h:Allows n f x (Payer n A l*c))(u:‖f x‖≤c):Assets n f x (χn n A l) (2*c):=by
 have ht:=τn (m:=n) p; refine ⟨h.smooth,(nob_earn h (ht.pos l).le (ht.cap _)).trans ?_⟩; unfold χn; rw [←mul_assoc _ _ c]; let r:= (n:ℝ)*Payer n A l; apply (add_le_add u ?_).trans_eq (two_mul _).symm; rw [← div_eq_mul_inv]; apply (div_le_iff₀ (inv_pos.mp (ht.pos l))).mpr; nlinarith
private lemma bark_m (I:Type)[LinearOrder I][Fintype I]{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{f:E→ℂ}{x:E}(h:Allows n f x c)(p:0≤H): Allows n (fun x=>dilF H (hollow (n:=I) (f x))) x c:=by
 rw [←one_mul c]; change Allows n (fun x=> bark I H (f x)) x _; refine Allows.linear (G:=Dough I) (bark I H) h ?_; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; exact mintB p I
lemma ark_p (B:Side)(n:ℕ)(p:1≤K)(y:0<A)(z:0<d)(u:0≤c): ∃ ρ:ℕ→ℝ,Apert ρ∧∀ (m:Side)(e a G H:ℝ)(W:Scroll m B (northZ m B))(V:Stamp m B→Train m B e→ Ewe m B)(v:Stamp m B→ℝ)(t:1≤H)(r b θ:ℝ), Budget B e d→ GripK W A a G→ Construct m B H t e θ (northZ m B) r b V v →(∀ S,shines e K n (V S) H (c*v S))→∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](Y:E→ Train m B e)(X:Set E),IsOpen X→ Tagged e K n (release ∘Y) X→(∀ x∈X,Y x∈ Breath m B e)→∀ x∈X,∀ i:leafP m B,Assets n (fun x=> dilF H (seedCW W V i (Y x))) x (ρ (Xmas m B i).val.card) (2*κCost W v d i):=by
 obtain ⟨F,hf,g⟩:=bit_x p y B n; let S:ℝ:=max d⁻¹ 1*F; let C:=max S c; have hC:0 ≤ C:= le_trans u (le_max_right S _); refine ⟨χn n C,τn hC,fun m e a G H W V v t r b θ h l k E' E _ _ _ Y X o Q U x hx i=>?_⟩
 let D:= Xmas m B i; have he:=(κcs h k i l.meter).1; have hp := zero_le_one.trans t; apply clamp_c hC he.price D.val.card (f:=fun x=>dilF H (seedCW W V i (Y x))) _ ((Gas.price_d H hp _).trans (he.avail _ (U x hx))); unfold D at *; cases i with
 | inr i=>
    refine (E' i E Y X o U Q x hx).mono ?_; unfold Payer; apply mul_le_mul_of_nonneg_right _ (k.serve i).price; apply le_trans (le_max_right S c); exact le_mul_of_one_le_right hC (one_le_pow₀ (by simp))
 | inl i=>
    have hh:= bark_m (Hearth m B) (g E m e d a G (northZ m B) W z h l (release ∘ Y) X Q o x hx i) hp
    apply hh.mono; change S*(1+_:ℝ)^_ *dinQ W d i≤ _; unfold Payer; apply mul_le_mul_of_nonneg_right _ he.price; apply mul_le_mul (le_max_left _ c) _ (by positivity) hC; apply pow_le_pow_left₀ (by positivity) _; apply add_le_add_right
    let A:=chairs m B i.2
    -- A and X planning area moved
    have hp: A.card ≤ D.val.card:=by
       rw [← card_image_of_injective A (ρx i.1).injective]; unfold A; rw [chairs_P]; exact card_le_card (Finset.Subset.trans chair_pad (pad_max (Sum.inl i)))
    exact_mod_cast hp
-- test-only jets on any positive-law open
abbrev Γe (K:ℝ)(n:ℕ)(V:Briar m B e → Ewe m B)(H:ℝ)(ρ:ℕ→ℝ)(l:ℕ)(w:ℝ): Prop:=∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](f:E→ Briar m B e)(S:Set E),IsOpen S→ (∀ x∈ S,TransK n (fun i=>(f i).val) x K) →∀ x∈ S,Assets n (fun x=>Gas.dilF H (V (f x))) x (ρ l) w
end YM.CF.Maize
