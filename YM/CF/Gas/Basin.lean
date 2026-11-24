import YM.CF.Gas.Berry
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gas
open Function Filter Metric Finset NormedSpace Lattice Branch Tenant Petal Manifest Palot Stilo Corona RG Push.AbsoluteSums Trees Ursell Relation Graph MeasureTheory Phase.Sample Jet
open scoped Topology Classical BigOperators
variable {I A D E G T:Type} [Fintype I][DecidableEq I][Fintype A][DecidableEq A]
variable[TopologicalSpace D][FirstCountableTopology D][LocallyCompactSpace D][TopologicalSpace T][CompactSpace T][T2Space T][SecondCountableTopology T][MeasurableSpace T][BorelSpace T][Nonempty T]{μ:Measure T}[IsProbabilityMeasure μ][NormedCommRing E][NormedAlgebra ℝ E][CompleteSpace E][NormOneClass E]
variable{L:Lodge A E D G}{V:Cabin μ L}{M:ℕ}{r C v w K δ:ℝ}
variable{ϕ: Mood A D T→ E}{S Q: Finset A}
section s
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]{W:Set F}(Y:F→D) (P:FireK W (V.seat ∘ Y) K M)
variable (Z:E→ₐ[ℝ] E)(p:Continuous Z)(u:∀ x,‖Z x‖≤ L.fare x)
include Z p
lemma commuteA (h: Manifest V ϕ v S Q)(B:D) : Z (motor V ϕ B)=∫ t,fall (V.seat B) t • Z (ϕ (B,t)) ∂fares A μ:=by
 let X:E→L[ℝ] E:=⟨Z.toLinearMap,p⟩; symm; apply Eq.trans _ (X.integral_comp_comm (Phase.net_compact (h.cashG B)))
 apply integral_congr_ae; apply Eventually.of_forall; exact fun t=>(map_smul X (fall _ t) _).symm
include P Y u
lemma earnC (h:Manifest V ϕ v S Q)(hC:0<C)(hp:C≤1)(s:∀ t:A→T,∀ x∈ W,fall (V.seat (Y x)) t≠0→ Assets M (fun y=> Z (ϕ (Y y,t))) x C v) (x:F)(hx:x∈ W): Allows M (fun x=> Z (motor V ϕ (Y x))) x (mercury S.card M K (M.factorial*v*C⁻¹^M)):=by
 simp_rw [commuteA Z p h]; let f(x:F):=Y x; have hv:=h.price
 apply (waitB P (fun x t=> Z (ϕ (Y x,t))) Q (fun x _=>h.records (Y x)) (fun t y g w=>(s t y g w).out hC hp) (by positivity) (fun x _ a b g l s=>congrArg Z (h.localise _ _ _ s g l)) (fun y _=>?_ ) x hx).mono
 · unfold mercury; gcongr; exact h.pad
 exact (show Continuous fun t=> Z (fall (V.seat (Y y)) t • ϕ (Y y,t)) from p.comp (h.cashG _)).congr (fun i=>map_smul ..) -- tune
end s
structure Apert (K:ℕ→ℝ):Prop where
 pos i:0 < K i
 cap i:K i ≤1
 ant:Antitone K
 poly :∃ r:ℕ,∃ A:ℝ,0 ≤ A∧∀ i:ℕ,(K i)⁻¹ ≤ A*(1+i:ℝ)^r
variable (n:ℕ)
def stoke (K:ℝ)(k:ℕ→ℝ)(M:ℕ)(i:ℕ):ℝ := 1+M*mercury i M K ((M.factorial:ℝ)*(k i)⁻¹^M)
def torchR (K:ℝ)(k:ℕ→ℝ)(M:ℕ)(i:ℕ) := (stoke K k M i)⁻¹
variable {ρ:ℕ→ℝ} (g:Apert ρ)
lemma Apert.tor (X:ℝ)(g:Apert ρ) : Apert (torchR X ρ n):=by
 let p (i):=stoke X ρ n i; have hu(i:ℕ):1 ≤ p i:=by have ht:=g.pos i; unfold p stoke mercury; exact le_add_of_nonneg_right (by positivity)
 have hv(i):0< p i:= one_pos.trans_le (hu i)
 refine ⟨fun i=>inv_pos.mpr (hv i),fun i=>inv_le_one_of_one_le₀ (hu i),?_,?_⟩
 · intro i j h; change (p j)⁻¹ ≤ _; apply inv_anti₀ (hv i); unfold p stoke mercury; have ht:=g.pos j; have hx:=g.pos i; gcongr<;> exact g.ant h
 obtain ⟨m,a,k,w⟩:=g.poly
 let C:= mercury 0 n X ((↑n.factorial:ℝ)*a^n); have h:0≤ C:=by unfold C mercury; positivity
 refine ⟨m*n+n,1+n*C,by positivity,fun i=>?_⟩; unfold torchR; rw [inv_inv,add_mul,one_mul]; let r:= (1+i:ℝ); have hx:r≥1:= by unfold r; simp
 unfold stoke; apply add_le_add (one_le_pow₀ hx)
 rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _); unfold C
 have hh:=g.pos i
 calc
   _ ≤ mercury i n X ((n.factorial:ℝ)*(a*r^m)^n) :=by unfold mercury; gcongr <;> exact w i
   _ = _:=by unfold mercury r; rw [mul_pow, pow_add,pow_mul]; norm_num; ring -- tune
section s
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]{W:Set F}{Y:F→D} (P:FireK W (V.seat ∘ Y) K M)
variable (Z:E→ₐ[ℝ] E)(p:Continuous Z)(u:∀ x,‖Z x‖≤ L.fare x)
include Z p u g P
lemma meritB (h:Manifest V ϕ v S Q)(s:∀ t:A→T,∀ x∈ W,fall (V.seat (Y x)) t≠0→ Assets M (fun y=> Z (ϕ (Y y,t))) x (ρ S.card) v) (x:F)(hx:x∈ W): Assets M (fun x=> Z (motor V ϕ (Y x))) x (torchR K ρ M S.card) (2*v):=by
 let c:=stoke K ρ M S.card; have hp:= g.pos S.card; have ht:=(Apert.tor M K g).pos S.card; have hh:0<c:= inv_pos.mp ht; have hw: 1 ≤ c:= by unfold c stoke; simp only [mercury]; exact le_add_of_nonneg_right (by positivity)
 let X:= M.factorial*v*(ρ S.card)⁻¹^M; let B:=mercury S.card M K X
 have he:Allows M (fun x=>Z (motor V ϕ (Y x))) x B:= earnC _ P Z p u h hp (g.cap _) s x hx -- tune
 have hV:0 ≤ v:=h.price
 have hy : M*B=(c-1)*v:=by unfold B X c stoke mercury; ring
 refine ⟨he.smooth,(Jet.nob_earn he ht.le ((Apert.tor M K g).cap S.card)).trans ?_⟩
 apply (add_le_add ((u _).trans (h.flush.owns _)) ?_).trans_eq (show v+v=2*v from (two_mul _).symm)
 change M*B*c⁻¹≤v; rw [hy,←div_eq_mul_inv]; apply (div_le_iff₀ hh).mpr; nlinarith
end s
end YM.CF.Gas
