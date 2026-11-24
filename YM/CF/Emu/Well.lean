import YM.CF.Emu.Pin
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Pic Nova Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc MeasureTheory Vale RG Wilson Scree Skye Pastry
open YM.Stationary (Gaia)
variable {α:Type*}{N:Side}{o:Site N}{L B:Side}{j n:ℕ}{O:Odd L.val}{Y:Pricing j L O (Thread j)}{e b c v K a l r τ w u:ℝ}{P:Grasp Y B e}{H:Pearl P}{m:Side}{f:ℕ→Side}{R T W:ℕ→ℝ}
lemma fig (Q:α→ Wing)(x:α→Gaia)(h:Yard (aj B f) R):∃ p:Plot α R,p.atV=x∧p.seat=Q:=by
 let z(i:ℕ)(a:α)(j:Axis):ℤ:=⌊R i*x a j⌋
 have hp(a:α)(j:Axis): Tendsto (fun i=> (z i a j:ℝ)/R i) atTop (𝓝 (x a j)):=by
    rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero (fun _=>norm_nonneg _) (g:=fun i=> 1/R i) ?_ (h.thinner 1); intro i; have he :↑(z i a j)≤ R i*x a j:= Int.floor_le _; have hz:R i*x a j ≤ (z i a j:ℝ)+1:=(Int.lt_floor_add_one _).le; have hr:=h.pos i; rw [Real.norm_eq_abs]; apply abs_le.mpr; constructor
    · rw [le_sub_iff_add_le,le_div_iff₀ hr]; field_simp at *; linarith
    have hh:(z i a j:ℝ)/R i ≤ x a j:= (div_le_iff₀ hr).mpr (he.trans_eq (mul_comm ..)); linarith [show 0<1/R i by positivity]
 refine ⟨⟨z,Q,x,fun i=> ?_,fun i j h=> Eventually.of_forall fun m=>by unfold z; rw [h]⟩,rfl,rfl⟩
 apply Tendsto.comp (g:=WithLp.toLp (p:=2) (V:=Axis →ℝ)); rotate_right; exact (nhds (WithLp.ofLp (p:=2) (x i))); exact PiLp.continuous_toLp _ _|>.tendsto _; exact tendsto_pi_nhds.mpr (hp i)
lemma existent(B:Side):∃ f R,Yard (aj B f) R:=by
 let f(i:ℕ):Side:= ⟨(i+1)^2,by positivity⟩; let R(i:ℕ):ℝ:=i+1; have he:Tendsto R atTop atTop:= tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
 refine ⟨f,R,⟨fun i=>by unfold R; positivity,he,?_,fun i=> Even.mul_right (even_two.mul_left (f i).val) _⟩⟩
 have ht:Tendsto (fun i=> Real.pi/(R i*((2:ℝ)*B.val))) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (he.atTop_mul_const (show 0<2*(B.val:ℝ) by have :=nPos B; positivity))
 refine ht.congr fun i=>?_ ; change _=R i*(Real.pi/(↑((f i).val*2*B.val):ℝ)); unfold R f; push_cast; have he:0 < (i:ℝ)+1:=(by positivity); change _=(↑i+1)*(Real.pi/(((↑((i+1)^2:ℕ):ℝ))*2*B.val)); push_cast; field_simp -- tune
lemma ripen(L:Side)(p:Odd L.val)(j:ℕ)(h:1≤j)(g:Even j):∃ (V: Pricing j L p (Thread j))(B:Side)(e:ℝ)(P:Grasp V B e)(H:Pearl P)(K b v c l r:ℝ)(n:ℕ),Nonempty (Span H K b v c l r n):=by
 obtain ⟨Y,hY⟩:= sparkling g h p; obtain ⟨R⟩:=Acorn.restoreX j h; obtain ⟨n,v⟩:= ava Y R h; let b:Side:=⟨n+1,by positivity⟩; obtain ⟨l,Q⟩:=v b (Nat.le_add_right n _); let D:Side:= ⟨l+1,by positivity⟩; obtain ⟨K,X⟩:=Q D (Nat.le_add_right ..); let A:Side:=⟨K+1,by positivity⟩; let B:= b*(D*A); have he : K≤B.val:=le_trans (Nat.le_add_right K 1) ((Nat.le_mul_of_pos_left A.val D.property).trans (Nat.le_mul_of_pos_left _ b.property))
 obtain ⟨e,h,g⟩:= X B he ⟨_,rfl⟩ ⟨b*A, by unfold B; ac_rfl⟩; obtain ⟨V,⟨H⟩,W⟩:=g e h le_rfl; exact ⟨Y,B,e,V,H,crop0 H hY ‹1≤j› h⟩
end YM.CF.Emu
