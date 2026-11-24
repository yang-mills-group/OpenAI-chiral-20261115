import YM.CF.Cadre.Vast
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function NormedSpace Filter Set Lattice Palot
open scoped Classical Topology BigOperators
variable {A:Type*}[Fintype A][DecidableEq A](a h c:ℝ)
-- barrier early time.T verified
lemma carom(S V:A→ℝ→ℝ)(h₁:∀ i t,HasDerivAt (S i) (V i t) t)(p:∀ i:A,S i 0 < c)(w:∀ i:A,∀ t∈Set.Icc 0 h,S i t=c→ (∀ j:A,S j t≤ c)→ V i t < 0) (i:A)(t:ℝ)(x:t∈Set.Icc 0 h):S i t < c:=by
 by_contra hx; rw [not_lt] at hx
 let F(i:A):Set ℝ:= {y| c≤S i y}; let U:=Icc (0:ℝ) h∩⋃ i:A,F i
 have ht:∀ i,Continuous (S i):=fun i=> continuous_iff_continuousAt.mpr fun t=> (h₁ i t).continuousAt; have hu:IsCompact U:= isCompact_Icc.inter_right (isClosed_iUnion_of_finite (fun i=> isClosed_le continuous_const (ht i)))
 obtain ⟨y,v,e⟩:= hu.exists_isMinOn (show U.Nonempty from ⟨t, ⟨x,mem_iUnion.mpr ⟨i,hx⟩⟩⟩) continuous_id.continuousOn
 obtain ⟨hy,f⟩:=v; obtain ⟨j,q⟩:=mem_iUnion.mp f; change c ≤ S j y at q
 have hg:0<y:=lt_of_le_of_ne hy.1 fun l=>(not_lt_of_ge (l.symm ▸ q)) (p j)
 let B:= 𝓝[<] y; have hv:∀ k:A,∀ᶠ x in B,S k x ≤ c:=by
    intro k; filter_upwards [self_mem_nhdsWithin, (show ∀ᶠ x in B,0 ≤ x from mem_nhdsWithin_of_mem_nhds (le_mem_nhds hg))] with x z x'; have hx:x< y:=z; by_contra q; exact not_lt_of_ge (show y≤x from e (show x∈U from ⟨⟨x',hx.le.trans hy.2⟩,mem_iUnion.mpr ⟨k,(lt_of_not_ge q).le⟩⟩)) hx -- order z inferred
 have hr(k:A): S k y ≤ c:=le_of_tendsto ((ht k).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s:= _) (a:=y))) (hv k)
 have hl:=w _ _ hy (le_antisymm (hr j) q) hr; have H:= (hasDerivAt_iff_tendsto_slope_left_right.mp (h₁ j y)).1; apply not_lt_of_ge _ hl; apply ge_of_tendsto H
 filter_upwards [hv j,self_mem_nhdsWithin] with t p x; have ht:t<y:= x; exact (by rw [slope_def_field]; exact div_nonneg_of_nonpos (sub_nonpos.mpr (p.trans q)) (by linarith)) -- tune
end YM.CF.Cadre
