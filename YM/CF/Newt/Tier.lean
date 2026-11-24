import YM.CF.Newt.Pole
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior Finset MeasureTheory
  Push Push.Uniform Metric
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge} {c f:Side} {k n l:ℕ}{q:Clip}{R:PathData G}{σ C a D W d:ℝ}
section actual
variable {S:StepData c f}{F:Forest S.ratio}{x:Positions (Joint F G)}
structure Wax (y: Positions (Joint F G)→ℝ) (B: Positions (Joint F G))(n:ℕ)(d C:ℝ): Prop where
 he: ContDiffAt ℝ ω y B
 hv: Scatter (address F G) d n y B C
lemma wax_add {f g:Positions (Joint F G)→ℝ} (p:Wax f x n a C)(t:Wax g x n a D):Wax (fun z=>f z+g z) x n a (C+D):= ⟨p.he.add t.he,p.hv.add p.he t.he t.hv⟩
lemma Wax.mono {f:Positions (Joint F G)→ℝ} (p:Wax f x n a C)(t:C ≤ D): Wax f x n a D:=⟨p.he,p.hv.mono t⟩
def fareX(G:Gauge)(q n:ℕ)(Z σ:ℝ)(L:Side) := atomCost G Z σ n q*countCost (entryWidth n L σ/2)
lemma atomX (h:0<σ)(p:PaintSupply G n D)(s: Signed)(A:ℕ→ Atom G k)(q:SumBudget (fun j=>(A j).budget σ) C)(hx:x∈ ball 0 1):
 let d:=entryWidth n S.patch.L σ
 Wax (fun y=>uncut A (signedFine F y s)) x n (weaker n d) (C*fareX G k n D σ S.patch.L):=by
 intro d
 have he(i):=atom_beacon F s h q p x hx i; have hh(i):=label_analytic F A h q s p i x hx
 have hp : Injective (affine (R:=Per f) s 0) := fun i j h=>by unfold affine at h; simpa using congrArg s⁻¹.act (add_right_cancel h)
 have hq := width_positive h n S.patch.L; have ht:0 ≤ C:= (tsum_nonneg q.1).trans q.2.2; have hv:=scatter (Multiplicity.injective hp) hh he hq (mul_nonneg ht (atomCost_nn p h k))
 refine ⟨ContDiffAt.sum (s:=Finset.univ) fun i _=>hh i,hv.mono ?_⟩; exact le_of_eq (by unfold fareX; rw [show S.patch.L=S.ratio.count from rfl]; ring)
lemma Wax.average {f:Signed→Positions (Joint F G)→ℝ}(p:∀ s,Wax (f s) x n d C) : Wax (fun y=>Patch.average fun s=>f s y) x n d C:=by -- d type Nat fix
 have hv:0<(Fintype.card Signed:ℝ) :=by positivity
 let v := (Fintype.card Signed:ℝ)⁻¹; let Q y:= ∑ s,f s y; have h : ContDiffAt ℝ ω Q x:= ContDiffAt.sum (s:=Finset.univ) fun s _=>(p s).he
 have ht:=(scatter_sum (s:=Finset.univ) (fun i _=>(p i).he) (fun i _=>(p i).hv)).smul h v
 simp_rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,abs_of_pos (show 0<v from inv_pos.mpr hv),show v*((Fintype.card Signed:ℝ)*C)=C from by unfold v; field_simp] at ht
 exact ⟨h.const_smul v,ht⟩
def muskP(G:Gauge)(n:ℕ)(Z σ C:ℝ)(L:Side):= Stationary.gramCost G C*fareX G 2 n Z (σ/2) L+C*fareX G 3 n Z (σ/2) L+C*fareX G 4 n Z (σ/2) L
abbrev costP (F:Forest S.ratio)(T:S.Choices)(q:Clip)(R:PathData G):=Push.Uniform.priced F T q R
def tailP(S:RG.Patch)(σ:ℝ)(n:ℕ):=weaker n (entryWidth n S.L (σ/2))
lemma tail_paid (h:R.Bounds q σ C a)(m:ℕ)(F:Forest S.ratio)(k:S.Choices)(p:PaintSupply G n D)(x:Positions (Joint F G))(hx:x∈ ball 0 1):
 Wax (costP F k q R-costP F k q (grainA R m)) x n (tailP S.patch σ n) (tollE σ m*muskP G n D σ C S.patch.L):=by
 rw [show costP F k q R-costP F k q (grainA R m)=_ from funext (tail_exact h m F k)]; apply Wax.average
 intro s; let v:= h.width; apply Wax.mono (wax_add (wax_add (atomX (half_pos v) p s _ (hurry h m) hx) (atomX (half_pos v) p s _ (pastA _ v h.three m) hx)) (atomX (half_pos v) p s _ (pastA _ v h.four m) hx)); exact le_of_eq (by unfold muskP; ring)
end actual
end YM.CF.Newt
