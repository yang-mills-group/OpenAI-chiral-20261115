import YM.CF.Ave.Silk

/-! Cash limits, including tuning the open nonvanishing knobs. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ave
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock SU Lat Cube Phase Phase.Sample Mir RP MeasureTheory NormedSpace Branch Lattice Tenant Function Pastry Petal Manifest Filter Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {e H k : ℝ}
def bond (σ:ℝ) (h:ℝ) (n:ℕ) := h/(σ^n)
lemma bond_good {σ h : ℝ} (p:1≤h) (g : 0<σ) (k : σ<1) (n:ℕ) : 1≤ bond σ h n := by unfold bond; apply (le_div_iff₀ (by positivity)).mpr; rw [one_mul]; exact (pow_le_one₀ g.le k.le).trans p
-- transfer residual gets bounds even with rising grade cost
lemma insurable {k : ℝ} (hk : 0<k) : ∃ (σ:ℝ), 0<σ ∧ σ<1 ∧ ∃ N:ℕ,∀ B:Side,N≤B.val→∀ h:ℝ,∀ p:1≤h,∃ J:ℕ,∀ n:ℕ,J≤n→∀ t:ℝ,n≤t → t≤n+1 → ∀ (e:ℝ), Room B e → ∀ (m:Side) (c : Foot m B),∃ (V:1≤bond σ h n) (F : Stamp m B→Train m B e→ Ewe m B) (C : Stamp m B→ℝ), Construct m B (bond σ h n) V e t c k (1/16) F C := by
  obtain ⟨a,q,K,p,g,u,v,L⟩:= wing amp launchH (launchC false) attends (tight _) (unit_each _)
  let s := Real.sqrt q; have hs : 0<s := Real.sqrt_pos.mpr g; have hs' : s^2=q:= Real.sq_sqrt g.le; have hS : s<1 := by nlinarith
  obtain ⟨σ,hp,hσ⟩:= exists_between hS; have ht := hs.trans hp
  obtain ⟨N,f⟩:= exists_nat_gt (k*21^4/(a/2))
  refine ⟨σ,ht,hσ,N,?_⟩; intro B hB h p'
  let r := q/σ^2; have hr : 0<r := div_pos g (pow_pos ht _); have hv : r<1 := by unfold r; apply (div_lt_one (by positivity)).mpr; nlinarith
  let G := 4 * bulk a quota; let C := Real.exp (k*21^4); let R := 16*(7*(B.val:ℝ)+1)^4
  let W (n:ℕ) := C * (R*((G*K*h^2)*r^n))
  have he n : C*(R*((G*(K*q^n))*(bond σ h n)^2))=W n := by
    unfold bond W r; rw [div_pow,div_pow, ←pow_mul, pow_mul' σ]; ring
  have hh : Tendsto W atTop (𝓝 0) := (((summable_geometric_of_lt_one hr.le hv).mul_left (G*K*h^2)).mul_left R|>.mul_left C).tendsto_atTop_zero
  obtain ⟨J,H⟩:= eventually_atTop.mp (hh.eventually (gt_mem_nhds (show 0<(1:ℝ)/16 by norm_num)))
  refine ⟨J,?_⟩; intro n l t k₁ k₂ e b m c
  let z := codify (m:=m) (B:=B) c; obtain ⟨⟨A,Y,X,y,D⟩,⟨T,B',Z,j,Q⟩,F,U,i,c',q⟩:= L t n k₁ k₂ z
  have hx : ∀ S:Stamp m B,Linen (n:=Elf m B) S (A S) (T S) (F S) (sigK _) (Y S) (B' S) (U S) := fun S=> ⟨X S,Z S,i S⟩
  let s := bond_good p' ht hσ n
  let f₁ S := town (m:=m) (B:=B) (e:=e) fun d=>hang (n:=Elf m B) (A S d) (T S d) (F S d)
  have hg : k*21^4≤a/2*(B.val:ℝ) := by apply le_trans (le_of_lt ((div_lt_iff₀ (half_pos p)).mp f)); rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hB) (half_pos p).le
  obtain ⟨p,v⟩:= minted b s hx p y j c' k hk hg
  refine ⟨s,f₁,_,⟨fun S=>wand b s (hx S),p,fun i=>?_,fun x g=>?_⟩⟩
  · apply (v i).trans; rw [he]; exact (H n l).le
  let t' : Post m B:=⟨_,tenant_t b g⟩
  unfold f₁ town; simp_rw [entrance (m:=m) (B:=B) (v:=none) (p:=stick 0) (q:=stick 0) (tenant_t b g)]; rw [sum_quilt (n:=Elf m B)]; unfold retire silt
  congr 1
  · exact (D t').symm
  · exact (Q t').symm
  exact (q t').symm
-- pay the free amplitude local pieces for minuscule retuning
abbrev qua (m B : Side) (a d k : ℝ) := Real.exp (k*21^4) * (16*(7*(B.val:ℝ)+1)^4*d)
lemma motorFee {a d u v : ℝ} {c : Foot m B} {W : Scroll m B c} (g : Budget B e u) (p : ScaleK a d W) (L : 0≤d) (h : k*21^4≤a*(B.val:ℝ)) (v' : 0<k) (i : Index m) : cellHit m B k W.mint i ≤ Real.exp (k*21^4)*(16*(7*(B.val:ℝ)+1)^4*(d+(way B:ℝ)*d)) := hit_transfer v'.le h (fun S=> (gainS p g S).connect) (fun S=>(gainS p g S).pos) (fun _=>Scroll.covers p _) (by positivity) i
lemma conventional {a d u : ℝ} {c : Foot m B} {W : Scroll m B c} (g : Budget B e u) (p : ScaleK a d W) (S : Stamp m B) : supportsCup m B S (W.value S none) (W.mint S) e := by
  let f:= currency p g.1 S none
  exact ⟨f.cont,f.norm,f.pos,fun k x u=> f.gaugeEq x k u,f.connect,fun x u y v=> f.matched x y trivial u v⟩
lemma subsidy {a d u : ℝ} {c : Foot m B} {W : Scroll m B c} (g : Budget B e u) (p : ScaleK a d W) (S : Stamp m B) (σ : ℝ) : supportsCup m B S (fun x=>σ • W.value S none x) (‖σ‖*W.mint S) e := by
  obtain ⟨h,p,g,k,l,v⟩:= conventional g p S; refine ⟨(continuousOn_const (c:=σ)).smul h,fun x H=>?_,mul_nonneg (norm_nonneg _) g,fun t x q=>congrArg _ (k t x q),fun e=>l (right_ne_zero_of_mul e),fun x t y q H P=>congrArg _ (v x t y q H P)⟩ -- tune
  rw [norm_smul]; exact mul_le_mul_of_nonneg_left (p x H) (norm_nonneg _)
-- easier fund - lambda*cabin = lambda*seed + (1-lambda) full fund
lemma shake {a d u : ℝ} {c : Foot m B} {W : Scroll m B c} (g : Budget B e u) (p : ScaleK a d W) (S : FaceTerm m B) (σ : ℝ) : supportsCup m B (driftK S) (fun x=>σ • seedK W S x) (‖σ‖*coinK W u S) e := by
  obtain ⟨h,p,g,k,l,v⟩:= life p g S; refine ⟨(continuousOn_const (c:=σ)).smul h,fun x H=>?_,mul_nonneg (norm_nonneg _) g,fun t x q=>congrArg _ (k t x q),fun e=>l (right_ne_zero_of_mul e),fun x t y q H P=>congrArg _ (v x t y q H P)⟩
  rw [norm_smul]; exact mul_le_mul_of_nonneg_left (p x H) (norm_nonneg _)
end YM.CF.Ave
