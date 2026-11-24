import YM.CF.Cascade.Velvet
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
lemma fiscalY(n:Side)(X:Op (Single n)):Matrix.trace ((love n).symm X)=Matrix.trace X:= Equiv.sum_comp (helix n).symm (fun i=> X i i)
lemma bar_n (p:Momentum):Matrix.trace (bar j n p)=2:=by
 have he:= Matrix.trace_mul_comm (zen (skin j n p)) grading; let X:= zen (skin j n p); change _= Matrix.trace (grading*X) at he
 have ht: Matrix.trace (grading*X)=0:=by rw [zenG, Matrix.trace_neg]; rw [zenG,Matrix.trace_neg] at he; exact neg_eq_zero.mpr (by linear_combination (1/2:ℂ)*he)
 have hx:Matrix.trace grading=0:=by rw [ordA,Matrix.trace_sub,Matrix.trace_smul,dateA]; norm_num [SpinIdx]
 unfold bar; rw [Matrix.trace_add, Matrix.trace_add,Matrix.trace_smul, Matrix.trace_smul,hx, ht]; norm_num [SpinIdx]
variable {m B L:Side}{ho:Odd L.val}{e:ℝ}{Y:Pricing j L ho (Vault.Thread j)}{P:Grasp Y B e}
lemma rank_z (N:Side)(t:1≤j)(M:Male): Matrix.trace (spar j M (1:Bkg (More N)))= Matrix.trace (tickA N):=by
 let V:=love N
 unfold spar; rw [profile_trivial,funde_flat _ t, show cart N (tub (bar j M.val))= _ from cart_traded (A:=bar j M.val) (cBar j M.val true t M.property) N, ← atmos]; rw [← fiscalY,← fiscalY N (tickA N),plusInk,StarAlgEquiv.symm_apply_apply, StarAlgEquiv.symm_apply_apply]; change Matrix.trace (subHub (fun i:Site N=> bar j M.val (mel i) ⊗ₖ (1:Op Slot)))=Matrix.trace (flatV Slot N); rw [←show subHub (fun _: Site N=>bins Slot)=flatV Slot N from bin_hub]; simp_rw [trace_hub,Matrix.trace_kronecker,bar_n,bins,Matrix.trace_kronecker,dateA]
lemma trace_near {ι E:Type*}[TopologicalSpace ι][LinearOrder E][Fintype E](x:ι)(P:ι→ Op E)(h: ContinuousAt P x)(g:∀ᶠ v in 𝓝 x,IsStarProjection (P v)):∀ᶠ v in 𝓝 x,Matrix.trace (P v)=Matrix.trace (P x):=by
 classical
 let S:Set ℂ:= {z|∃ t:Finset E,(t.card:ℂ)=z}; let f:=Matrix.trace ∘ P; have he:ContinuousAt f x:= ((Matrix.traceLinearMap E ℝ ℂ).toContinuousLinearMap.continuous.continuousAt.comp h)
 have ha:S.Finite:=by apply Set.Finite.subset (Set.finite_range fun i:Finset E=> (i.card:ℂ)) (fun i h=> h)
 let A:= (S \ {f x})ᶜ; have hx : A∈𝓝 (f x):=(ha.sdiff|>.isClosed|>.isOpen_compl).mem_nhds (by simp [A]); have hh(v:Op E)(p:IsStarProjection v):Matrix.trace v∈ S:=by
    obtain ⟨U,s,rfl⟩:=spot_projection _ p; rw [trace_twist,trace_cut]; exact ⟨s,rfl⟩
 filter_upwards [g,he.preimage_mem_nhds hx] with j hj hz; have hy:f j∈S:=hh _ hj; apply Classical.byContradiction; exact fun h=>(hz: f j ∈ A) (show f j ∈ S \ {f x} from ⟨hy,fun v=>h v⟩)
lemma stableD {m:Type*}[Fintype m][DecidableEq m](P:Op m)(s:star P=P)(u:IsUnit P): Matrix.det P ≠0 ∧ (Matrix.det P).re≠0:=by
 have he:= isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp u); have ht: (Matrix.det P).im=0:=Complex.conj_eq_iff_im.mp (by change star _ = _; rw [←Matrix.det_conjTranspose,←Matrix.star_eq_conjTranspose, s]) -- tune
 exact ⟨he,fun h=>he (Complex.ext h ht)⟩
def Zoom(N:Side)(A:Op (Single N)):= A*star A+(1-tickA N)
def foray(N:Side)(f:Op (Single N)):= cash ((love N).symm (Zoom N f))
lemma beamCash(N:Side)(T C: Op (Single N)):foray N (tickA N*(1+C)*T)= OrbT (tickA N) T C:=by
 unfold foray Aroma.cash OrbT; rw [show Matrix.det ((love N).symm _)=Matrix.det (Zoom N _) from Matrix.det_submatrix_equiv_self ..]; unfold Zoom; ring
lemma plume (U:Dress n)(M:Male)(u:CoreX)(x:Air n): Aroma.Met (ArcJ u j M U) x = (love n).symm (Zoom n (grace j M U (pour n u x))):=by unfold Met Zoom; rw [map_add,map_sub,map_mul,map_star,map_one, plusInk,StarAlgEquiv.symm_apply_apply]; rfl
lemma heat_n (N:Side) (A:Op (Single N))(p:IsUnit ((love N).symm (Zoom N A))): ContDiffAt ℝ ω (foray N) A:=by
 let L(B:Op (Single N)):= (love N).symm (Zoom N B); have he:star (L A)=L A:=by unfold L; rw [← map_star]; simp only [Zoom,star_add,star_mul,star_star,star_sub,star_one,show star (tickA N)=tickA N from (plus_P _).2]; -- tune
 have hx:= stableD (L A) he p; have ht : ContDiffAt ℝ ω L A:=by
    let P:Op (Single N)→L[ℂ] Op (Model N):= (love N).symm.toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap; exact ((P.restrictScalars ℝ).contDiff.contDiffAt.comp (f:=Zoom N) _ ((contDiffAt_id (n:=ω) |>.mul ((starL ℝ:Op (Single N)≃L[ℝ]Op (Single N)).contDiff.contDiffAt)).add contDiffAt_const)) -- tune id'
 have hm: ContDiffAt ℝ ω Matrix.det (L A):=by
    change ContDiffAt ℝ ω (fun x:Op _=>Matrix.det x) _; simp_rw [Matrix.det_apply]; refine ContDiffAt.sum fun i _=> ContDiffAt.const_smul i.sign (contDiffAt_prod fun j _=> Nacre.tort.mp contDiffAt_id _ _) -- tune
 exact contDiffAt_const.mul ((Complex.reCLM.contDiff.contDiffAt.comp _ (hm.comp _ ht)).log hx.2)
lemma hourZ (U:Dress n)(M:Male)(u:CoreX)(p: Foot (ting u) j M.val (ArcJ u j M U)): IsUnit ((love n).symm (Zoom n (grace j M U 0))):=by
 have ht:= p.census.1; rw [plume,map_zero] at ht; exact ht
end YM.CF.Cascade
