import YM.CF.Tulip.Cloud
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir WilsonFrame
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
abbrev Male := {M:Side//Odd M.val}
lemma maleP (j:ℕ)(hj:1≤j): Lively fun (M:Male) N=> art N j M.val:=by
  have he: Lively (fun (M:Male) N=>reserveP N j M.val):=tube_uniform _ (fun x:Male=>x.val) (fun x=>x.property) hj
  exact (he.add he.reverseL).sub Lively.one
lemma male_e (j:ℕ)(hj:1≤j):∃ a r:ℝ,0<a∧0<r∧∃ v:ℕ,shelf (fun (M:Male) N x=>art N j M.val x*art N j M.val x-1) a (1/2) v r:=by
  let f:=fun (M:Male) N (x:Chin N)=>art N j M.val x*art N j M.val x-1
  obtain ⟨a,r,e,h,hp,hh,v,L⟩:= ((maleP j hj).prod (maleP j hj)).sub Lively.one
  obtain ⟨d,m,p1,p2,-,-,w,H⟩:= Lively.estate (f:=f) L h hh hp (1/2) (by norm_num) (by
    intro i N _
    obtain ⟨he, hx⟩:= art_one N hj i.val i.property
    unfold f; rw [he]; simp only [mul_sub,sub_mul,mul_one,one_mul,Matrix.smul_mul,Matrix.mul_smul,hx.isIdempotentElem.eq]; module)
  exact ⟨d,m,p1,p2,w,H⟩
private lemma buysafe {n:Type*}[Fintype n][DecidableEq n][Nonempty n]{A: Op n}(hp:IsSelfAdjoint A)(h:‖A*A-1‖≤1/2): Safe A:=by
  have hS: IsSelfAdjoint (A*A-1):=by rw [isSelfAdjoint_iff,star_sub,star_mul,hp.star_eq,star_one]
  refine ⟨hp,?_,?_⟩
  · have hh:‖A‖*‖A‖=‖A*A‖:=by rw [← CStarRing.norm_star_mul_self, hp.star_eq]
    have hb:= norm_le_norm_sub_add (A*A) 1; rw [norm_one] at hb; nlinarith
  have hb:= op_ge_neg_scalar hS h
  rw [sq]; rw [le_sub_iff_add_le] at hb; apply le_trans _ hb; exact le_of_eq (by module)
lemma painter (j:ℕ)(hj:1≤j): Lively (fun (M:Male) N x=> projector (art N j M.val x)) ∧
  ∃ e:ℝ, 0<e∧∃ v:ℕ,∀ M:Male,∀ N:Side,v≤N.val→∀ U:Bkg (More N), Cube.Guard U e→Safe (art N j M.val (profile U)) :=by
  obtain ⟨a,r,h,hp,v,H⟩:= male_e j hj
  constructor
  · refine royal (maleP j hj) hp rho_pos rho_lt (v:=v) (fun i N hv x hx=> ?_)
    let F:=art N j i.val x; have he:‖F*F-1‖≤1/2:=(H i N hv).lib.boundOp h.le ⟨x,hx⟩
    change ‖slack F‖≤ _
    rw [slack,show (1:Op _)-(1/256:ℝ) • F^2=(255/256:ℝ) • 1-(1/256:ℝ) • (F*F-1) by rw [sq]; module]
    refine (norm_sub_le ..).trans ?_; rw [norm_smul,norm_smul,Real.norm_of_nonneg (by norm_num),Real.norm_of_nonneg (by norm_num),norm_one]; unfold rho; linarith
  refine ⟨r,hp,v,fun i N hv U hg=>?_⟩
  let x:=profile U; have ht:x∈Openc (More N) r:=⟨U,hg,by simpa [x]⟩
  have hh:star (art N j i.val x)=art N j i.val x:=by unfold art pale; rw [ice_pr,star_sub,star_add,star_star,star_one,add_comm]
  exact buysafe hh ((H i N hv).lib.boundOp h.le ⟨_,ht⟩)
lemma projector_one (N:Side){j:ℕ}(hj:1≤j)(M:Male): projector (art N j M.val 1)=reserveP N j M.val 1:=by
  let A:=art N j M.val 1; let P:= reserveP N j M.val 1
  obtain ⟨he,hp⟩:=art_one N hj M.val M.property; change A=(2:ℝ) • P-1 at he
  change IsStarProjection P at hp
  have hx:A*A=1:=by rw [he]; simp only [mul_sub,sub_mul,mul_one,one_mul,Matrix.smul_mul, Matrix.mul_smul,hp.isIdempotentElem.eq]; module
  have ha:Safe A:=buysafe (show IsSelfAdjoint A from (by rw [he,isSelfAdjoint_iff,star_sub,star_smul,hp.isSelfAdjoint.star_eq]; simp)) (by rw [hx]; norm_num)
  change projector A=P; rw [projector,polarity_scalar ha 1 (by norm_num) (by simpa),he]; norm_num; module
lemma atmos (N:Side)(A:Momentum→Op SpinIdx): love N (fourImage Slot N (fun k=> A (mel k))) = plates N A ⊗ₖ (1:Op Slot) := by
  let X:= overU N SpinIdx; let C:= (X.val: Op (Site N×SpinIdx))
  have he:C ⊗ₖ (1:Op Slot)=love N (spatialU N Slot).val:=by
    ext ⟨⟨i,a⟩,l⟩ ⟨⟨k,b⟩,w⟩; simp only [loveAt,unityP,Matrix.submatrix_apply]
    simp [X,C,helix,spatialU,overU,Matrix.one_apply,ite_and,mul_ite,ite_mul]; grind
  have hx: mark N A ⊗ₖ (1:Op Slot)=love N (bands Slot fun k=>A (mel k)):=by
    ext ⟨⟨i,a⟩,l⟩ ⟨⟨k,b⟩,w⟩; simp [loveAt,unityP,helix,Rush.mark,bands,jump_apply,ite_mul]
  rw [show plates N A ⊗ₖ 1=(C ⊗ₖ (1:Op Slot))*(mark N A ⊗ₖ 1)*star (C ⊗ₖ 1) by rw [op_star_kron,star_one,op_kron_mul,mul_one,op_kron_mul,mul_one,plates, twist_formula]]
  rw [he,hx]; change love N (twist (spatialU N Slot) (bands _ _))=_; rw [twist_formula,map_mul,map_mul,map_star]
lemma flatBand (j:ℕ)(hj:1≤j)(N:Side): projector (dome N 1)=reserveP N j 1 1:=by
  let U: Bkg (More N):=1
  have hh: links U=1:=by funext z; simp [U,links]; -- inspect
  have hp:dome N 1=love N ((emptyFrame matter N).H):=by nth_rw 1 [← profile_trivial]; rw [dome_kernel, hh]; rfl
  have he := start_bar j
  rw [hp,oriented_love (emptyBand matter N),project_four,ptone N hj 1 odd_one,← atmos]; congr; exact funext fun i=> (he _).symm
end YM.CF.Tulip
