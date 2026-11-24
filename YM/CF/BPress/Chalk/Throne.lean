import YM.CF.BPress.Chalk.Script
/-! Site decomposition and mask using the pairs in the sector. Tube lift alpha v. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Chalk
open Function Filter Finset NormedSpace Fock SU SU.Pair Lattice Cube Lat Spin Spin.Paint Spin.Stride Spin.Hole Pf Dial Nacre Tulip Branch Bias Skye Fixed
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N:Side} (H:Paint (More N))(x:Site N){A:Op Slot}(S:Support N)
lemma snug (P:Op Slot) : Sector (den x) false (coupl (Yore x P)):=neatV (by
 let A:=shelf x; unfold Yore; have ht: A*A=A:= (cutM_idp _).isIdempotentElem.eq; rw [← mul_assoc A,← mul_assoc A,ht,mul_assoc _ A A,ht])
abbrev summitOp(x: Site N)(P: Op Slot): FC (Single N):= exp (coupl (Yore x P))
def proud (x: Site N):= occupy (upS x) (downS x)
def Dock(x:Site N):=occupy ∅ (den x)
def helm: PanelA N:=⟨proud, fun _=> neat_occupy (close_up ..) (close_up ..)⟩
def sail : PanelA N:=⟨fun x=> exp (coupl (regent H x)), fun x=> neatC (snug ..)⟩
def woven : PanelA N:= merge (pal S helm) (sail H)
local notation "ξ0"=>vacuum (Single N)
lemma coupl_plus {I:Type}[Fintype I][LinearOrder I](A B:Op I):coupl (A+B)=coupl A+coupl B:=by unfold coupl squareP; simp only [Matrix.add_apply,add_smul,sum_add_distrib,smul_add]
lemma sailing : exp (coupl (∑ x∈S,regent H x))= tomes S (sail H):=by
 have he(x:Site N)(A:Support N)(h:x∉A): Commute (coupl (regent H x)) (coupl (∑ i∈A,regent H i)):=by
    induction A using Finset.induction_on with| empty=> rw [sum_empty]; simp only [coupl,squareP,Matrix.zero_apply,zero_smul,sum_const_zero, smul_zero]; exact Commute.zero_right _| @insert i u v ih=> rw [sum_insert v,coupl_plus]; rw [mem_insert,not_or] at h; exact (neatN (snug x _) (snug i _) (disj_zone h.1)).add_right (ih h.2)
 letI : NormedAlgebra ℚ (FC (Single N)) := NormedAlgebra.restrictScalars ℚ ℂ (FC (Single N))
 induction S using Finset.induction_on with| empty=> simp [coupl,squareP]| @insert i u t ih=> rw [sum_insert t,coupl_plus, exp_add_of_commute (he i u t), brick _ _ i t, ih]; rfl
lemma movement:occupy (Locks S true) (Locks S false)=tomes S helm:=by
 rw [dorsal true S,dorsal false S] -- tune
 induction S using Finset.induction_on with | empty=> simp [occupy_0]| @insert i S h ih=> rw [biUnion_insert,biUnion_insert,occupy_κ,ih,brick _ _ i h]; rfl
lemma woven_unit : braC (Locks S true) (Locks S false) (coupling H)= acts (tomes univ (woven H S)) (vacuum _):=by
 rw [braC,woven,merge_prod,rent,univ_inter,←sailing, ←position_sea, ←movement,act_mul,stored] -- tune
abbrev pure (i:Site N): ℂ:=pf (Yore i 1) (upS i)
abbrev punctual (i: Site N):= pure i • basisKet (upS i)
lemma point_norm : ‖punctual x‖=1:=by
 have hs:Spin.Sym (1:Op Slot):=⟨Matrix.transpose_one,(unitary _).one_mem,Matrix.det_one⟩
 rw [punctual,norm_smul, pure, pf_go x hs]; simp [basisKet]
lemma patch_o {V:FC (Single N)}{b:Bool}(h:Sector (den x) b V){W:Finset (Single N)}(t:¬ W⊆ den x): (acts V (vacuum _)).ofLp W=0:=by
 obtain ⟨i,h',p⟩:= not_subset.mp t; rw [vacuum,basis_act]; by_contra g; exact notMem_empty i ((h.dotGrade _ _ g _ p).mpr h')

lemma markHere(e:Spin.Sym A): acts (proud x*summitOp x A) ξ0= punctual x:=by
 apply PiLp.ext; intro i; rw [act_mul,proud,cut_apply]; by_cases h:i=upS x; subst i; rw [if_pos (by have he:= outage ({x}:Support N); exact mem_filter.mpr ⟨mem_univ _,Subset.refl _,he⟩), summitOp,stored]; unfold punctual pure; rw [← home_swing x e]; simp; rfl -- tune
 unfold punctual; simp only [WithLp.ofLp_smul,Pi.smul_apply, basis_apply,h,ite_false,smul_zero]; split; next p=>
    apply patch_o x (neatC (snug ..)); obtain ⟨a,b⟩:= (mem_filter.mp p).2; intro t; apply h (Subset.antisymm ?_ a); intro j p; have hx:= t p; rw [← patch_duo, mem_union] at hx; exact hx.resolve_right (disjoint_left.mp b p)
 next p=> rfl
lemma condition_cut : occupy (Locks (univ:Support N) true) (Locks (univ:Support N) false)=lineOp (tickA N):=by
 let A:= Blank.tenureX N true; rw [← Blank.t_comp, Blank.tenureP,cutLine]; change _=cutM {A}; apply congrArg cutM; simp only [light]; ext i; simp only [mem_filter,mem_univ,true_and,mem_singleton]; have he : Locks (univ:Support N) true=A:=by ext i; simp [A,Locks]
 rw [he, show Locks (univ:Support N) false=Aᶜ from ?_, disjoint_compl_right_iff]; exact ⟨fun ⟨t,v⟩=> Subset.antisymm v t,fun p=>by rw [p] ; simp⟩; ext i; simp [A,Locks,Blank.tenureX,Blank.cup]
lemma woven_mate (p:MatPlan H): acts (tomes univ (woven H univ)) ξ0=mateK N:=by
 let x:Stun N:=vacuumW N; let N':Paint (More N):= fun i=> SU.Pair.fullM (hook x i); have h': MatPlan N':=fun i=> Spin.Sym.full _ (hookN ..)
 have he(G:Paint (More N))(p:MatPlan G)(x:Site N): acts ((woven G univ).val x) ξ0=punctual x:=by
    unfold woven merge; simp only [Pi.mul_apply,pal,mem_univ,ite_true]; exact markHere x (p (node x))
 rw [Chalk.reading (woven H univ) (woven N' univ) univ (fun i _=> (he H p _).trans (he N' h' _).symm),←woven_unit,braC,condition_cut,show coupling N'=spotC (hook x ∘ node) from rfl]; exact constB (hook x ∘ node) (fun _=> hookN ..) -- tune
-- Mark insertion
/-- Global expression for tensor `|b><p|` on a single site. final operator on BRA side is its star. See `triumphant`. -/
def pureUp(x:Site N)(A: Op Slot): FC (Single N):= let V:= summitOp x A; V*Dock x*star V*proud x
lemma pure_sect(A:Op Slot): Sector (den x) false (pureUp x A):= ( ( (neatC (snug x A)).mul (neat_occupy (empty_subset _) le_rfl)).mul (neatC (snug x A)).contr ).mul (helm.property x)
lemma shell_v {V:FC (Single N)}(p:Sector (den x) false V): acts (Dock x* V) ξ0= V ∅ ∅ • ξ0:=by
 apply PiLp.ext; intro i; rw [act_mul,Dock,cut_apply]; by_cases v:i=∅; · subst i; simp [vacuum,light]
 unfold vacuum; rw [WithLp.ofLp_smul, Pi.smul_apply, basis_apply, if_neg v, smul_eq_mul, mul_zero]; split; rename_i u; let f:= (mem_filter.mp u).2.2; apply patch_o x p; intro t; exact v (by ext j; simp only [notMem_empty,iff_false]; exact fun e=>disjoint_left.mp f e (t e)); rfl -- syntax
lemma triumphant(t:Spin.Sym A): acts (pureUp x A) (punctual x)= acts (summitOp x A) ξ0:=by
 let S:= summitOp x A; have hs:=neatC (snug x A); let G:=proud x; let q:= helm.property x; let h:IsStarProjection G:=cutM_idp _; let D:=star S * (G*S); have hd : Sector (den x) false D:= hs.contr.mul (q.mul hs)
 have he : D ∅ ∅=(1:ℂ):=by
    have hx:=markHere x t; rw [show D=star (G*S)*(G*S) by unfold D; rw [star_mul,h.isSelfAdjoint,mul_assoc,←mul_assoc G G,h.isIdempotentElem.eq]]
    rw [← basis_act (star (G*S)*(G*S)) ∅ ∅,← basis_inner,act_mul,←act_inner, star_star, inner_self_eq_norm_sq_to_K, show acts (G*S) (basisKet ∅)=_ from hx, point_norm]; simp
 have ho: pureUp x A*(G*S)= S*(Dock x* D):=by change S*_*star S*G*_= _; unfold D; rw [←mul_assoc, mul_assoc (S*_*star S) G G, h.isIdempotentElem.eq]; simp only [mul_assoc]
 rw [←markHere x t,← act_mul, ho, act_mul,shell_v x hd,he,one_smul] -- tune
end YM.CF.BPress.Chalk
