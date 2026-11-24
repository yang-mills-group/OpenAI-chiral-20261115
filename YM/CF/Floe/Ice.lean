import YM.CF.Floe.Ton
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
variable {N:Side}{a b c d r e:ℝ}{F G:pMat}{u v:Bool}
namespace LedgerP
lemma expV(h:LedgerP F u u):LedgerP (fun i x=> exp (F i x)) u u:= by
 obtain ⟨a,b,m,p,k,v,h⟩:=h; let V(n:ℕ):=‖(n.factorial:ℂ)⁻¹‖*(Real.exp a*(2*m)^n); refine keeps (a:=a) (c:=∑' i,V i) (fun i=>?_) p k
 rw [exp_eq_tsum ℂ]; refine Crown.tsK V (fun j=>((h i).powers p.le j).scale _) p.le ?_; refine (((norm_expSeries_summable' (𝕂:=ℂ) ((2*m:ℝ):ℂ)).mul_left (Real.exp a))).congr ?_
 intro i; rw [norm_smul,norm_pow, Complex.norm_real,Real.norm_of_nonneg (by positivity)]; unfold V; ring
lemma cert_drop(h:certS F u v a b r)(p:c≤a): certS F u v c b r:=fun i=>(h i).drop p
lemma opL(h:certS F u v a b r):certS (starL F) v u a b r:=fun i=>(h i).impose eθ eθ_o ele_e ema echo_valid
-- transpose lemma private mirror, reprove.
lemma mutA(h:certS F u v a b r):certS (fun i x=> (F i x)ᵀ) (!v) (!u) a b r:=by
 intro i; obtain ⟨G,C,p,V,h⟩:= h i; rw [←tag_other v, ← tag_other u]; refine ⟨_,_,fun i=>⟨(show Ticket _ _ i (Function.swap (C i)) (fun x=> (G i x)ᵀ) from ?_),fun j k=>(p i).fuel k j⟩,V.flip,?_⟩
 · convert! (p i).toTicket.starT.ccT using 2; funext z; unfold cc; rw [star_star]
 intro x; dsimp only; change ( (fun y=> F i (Subtype.val y)) x )ᵀ=_; rw [h x]; simp only [Matrix.transpose_sum] -- tune
lemma tagCt(h:certS F u v a b r):certS (tagC F) (!u) (!v) a b r:=mutA (opL h)
end LedgerP
open LedgerP Tour Enters
abbrev xD(z:Δ):FrameP z.1:= fun x=> decay (massB z x) 1
lemma death : LedgerP xD true true:=by
 let P:pMat:=fun i x=> polarity (massB i x); have ht:LedgerP P true true:=by
    let Q:=sub (scale_t σLp 2) (identL _); have hf:(fun (i: IndexK)(x:BayP i.1)=> (2:ℝ) • compB i x-1)=P:=by
       funext i x; unfold P; rw [compB,projector]; module
    exact hf ▸ Q
 exact expV (scale_t (times μLp ht) (-1))
lemma drift :∃ d b r c:ℝ, 0<d ∧ 0<b∧0<r∧0<c∧ c<1∧∀ n:ℕ, certS (xD^n) true true d b (r*c^n):=by
 let V:ℝ:=Real.exp (-1/2); exact powS _ death (Real.exp_lt_one_iff.mpr (by norm_num)) (Real.exp_pos (-1/2)|>.le) (fun i x=>by unfold xD; rw [mass_j]; exact slows (attends ..) _ zero_le_one)
-- Earning lifted
abbrev kPv :pMat:=mercy* compB
abbrev ePv :pMat:= -(kPv*kM false* tagC (1-compB))
abbrev qPv:pMat:=(1-compB)*(kM false-kM false*kPv*kM false)*tagC (1-compB)
section
variable(i:Δ)(x:Own i.1)
local notation "W"=>skin x.val
@[simp] lemma kPv_i:kPv i W=reserve (Pmat i x) (pairF false i x):=by change mercy i W*compB i W=_; rw [mercy_c,comp_j]; rfl
@[simp] lemma ePv_i:ePv i W=driftB (Pmat i x) (pairF false i x):=by unfold ePv kPv; simp only [Pi.neg_apply, Pi.sub_apply,Pi.one_apply,Pi.mul_apply,mercy_c,tag_my,comp_j,kM_y]; rfl
@[simp] lemma qPv_i:qPv i W=weldB (Pmat i x) (pairF false i x):=by unfold qPv kPv; simp only [Pi.sub_apply,Pi.one_apply,Pi.mul_apply,kM_y,tag_my,comp_j,mercy_c]; rfl
end
lemma κLp:LedgerP kPv false true:=times μCp σLp
lemma σPv:LedgerP ePv false false:=minus (times (times κLp (km false)) (ccL (sub (identL _) σLp)))
lemma θPv:LedgerP qPv true false:=by let h:=sub (identL _) σLp; exact times (times h (sub (km _) (times (times (km _) κLp) (km false)))) (ccL h)
end YM.CF.Floe
