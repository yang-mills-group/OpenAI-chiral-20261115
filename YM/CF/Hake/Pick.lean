import YM.CF.Hake.Pep
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hake
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
variable {ι I J n m r e:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m][LinearOrder r][Fintype r]{F:Oboe n→FC m}(p:Restart F)
abbrev WarpB(n:Type*):= Finset n × Finset n → ℂ
abbrev wontL:WarpB n→ₗ[ℂ]FC m:={ toFun:=wont p,map_add':=wont_s p,map_smul':=fun c v=>wont_c p v c }
def hope(n:Type*)[LinearOrder n][Fintype n] : WarpB n≃ₗ[ℂ] FC n:=by
 let P:= wontL (orchestra (n:=n)); have he(v): P v=pour v:= by change ∑ _,_= _; simp [playB,pour]
 have hi: Injective P:= fun _ _ g=> piano_same (by simp_rw [he] at g; exact g)
 refine LinearEquiv.ofBijective P ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hi⟩
 change _ = Module.finrank ℂ (Matrix (Finset n) (Finset n) ℂ); rw [Module.finrank_matrix]; simp [WarpB]
lemma hope_v(W:List (Oboe n)): (hope n).symm (rollC bell W)=chase W:=by
 have he: hope n (chase W)=rollC bell W:= chasing orchestra W; rw [←he,LinearEquiv.symm_apply_apply]
def hail : FC n →ₗ[ℂ] FC m := (wontL p).comp (hope n).symm.toLinearMap
lemma hailW (W:List (Oboe n)): hail p (rollC bell W)=rollC F W:= by change wont p ((hope n).symm (rollC bell W))=_; rw [show (hope _).symm (rollC _ _)=_ from hope_v W,chasing p]
lemma chant(P:Poly r m)(W:List r):P.eval (rollC put W)=rollC P.term W:=by
 induction W with
 | nil=> exact P.eval_one
 | cons i W ih=>
    rw [show rollC _ _=put i*rollC put W from rfl,fireT P ?_ ?_]
    · rw [ih]; exact congrArg (fun x=> x * rollC P.term W) ((congrArg _ (Poly.tag_once (cane r) i).symm).trans ((P.eval_oneT _).trans (Poly.tag_once _ _))) -- tune
    · rw [show put i=poke {i} from (Poly.tag_once (cane r) i).symm]; exact spanPt _
    · clear ih; induction W with| nil=> exact grandP | cons j t H=> exact spanT ((show put j=poke {j} from (Poly.tag_once (cane r) j).symm) ▸ spanPt _) H -- tune
variable [LinearOrder ι][Fintype ι]
section
variable (K:ι→ι→ℂ)(L:ι→m→ℂ)(pr: r→ι)(pb: Oboe n→ι)(hp:∀ i j,K (pr i) (pr j)+K (pr j) (pr i)=0)(hh:∀ i j,K (pb i) (pb j)+K (pb j) (pb i)= if i=revertP j then 1 else 0)
def cupP : Poly r (LinkI ι m):=⟨(largeH L+smallH K) ∘ pr, fun i j=> by rw [Function.comp_apply,Function.comp_apply,clash L K]; unfold Stilo.price; rw [←add_smul,hp i j,zero_smul]⟩
include hh
lemma hhP : Restart (n:=n) ((largeH L+smallH K) ∘ pb):= by intro i j; rw [Function.comp_apply,Function.comp_apply, clash L K]; unfold Stilo.price; rw [←add_smul, hh]; split_ifs; rw [one_smul]; rw [zero_smul]
def pet (f: FC r)(g:FC n): FC m:= let A:=(cupP K L pr hp).eval f * hail (hhP K L pb hh) g; let u:= pailL seenH ∅ (acts A (pod _)); ∑ i:Finset m,(u.ofLp i) • poke i
include hp
lemma pitch_s(f:FC r)(g:FC n):spanP m (pet K L pr pb hp hh f g):= snack fun i _=> spanS (spanPt _) _
lemma pet_r (u:List r)(b:List (Oboe n)):let F:=rollC put u; let G:=rollC bell b; taskC (lank L) (price K m) (u.map pr ++ b.map pb)=pet K L pr pb hp hh F G:=by
 intro f g; let T:= taskC (lank L) (price K m) (u.map pr ++ b.map pb)
 apply Eq.trans (rent_m ..) -- ambiguous T impl;
 let A:=largeH L+smallH K; have he(x:FC m)(i): crumb x i=(acts x (pod m)).ofLp i:= (basis_act _ _ _).symm; refine sum_congr rfl fun i _=>?_ ; rw [he,pitchA]; unfold f g; rw [chant, hailW]; unfold chime rollC; simp only [List.map_append,List.map_map,List.prod_append]; rfl
lemma pet_add1(f e:FC r)(g:FC n):pet K L pr pb hp hh (f+e) g=pet K L pr pb hp hh f g+pet K L pr pb hp hh e g:=by
 unfold pet; simp_rw [map_add,add_mul,act_add,map_add,WithLp.ofLp_add,Pi.add_apply,add_smul,sum_add_distrib]
lemma pet_add2 (f:FC r)(g u:FC n):pet K L pr pb hp hh f (g+u)=pet K L pr pb hp hh f g+pet K L pr pb hp hh f u:=by
 unfold pet; simp_rw [map_add,mul_add,act_add,map_add,WithLp.ofLp_add,Pi.add_apply,add_smul,sum_add_distrib]
lemma pet_c1 (f:FC r)(g:FC n)(x:ℂ):pet K L pr pb hp hh (x • f) g=x • pet K L pr pb hp hh f g:=by unfold pet; simp [Algebra.smul_mul_assoc,smul_sum,mul_smul]
lemma pet_c2 (f:FC r)(g:FC n)(x:ℂ):pet K L pr pb hp hh f (x • g)=x • pet K L pr pb hp hh f g:=by unfold pet; simp [Algebra.mul_smul_comm,smul_sum,mul_smul]
def petL : FC r →ₗ[ℂ] FC n →ₗ[ℂ] FC m where
 toFun f:={ toFun:=pet K L pr pb hp hh f,map_add':=pet_add2 K L pr pb hp hh f,map_smul':= fun c x=> pet_c2 K L pr pb hp hh f x c }
 map_add' x y:=LinearMap.ext fun i=>pet_add1 K L pr pb hp hh x y i
 map_smul' c x:=LinearMap.ext fun i=>pet_c1 K L pr pb hp hh x i c
end
end YM.CF.Hake
