import YM.CF.Stilo.Carter
set_option autoImplicit false
noncomputable section
namespace YM.CF.Stilo
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {ι I J n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
private abbrev feeC (F:ι→FC n)(u:Wave n)(i:Bout ι)(L:ι→ℂ):=cval i.neg • (L i.front) • chime F u i.back
lemma tune (G:ι→FC n)(L:ι→ℂ)(T:FC n)(x:Wave n)(h:acts T x=0)(p:∀ i,antiB T (G i)= L i • 1) (g:List ι) : acts T (chime G x g)= ((picks g).map (fun i=>feeC G x i L)).sum:=by
 induction g with
 | nil=> simp [picks,h]
 | cons i l ih=>
    rw [charm,←act_mul,show T*G i = L i • 1-G i*T from eq_sub_of_add_eq (p i),act_sub, act_smul,act_one,act_mul,ih,picks,List.map_cons,List.sum_cons,List.map_map]; let Q:=acts (G i) (((picks l).map fun j=> feeC G x j L).sum)
    have hp(k : Bout ι):feeC G x (beside i k) L=(-1:ℂ) • acts (G i) (feeC G x k L):=by rw [feeC,feeC]; dsimp only [beside]; rw [charm,map_smul,map_smul,cneg]; simp
    have hk:feeC G x (⟨false,i,l⟩:Bout ι) L=L i • chime G x l:=by simp [feeC,cval]
    rw [hk,show (fun j=>feeC G x j L) ∘ beside i=(fun j=> (-1:ℂ) • acts (G i) (feeC G x j L)) from funext hp,←desc (-1) _ (fun j=> acts (G i) (feeC G x j L)),←cact]; simp [sub_eq_add_neg]
def price (L:ι→ι→ℂ)(n:Type*)[LinearOrder n][Fintype n](i j:ι):FC n:= L i j • 1
lemma side(L:ι→ι→ℂ)(i j:ι)(b:Bool): (if b then -price L n i j else price L n i j)= cval b • L i j • 1 :=by cases b<;> simp [price,cval]
lemma devote (F G H:ι→ FC n)(Q:ι→FC m)(p:Wave n)(U: Wave n→L[ℂ] Wave m)(L:ι→ι→ℂ)(w:F=G+H)(ht:∀ i, acts (H i) p=0)(hv:∀ i j,antiB (H i) (F j)=price L n i j)(hp:∀ i x,U (acts (G i) x)=acts (Q i) (U x))(l:List ι): U (chime F p l)=acts (taskC Q (price L m) l) (U p):=by
 suffices hk:∀ k l,l.length<k→ U (chime F p l)=acts (taskC Q (price L m) l) (U p) from hk _ l (Nat.lt_add_one _)
 intro k; induction k with
 | zero=>intro _ _; omega
 | succ k ih=> intro l hl; cases l with
            | nil=> simp only [emptyChime,task_zero,act_one]
            | cons i l=>
                simp only [List.length_cons] at hl; rw [charm,show F i= _ from congrFun w i]; change U (acts (G i + H i) _)=_; let I:= picks l; let R:=taskC Q (price L m)
                rw [act_add, tune F (L i) (H i) _ (ht i) (hv i),U.map_add,hp,task_one,act_add,act_mul,ih _ (by omega),map_list_sum]; apply congrArg; -- tune
                let f(x:Bout ι):=(if x.neg then -price L m i x.front else price L m i x.front)* R x.back
                have hk (l:List (Bout ι))(f:Bout ι→FC m)(v:Wave m): ((l.map (fun i=> acts (f i) v)).sum)=acts ((l.map f).sum) v:=by induction l with | nil=>simp | cons i g h=>simp [act_add,h]
                rw [← hk (picks l), List.map_map]; congr 1; apply List.map_congr_left; intro a h; have hx:=ih a.back (by have hh:= picks_mem h; omega); simp only [Function.comp_apply,side,act_mul,act_smul,act_one]; unfold feeC; rw [map_smul,map_smul,hx] -- tune U' type
end YM.CF.Stilo
