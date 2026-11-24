import YM.CF.DPress.Chess.Lift.Sieve
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess.Print
open Function Filter Finset Lattice Rush Scroll Tulip Lat Dial SU Branch Wilson Fock Fixed NormedSpace Spire Scree Skye Tap Reed
open Cube (More)
open scoped Topology BigOperators NNReal ENNReal Kronecker Classical Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I X:Type*}[Fintype I][LinearOrder I]{s t:Finset I}{u:Wave I}{A B C:FC I}{b:Bool}{n:Side}
lemma linear_basis [NormedAddCommGroup X][NormedSpace ℂ X][FiniteDimensional ℂ X](S:Submodule ℂ X):∃ (N:ℕ)(σ:Fin N→ X→L[ℂ]ℂ)(g:Fin N→ S),∀ x∈S,x=∑ i,σ i x • (g i).val:=by
 let b:= Module.finBasis ℂ S; obtain ⟨F,p⟩:= S.subtype.exists_leftInverse_of_injective S.ker_subtype; let v:=Module.finrank ℂ S; let f(i:Fin v):X→ₗ[ℂ] ℂ:= (b.coord i).comp F; refine ⟨v,fun i=> (f i).toContinuousLinearMap,b,?_⟩ -- tune syntax nonrecord
 intro x y; let t: S:=⟨x,y⟩; have ht: F x=t:= DFunLike.congr_fun p t; rw [← show (S.subtype t)=x from rfl]; refine Eq.trans (congrArg S.subtype (b.sum_repr t).symm) ?_; rw [map_sum]; refine sum_congr rfl (fun i _=>?_); rw [map_smul]; change b.repr t i • _= b.repr (F x) i • _; rw [ht]; rfl
def spaceS (s:Finset I)(b:Bool):Submodule ℂ (FC I) where
 carrier := fun A=> Sector s b A
 zero_mem' := Sector.zero b
 add_mem':= fun p q=> Sector.add p q
 smul_mem' := fun c x p=> Sector.scale p c
abbrev spaceE (s t:Finset I)(b:Bool):Submodule ℂ (FC I) where
 carrier := fun A=> Fine s t b A
 zero_mem' := Fine.empty _
 add_mem' := fun p q=> Fine.add p q
 smul_mem' := fun i x p=> Fine.scale p i
lemma fEqual {J:Type*}(S:Finset J){A B:J→ FC I}(p:∀ i, Equal u (A i) (B i)): Equal u (∑ i ∈S,A i) (∑ i∈ S,B i):=by unfold Equal; rw [star_sum,star_sum,act_sum,act_sum]; exact Finset.sum_congr rfl (fun i _=> p i)
lemma lack (s t:Finset I)(b:Bool):∃ F: FC I→L[ℂ] FC I,(∀ A,Fine s t b (F A))∧∀ x,Sector t b x → Equal (basisKet s) x (F x):=by
 obtain ⟨N,f,g,t'⟩:= linear_basis (spaceS t b); choose y p e using fun i:Fin N=> prime (s:=s) (A:=(g i).val) (show Sector _ _ _ from (g i).property); let H:= ∑ i:Fin N,(f i).smulRight (y i); have hg(A:FC I):H A=∑ i: Fin N,f i A • y i:=by simp only [H,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply]
 refine ⟨H, fun x=>by rw [hg]; exact Fine.sumF _ _ (fun i _=>(p i).scale _), fun x p=>?_⟩; rw [hg]; nth_rw 1 [t' x p]; exact fEqual _ (fun i=> colorT (e i) _)
lemma Theta_ready (U:UNI I)(p: twist U (cutM s)=1-cutM s)(v:Sea (cutM s) u)(h: Equal u A B): Equal u (theta U A) (theta U B):=by
 let g(X:Wave I):= arum U false true u X; have he : g u=u:= arum_self _ _ _ _ v p; have hg(A:FC I):g (acts (star A) u)=acts (star (theta U A)) u:=by unfold g; rw [←theta_star]; exact ((arum_act U false true u u _)).trans (congrArg (acts _ ) he) -- tune
 unfold Equal; rw [←hg,←hg,h]
abbrev ψθ(x:Shape)(v:UNI SpinIdx)(N:Side) := prepU x v inert N
lemma τ_p(x: Shape)(v:UNI SpinIdx)(p:JetS x.s false true v): twist (ψθ x v n) (cutM (Fixed.upperIndices n))=1-cutM (Fixed.upperIndices n):=by rw [←Fixed.Tset_upperIndices]; exact Spire.tickR x inert v p n
lemma Θ_member {P Q:FC (Single n)} (x:Shape)(v:UNI SpinIdx)(p:JetS x.s false true v) (t:Equal (mateK n) P Q) :Equal (mateK n) (theta (ψθ x v n) P) (theta (ψθ x v n) Q) := Theta_ready (ψθ x v n) (τ_p x v p) (Fixed.tickA_upper _ ▸ tickB _) t
end YM.CF.DPress.Chess.Print
