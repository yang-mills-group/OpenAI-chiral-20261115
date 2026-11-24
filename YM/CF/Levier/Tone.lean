import YM.CF.Levier.Manse
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
include h
local notation "U"=>spinU b a.s
lemma tut(K:Branch.Tag (hall G e))(u:Bool)(l:K=pinH G e u)(g:Site (More P)→ E): steer G b a ((K.run g).val)= (K.run (starG b (a.broad G) g)).val:=by
 subst K; let W(x):=(pinH G e u|>.run x).val
 apply Epin G; rw [steer,port_back]
 let F(v:Hand G):=milU a U (xtra b) v.1; let X(g:Site (More P)→ E):= (W g).submatrix (abbe G).symm (abbe G).symm; have ht(g)(i j:Hand G):tap (X g) i j= if i=j then (1:Op SpinIdx)⊗ₖ (matter (g (meetH G u i))).val else 0:=by
    ext ⟨v,x⟩ ⟨r,y⟩; rcases i with ⟨z,q⟩; rcases j with ⟨p,j⟩
    cases u
    · change jump (Equiv.refl _) (fun i=> (spur G g i).val) ((z,q,v),x) ((p,j,r),y)= _; rw [jump_apply]; by_cases h:z=p <;> by_cases t:q=j<;>by_cases g:v=r<;>simp [h,t,g]; rfl
    change (temper G e|>.run g).val _ _= _; rw [temper_form]; -- tune
    change jump (Equiv.refl _) (fun i=> _) ((z,q,v),x) ((p,j,r),y)= _; rw [jump_apply]; by_cases h:z=p<;> by_cases t:q=j<;>by_cases g:v=r<;>simp [h,t,g]; rfl
 let T:=sings b (fros a G U (xtra b)) (X g); let y:=starG b (a.broad G) g
 suffices hx: ∀ i j:Hand G,tap T i j=tap (X y) i j by ext ⟨i,v⟩ ⟨j,w⟩; exact congr_fun (congr_fun (hx i j) v) w
 intro i j; unfold T fros; rw [tap_sg,ht,ht]; by_cases hp:i=j; swap; rw [if_neg hp,if_neg ((paceU ..).injective.ne hp),win_z,mul_zero,zero_mul]
 subst j; simp only [ite_true]; rw [meet_x G h]; change sings _ (milU a U (xtra b) _) _= _; rw [wingM,Scroll.wingK]; simp only [singT b U,win_i,map_one]; rw [←(xtra b).shore]; rfl -- tune
abbrev beamH (i:Hand G)(x:QuiltF):Iota G:=(abbe G).symm (i,x)
lemma wish_inv(k:Sweep N)(S:Seal (Site (More P))): toRoar G k (toRoar G k⁻¹ S)= S :=by rw [swept,mul_inv_cancel,sw_i]
lemma istrip(k:Sweep N){m:Type*}(z: m): (k⁻¹).charge=k.charge:=rfl
-- transport of single entries incl tags
local notation "π₀"=>paceU (castX k⁻¹) G
local notation "L₀"=>hall G e
lemma lineage(i j:Hand G)(l x: QuiltF)(S:Seal (Site (More P)))(V:ℝ)(F:cro G e→ ℂ)(hp:Expo L₀ S (beamH G (π₀ i) l) (beamH G (π₀ j) x) V F)(p q: QuiltF) : Expo L₀ (toRoar G k S) (beamH G i p) (beamH G j q) V (fun x=> cSignX (k.charge) (F (toWish G e k x))):=by
 have he(i: Hand G)(x:QuiltF): (L₀).home (beamH G i x)=meetH G true i:=rfl -- tune parser
 let R:=Shape.broad G (castX k⁻¹); have hv(i:Hand G)(a x:QuiltF)(l:(L₀).home (beamH G (π₀ i) a)∈ S): (L₀).home (beamH G i x) ∈ toRoar G k S:=by
    rw [he,meet_x G h] at l; rw [he]
    have hz:toRoar G k⁻¹ (toRoar G k S)= S:=by rw [swept,inv_mul_cancel,sw_i]
    rw [← hz] at l; obtain ⟨v,h',r⟩:= mem_image.mp l; rw [← R.anon_b.1 r]; exact h'
 have ht:Expo L₀ (toRoar G k S) (beamH G i p) (beamH G j q) V (F ∘ toWish G e k):= ⟨hp.positive,fun z=>⟨(prow P (Shape.broad G (castX k))).plus (hp.triggered z).1,hv i _ _ (hp.triggered z).2.1,hv j _ _ (hp.triggered z).2.2⟩,fun v=>hp.bounded _,fun y z=> (hp.variation (toWish G e k y) (toWish G e k z)).trans_eq (congr_arg _ (wish_e ..)),hp.connected.comp (cans ..)⟩ -- tune
 cases y:k.charge; exact ht; exact ht.dual
end YM.CF.Levier
