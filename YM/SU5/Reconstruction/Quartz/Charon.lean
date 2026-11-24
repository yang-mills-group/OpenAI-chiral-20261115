import YM.SU5.Reconstruction.Quartz.Zenith
import YM.SU5.Reconstruction.Trap.Horizon
/-!
# Moving the parameters in Club. Opp Observer rank.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Ship
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Picket CrossedFrame Clasp BridgeClub Anvil Waltz
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex
variable {H D K:Hilbert} (C:Clasp K H D)(F:H≃ₗᵢ[ℂ] D)
local notation "P"=> F.toContinuousLinearEquiv.toContinuousLinearMap
local notation "Q"=> F.symm.toContinuousLinearEquiv.toContinuousLinearMap
-- move the left port guarantee to D. No field charge on this shifted Clasp!
private lemma wedge_rev : ((P).comp C.l).adjoint.comp ((P).comp C.l) = C.angle :=by
 ext1 x; apply ext_inner_left ℂ; intro y; simp only [angle,ContinuousLinearMap.comp_apply,adjoint_inner_right]; exact LinearIsometryEquiv.inner_map_map ..
noncomputable def tug : Clasp K D D where
 l:= (P).comp C.l
 r:= C.r
 j:= F.injective.comp C.j
 k:= C.k
 p:= F.surjective.denseRange.comp C.p F.continuous
 q:= C.q
 frame:= by rw[wedge_rev];exact C.frame
local notation "T"=> tug C F
lemma tug_angle : (tug C F).angle=C.angle:= wedge_rev C F
lemma tug_Left : (T).Left=C.Left.trans F:= by
 apply DFunLike.ext; intro x; refine congrFun (a:=x) ((peel_dense C.l C.j).equalizer (T).Left.continuous (F.continuous.comp C.Left.continuous) ?_)
 funext x; have hx: peel C.l x=peel (T).l x:= DFunLike.congr_fun (show peel C.l=peel (T).l from congrArg CFC.sqrt (tug_angle C F).symm) x
 change (T).Left (peel C.l x)=F (C.Left _); rw [C.left_done,hx,Clasp.left_done]; rfl -- order
lemma tug_p : (tug C F).plume= F.conjStarAlgEquiv C.plume:= by rw [portAngle,tug_Left,tug_angle,portAngle C]; ext1 x; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
lemma tug_e : (tug C F).Cabin=C.Cabin:=by
  funext u; let p:(T).angle=C.angle:= tug_angle C F; have e:= Multiplier.compare_at ((T).motion) C.motion (1:K.Op) ((T).realF) C.realF ((T).measurable_realF) C.measurable_realF ((T).tagF) C.tagF ((T).angle_reads) C.angle_reads (show 1*(T).angle=C.angle*1 from by rw[p,one_mul,mul_one]) _ (river_price u); change 1* (T).Cabin u= C.Cabin u*1 at e; rwa [one_mul,mul_one] at e
lemma tug_b(t:ℝ):boost (tug C F) t= F.conjStarAlgEquiv (boost C t):=by rw[boost,cLeft,tug_Left,tug_e]; unfold boost cLeft; ext1 x; simp[LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
local notation "B₀"=> tug C C.look
lemma tug_backside : (tug C C.look).plume=C.Back.shadow:= by
 rw[tug_p,C.portAngle,shadow, portAngle, Back_Left, Back_angle,map_sub,map_one,sub_sub_cancel]; ext1 x; obtain ⟨x,rfl⟩:= C.Right.surjective x; simp[LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,look]
lemma turnaside (t:ℝ) : boost (tug C C.look) t=boost C.Back (-t):= by rw[tug_b, C.carryBoost]
lemma go (t:ℝ)(A:H.Op): ascend t (tug C F) (F.conjStarAlgEquiv A)=F.conjStarAlgEquiv (ascend t C A):=by simp only [ascend,tug_b,map_star,map_mul]
lemma run_inv (h:D.Op): F.conjStarAlgEquiv (F.symm.conjStarAlgEquiv h)=h:=by ext1 v; simp[LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
lemma run_base (h:H.Op): F.symm.conjStarAlgEquiv (F.conjStarAlgEquiv h)=h:=by ext1 v; simp[LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
-- Pull & merge
noncomputable def Pull (M:Net D) : Net H where
 toStarSubalgebra:=M.toStarSubalgebra.comap F.conjStarAlgEquiv.toStarAlgHom
 centralizer_centralizer':=by
    let F':= F.conjStarAlgEquiv; refine le_antisymm ?_ Set.subset_centralizer_centralizer; intro x h; change F' x∈ M; rw[←VonNeumannAlgebra.commutant_commutant M]; apply VonNeumannAlgebra.mem_commutant_iff.mpr; intro g p; obtain ⟨t,rfl⟩:= F.conjStarAlgEquiv.surjective g; have hp: F' t∈ M.commutant:=p; change F' t* F' x= F' x *F' t; rw [←map_mul,←map_mul]; apply congrArg; apply h _ -- tune
    intro a v; apply F.conjStarAlgEquiv.injective; exact (show F' (a*t)= F' (t*a) from by rw[map_mul,map_mul]; exact VonNeumannAlgebra.mem_commutant_iff.mp hp _ (show F' a∈ M from v))
lemma pulling(A:H.Op)(M:Net D) : A∈ Pull F M↔ F.conjStarAlgEquiv A ∈ M:= Iff.rfl
noncomputable def join (M N:Net H): Net H where
 toStarSubalgebra:= M.toStarSubalgebra⊓N.toStarSubalgebra
 centralizer_centralizer':=by
    refine le_antisymm ?_ Set.subset_centralizer_centralizer
    intro x h; change x∈ (M:Set H.Op)∧ x∈ (N:Set H.Op); rw[← M.centralizer_centralizer,← N.centralizer_centralizer]; refine ⟨fun i p=>h i (fun i d=> ?_),fun i p=>h i (fun i d=>?_)⟩; exact p i (show i∈ (M:Set H.Op) from d.1); exact p i (show i∈ (N:Set H.Op) from d.2) -- pair repr
lemma joining (M N:Net H)(A:H.Op) : A∈ join M N↔ A∈ M ∧ A∈ N:= Iff.rfl
end YM.Quartz.Ship
