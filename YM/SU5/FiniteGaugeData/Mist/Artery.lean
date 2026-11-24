import YM.SU5.FiniteGaugeData.Mist.Chasm
/-! # Extend under paid true paths. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Mist
open Function Filter Metric Finset Lattice Hills
open scoped Topology BigOperators InnerProductSpace
variable {H:Hilbert}{L:Side}{a:Axis}(X:Terrace H L a)
local notation "R"=> VistaQ L
variable (b c:Axis)(u:VistaQ L)(s:ℕ)(k:ℤ)(B:List Axis)
def ScrollQ (b:Axis): Willow H (VistaQ L) where
 U:= ramble X b
 init:=ramble_zero ..
 both:=ramble_two X b
 keep:=ramble_price X b
abbrev Stamina (b:Axis) := (ScrollQ X b).Standard
-- list powers even if not nodup, order irrelevant
abbrev GroupR (X:Terrace H L a) : List Axis→ ClosedSubmodule ℂ H
 | [] => ⊤
 | b::v => GroupR X v ⊓ Stamina X b
abbrev Anteroom:= GroupR X Terrace.scheduleL
local notation "P₀"=> GroupR X
lemma sting (x:H):x∈ GroupR X B ↔ ∀ i∈ B, x∈ Stamina X i:= by induction B with
 | nil=> exact ⟨by simp, fun _=>trivial⟩
 | cons j b ih=> rw [GroupR,ClosedSubmodule.mem_inf,ih]; simp_rw [List.forall_mem_cons,and_comm]
include X
lemma cool_nick (g:Allows a c k): Commute (X.stepT s c k g) (planeP (Stamina X b)) := Willow.commute_pay (ScrollQ X b) fun y=> (ramble_cool s k X b c y g).symm -- order check
lemma ring_nick : Commute (ramble X b u) (planeP (Stamina X c)):= Willow.commute_pay _ fun t=> ramble_across X b c u t
lemma desk_nick : Commute (planeP (Stamina X b)) (planeP (Stamina X c)):= Willow.bankC _ _ (ramble_across X b c)
private lemma stylish : Commute (planeP (Stamina X b)) (B.map (fun i=> planeP (Stamina X i))).prod:= by induction B with
 | nil=> exact Commute.one_right _
 | cons i g ih=> exact (desk_nick X b i).mul_right ih
lemma seat_group : planeP (GroupR X B)=(B.map (fun i=> planeP (Stamina X i))).prod:= by induction B with
 | nil=> exact Submodule.starProjection_top'
 | cons i g ih=>
    rw [GroupR,inf_comm,infP,ih]; rfl; rw [ih]; exact stylish ..
lemma comm_Group {A:H.Op}(p:∀ a:Axis,Commute A (planeP (Stamina X a))): Commute A (planeP (GroupR X B)):=by
 rw [seat_group]; exact hop B
where hop (B:List Axis) : Commute A (B.map (fun i=> planeP (Stamina X i))).prod:= by induction B with
       | nil=>exact Commute.one_right _
       | cons i g ih=> exact (p i).mul_right ih
lemma pay_Group (g:Allows a c k): Commute (X.stepT s c k g) (planeP (P₀ B)):= comm_Group X B (fun b=> cool_nick X b c s k g)
lemma air_Group: Commute (ramble X b u) (planeP (P₀ B)):= comm_Group X B (fun i=> ring_nick X b i u)
lemma include_unity : X.Unity ≤ GroupR X B:=by
 intro x p; rw [sting]; intro i _; have he(v:R):ramble X i v x=x:=by
    unfold ramble; split; rfl; rename_i e; obtain ⟨n,k,rfl⟩:=(frequentT L v).exists; rw [Driver_eq]; exact (X.unityH _).1 p _ _ _ _
 change Tendsto (fun x'=> ramble X i x' x) (𝓝 0) (𝓝 x); simp_rw [he]; exact tendsto_const_nhds
local notation "M"=> CoreH (P₀ B)
-- utility calcs at general CLM
omit X
namespace Cot
variable {D:Hilbert}{P:ClosedSubmodule ℂ D}
lemma dip_fun {A:D.Op} (h:Commute A (planeP P)) : (dip P).comp A=(social P A).comp (dip P):=by ext1 x; apply Subtype.ext; have hp: planeP P * planeP P=planeP P:= withdraw (le_refl P); change planeP P (A x) = planeP P (A (planeP P x)); exact DFunLike.congr_fun (show planeP P * A=planeP P * (A*planeP P) from by rw [h.eq,←mul_assoc,hp]) x
lemma cpo_fun {A:D.Op}(h:Commute A (planeP P)): A.comp (cpo P)=(cpo P).comp (social P A):=by ext1 x; change A (cpo P x)= planeP P (A (cpo P x)); exact (congrArg A (inlet (among x)).symm).trans (DFunLike.congr_fun h.eq _)
lemma citizen {A B:D.Op}(h:Commute A (planeP P)): social P (A*B)=social P A*social P B:=by ext1 x; exact DFunLike.congr_fun (dip_fun h) (B (cpo P x))
end Cot
include X
-- build real U on Pc(B) in each axis i∈B
variable (z:1<L.val)(t:ℝ)
def inhouse (b:Axis) : Willow (CoreH (GroupR X B)) (VistaQ L) where
 U v:=social (GroupR X B) (ramble X b v)
 init:=by rw [ramble_zero,social_id]
 both r t:= by rw [ramble_two]; exact Cot.citizen (air_Group ..)
 keep x w:=by rw [← yen (social _ _ w),← show ramble X b x (cpo (GroupR X B) w)= cpo _ (social _ (ramble X b x) w) from DFunLike.congr_fun (Cot.cpo_fun (air_Group X b x B)) w,ramble_price]; rfl
local notation "ι" b:max=> inhouse X B b
lemma remnant {i:Axis}(p:i∈ B) (x:CoreH (GroupR X B)): x∈ (inhouse X B i).Standard:=by
 let F:=ScrollQ X i; have he:F.AllowsR (cpo (P₀ B) x):= (sting X B _).1 (among x) _ p
 have hx:Tendsto (fun k=> (ι i).U k x) (𝓝 0) (𝓝 (dip (P₀ B) (cpo (P₀ B) x))):= ((dip (P₀ B)).continuous.tendsto _).comp he
 rw [allC] at hx; exact hx
section
include z
omit X in
lemma vistas {G:Type*}[TopologicalSpace G][T2Space G](K J:ℝ→G)(p:Continuous K)(t:Continuous J)(w:∀ u:VistaQ L,K u=J u) : K=J:= funext fun i=> (indicate L z).dense.induction (by rintro _ ⟨v,rfl⟩; exact w v) (isClosed_eq p t) i
private abbrev expandR (i:Axis)(x: CoreH (GroupR X B)) := (indicate L z).extend (fun u=> (inhouse X B i).U u x)
private lemma expandU {i:Axis}(p:i∈ B)(x:CoreH (GroupR X B)) : UniformContinuous (expandR X B z i x) := uniformContinuous_uniformly_extend (show IsUniformInducing ((↑):VistaQ L→ℝ) from ⟨rfl⟩) (indicate L z).dense (Willow.admits _ x (remnant X B p x))
private lemma expandC {i:Axis}(p:i∈ B)(x:CoreH (GroupR X B)) : Continuous (expandR X B z i x):=(expandU X B z p x).continuous
private lemma expand_eq {i:Axis}(p:i∈ B)(x:CoreH (GroupR X B))(v:VistaQ L): expandR X B z i x (v:ℝ)=(ι i).U v x:= (indicate L z).extend_eq ((Willow.grammar _ _).1 (remnant X B p x)) v
private lemma keepR {i:Axis}(p:i∈ B)(x:CoreH (GroupR X B)): ‖expandR X B z i x t‖=‖x‖:= congr_fun (vistas z (fun t=> ‖expandR X B z i x t‖) (fun _=>‖x‖) (expandC X B z p x).norm continuous_const (fun u=> (congrArg norm (expand_eq X B z p x u)).trans ((ι i).keep _ x))) t
private def artery (i:Axis) (p:i∈B): (CoreH (GroupR X B)) →ₗᵢ[ℂ] (CoreH (GroupR X B)) where
 toFun x:= expandR X B z i x t
 map_add' x y:=by have he: (fun t=>expandR X B z i (x+y) t)=(fun t=> expandR X B z i x t+expandR X B z i y t):= vistas z _ _ (expandC X B z p _) ((expandC X B z p x).add (expandC X B z p y)) fun k=> by rw [expand_eq X B z p, expand_eq X B z p, expand_eq X B z p,map_add]
                  exact congr_fun he t -- indent
 map_smul' c x:= by
   let f:=expandR X B z i; change f (c • x) t=c • f x t; refine congr_fun (vistas z _ (fun t=>c • f x t) (expandC X B z p _) ((expandC X B z p _).const_smul c) fun i=> ?_) t; unfold f; rw [expand_eq X B z p,expand_eq X B z p, map_smul]
 norm_map' x:=keepR X B z t p x

def mistU (i:Axis)(p:i∈B): (CoreH (GroupR X B)).Op:= (artery X B z t i p).toContinuousLinearMap
local notation "Ω" t:max => mistU X B z t
variable {i:Axis}(p:i∈B)
lemma unit_eq (x:CoreH (GroupR X B)): mistU X B z t i p x=expandR X B z i x t:=rfl -- lemma priv
lemma unitC (x:CoreH (GroupR X B)): UniformContinuous fun t=> mistU X B z t i p x:= expandU X B z p x
lemma unitPaid (x:VistaQ L): mistU X B z (x:ℝ) i p=social (GroupR X B) (ramble X i x):= ContinuousLinearMap.ext fun y=>expand_eq X B z p y x
lemma unitInit : mistU X B z 0 i p=1:= (unitPaid X B z p 0).trans ((ι i).init)
lemma unitBoth (u':ℝ): mistU X B z (t+u') i p= (Ω t) i p *(Ω u') i p:=by
 apply ContinuousLinearMap.ext; intro x; refine congr_fun (vistas z (fun t=> (Ω (t+u')) i p x) (fun t=> (Ω t) i p ((Ω u') i p x)) ((unitC X B z p x).continuous.comp (continuous_id.add continuous_const)) (unitC X B z p ((Ω u') i p x)).continuous (fun r=> ?_)) t; refine congr_fun (vistas z (fun u=> (Ω ((r:ℝ)+u)) i p x) (fun u=>(Ω (r:ℝ)) i p ((Ω u) i p x)) ((unitC X B z p x).continuous.comp (continuous_const.add continuous_id)) (((Ω (r:ℝ)) i p).continuous.comp (unitC X B z p x).continuous) (fun v=>?_)) u'; change (Ω (((r+v:R):ℝ))) i p x = (Ω (r:ℝ)) i p ((Ω (v:ℝ)) i p x); rw [unitPaid,unitPaid,unitPaid]; exact ((ι i).both_inner r v x).symm

def WindR : Willow (CoreH (GroupR X B)) ℝ where
 U t:= mistU X B z t i p
 init:=unitInit ..
 both m n:=unitBoth X B z m p n
 keep t x:= keepR X B z t p x -- defeq
lemma unitDuty (x:CoreH (GroupR X B)): (WindR X B z p).AllowsR x := ((WindR X B z p).grammar x).2 (unitC X B z p x).continuous
lemma unitInter {U:H.Op}(g:∀ t, Commute (ramble X i t) U): Commute (mistU X B z t i p) (social (GroupR X B) U):=by
 -- need U comm P_all for multiplication reverse. use citizen and reverse commute with P from ramble, sufficient. add citizen'.
 let L':= social (P₀ B) U; apply ContinuousLinearMap.ext; intro y; refine congr_fun (vistas z (fun u=>(Ω u) i p (L' y)) (fun u=>L' ((Ω u) i p y)) (unitC X B z p _).continuous (L'.continuous.comp (unitC X B z p y).continuous) (fun i'=>?_)) t; rw [unitPaid]; rw [← mul_apply_eq_comp,← mul_apply_eq_comp]; apply DFunLike.congr_fun
 let V:=ramble X i i'; let P:= planeP (P₀ B)
 unfold L'; rw [← Cot.citizen (air_Group X i _ B),← social_mul]; let A:= P₀ B; change social A (V*U)= social A (U*P*V)
 have h:=g i'; rw [show V*U=U*V from h.eq, mul_assoc U, ←show V*P=P*V from (air_Group X i i' B).eq]
 ext1 w; change dip A (U (V (cpo A w)))= dip A (U (V (P (cpo A w)))); rw [show P (cpo A w)=cpo A w from inlet (among w)]
lemma unitAcross (h:b∈B)(u:ℝ): Commute (mistU X B z t i p) (mistU X B z u b h):=by
 ext1 w; let A:=(Ω t) i p; change A ((Ω u) b h w)= (Ω u) b h (A w)
 refine congr_fun (vistas z (fun u=> A ((Ω u) b h w)) (fun u=> (Ω u) b h (A w)) (A.continuous.comp (unitC X B z h w).continuous) (unitC X B z h (A w)).continuous (fun i'=> ?_)) u; rw [unitPaid]; exact DFunLike.congr_fun (unitInter X B z t p (fun t=> ramble_across X i b t i')).eq _
lemma unitNorm : ‖mistU X B z t i p‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>(((WindR X B z p).keep t x).trans (one_mul ..).symm).le)
end
end YM.CF.Buffered.Afterglow.Hierarchy.Mist
