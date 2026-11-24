import YM.SU5.Selected.Prag.Riding
import YM.SU5.Selected.Actress.Altar
import YM.SU5.Selected.Actress.Scarves
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxHeartbeats 290000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
open Function Filter Metric Topology NormedSpace
open scoped BigOperators Kronecker InnerProductSpace ComplexOrder NNReal ENNReal Classical
variable {Γ:AddSubgroup ℝ} {A:Hilbert}{j:Axis}(P:Alliance (Trans j) Γ A) (dp:Dense (Γ:Set ℝ)) (S: OS.Semigroup A j)(q: ∀ i v t, Commute ((P.crew i).play v) (S.E t))
local notation "u" t:max=> S.E t
local notation "L₀"=> P
local notation "δ"=> dp
local notation "X"=> look j
local notation "T₀"=> (L₀).Realm X
local notation "Y"=> prism P
local notation "V"=> Frog P dp S q
open Spectral Spectral.Alps Function
local notation "Π"=> (P).aviator X
local notation "π"=> P.stackS (look j)
local notation "ι"=> Trans j
local notation "Ω" t:max=> (P.crew t).play
noncomputable def arise : (T₀).space→L[ℂ] A:= (Π).subtypeL
noncomputable def descendH : A→L[ℂ] (T₀).space:= (Π).orthogonalProjectionOnto
local notation "d"=> descendH P
local notation "R"=>arise P
lemma descends (x:A) : d x=Y x:= Subtype.ext (DFunLike.congr_fun (P.stack_ort.symm) x)
lemma descends_d (x:T₀) : d (arise P x)=x:= (Π).orthogonalProjectionOnto_mem_subspace_eq_self _
lemma propels(x:A) : R (d x)=π x:=congrArg R (P.descends x)
lemma cityH (x:T₀)(y:A) : inner ℂ (R x) y=inner ℂ x (d y):=by
 rw [P.descends]; change inner ℂ (x.val:A) _=inner ℂ (x.val:A) ((π) y); conv_lhs=> lhs; rw [←P.grounded X x.property]
 rw [←ContinuousLinearMap.adjoint_inner_right π,P.symmetricstack]
lemma coins(x:T₀) : ‖R x‖=‖x‖:=rfl
lemma rebuilt(x:A)(p:x∈ Π): R (Y x)=x:= P.grounded X p
lemma prism_full (x:T₀):Y (R x)=x:= (descends P (R x)).symm.trans (descends_d ..)
-- U_p √. notch formula intertwine resolve relative supports real directions
noncomputable def aSpot(v:Trans j)(x:Γ): OS.Cross j:= pours j fun i:Trans j=> if i=v then x.val else 0
local notation "τ"=> (V).U
local notation "φ"=> (V).E
lemma pointR {v:Trans j}(x:Γ)(p:Trans j→Γ)(L:List (Trans j))(h:L.Nodup)(e:∀ i∈L,p i = if i=v then x else 0) : P.raw L p= if v∈ L then (P.crew v).play x else 1:=by
 induction L with
 | nil=> simp [raw]; rfl
 | cons a L ih=> obtain ⟨hv,h⟩:=List.nodup_cons.mp h; rw [P.raw_step, ih h (fun i t=> e _ (List.Mem.tail _ t)), e a List.mem_cons_self]; by_cases t:a=v; · subst a; simp [hv]; rfl --
                 by_cases g:v∈L <;> simp [t,Ne.symm t,g,(P.crew a).play_zero] <;> try rfl
local notation "f" v:max=> P.raw X v
lemma spotR (v:Trans j)(p:Γ)(x:T₀) : R (τ (aSpot v p) x)= ((Ω v) p) (R x):=by
 let Z:Trans j→Γ:=fun i=> if i=v then p else 0
 have hz:(f Z)=(Ω v) p:=by rw [pointR P p Z X (look_one j) (fun i t=> rfl),if_pos (look_all j v)]
 have hp:aSpot v p= pours j (fun i=> (Z i).val):=by unfold aSpot; congr 1; funext i; unfold Z; split_ifs <;> rfl
 have he:R (Y (R x))= (R x):=congrArg R (prism_full ..)
 nth_rw 1 [←P.prism_full x]; rw [hp]; change _=(P.crew v).play p (R x); rw [←hz]
 exact (ray P dp S q Z (R x)).trans (congrArg (f Z) he)
lemma pulseR (t:ℝ≥0)(x:T₀): R (φ t x)= (S.E t) (R x):=rfl
-- intertwines Mink edge via analytic
lemma pointH (z:ℂ)(h:0≤ z.im)(x:T₀) : d (balcony S z (R x))= balcony V z x :=by
 apply ext_inner_left ℂ; intro y; rw [←P.cityH]; exact Alliance.twilight S V (R y) (R x) y x 1 1 (fun t=> (congrArg (inner ℂ (R y)) (pulseR P dp S q t x).symm)) z h -- defeq inner range. tune simpler use edge intertwiner
lemma pointH_full (z:ℂ)(h:0≤ z.im)(x:T₀): R (balcony V z x)= balcony S z (R x):=by
 apply ext_inner_left ℂ; intro y; -- transfer by equality at heat & MAGIC
 have hi(z:T₀): inner ℂ (d y) z=inner ℂ y (R z):= (inner_conj_symm (𝕜:=ℂ) ..).symm.trans ((congrArg (starRingEnd ℂ) (P.cityH z y).symm).trans (inner_conj_symm ..))
 rw [←hi]; exact Alliance.twilight V S (d y) x y (R x) 1 1 (fun t=> (hi ((V).E t x)).trans (congrArg (inner ℂ y) (pulseR P dp S q t x))) z h -- test defeq
-- singleton/vacuum normalization
variable (w:A)
def Follows (x:A):Prop:= ∀ i k, (P.crew i).play k x=x -- nonfull: implicit Space topology
include S q dp -- need remove below
variable (h:P.Follows w)
local notation "w₀"=> Y w
include h
omit S q dp in
lemma follows_mem : w∈ Π :=by
 refine (P.assembled ..).2 (fun i _=>?_); change ContinuousAt (fun k:Γ=>(Ω i) k w) 0; rw [show (fun k:Γ=>(Ω i) k w)=fun k=>w from funext (fun t=> h i t)]; exact continuousAt_const
lemma follows_full (x:OS.Cross j): τ x w₀=w₀:=by
 apply Subtype.ext; change P.flight dp X _ ((π) w) = (π) w; have hp: π w=w:=P.grounded X (P.follows_mem w h); rw [hp]
 have hl(c:ℝ)(i:Trans j): (P.crew i).route dp c w=w:=by
    have hr:(P.crew i).pi_c w=w:= (P.crew i).pi_fixer ((P.assembled ..).1 (P.follows_mem w h) _ (look_all j i))
    refine congrFun (dp.denseRange_val.equalizer ((P.crew i).route_uc dp w).continuous continuous_const (funext fun k=>?_)) c; exact ((P.crew i).route_on dp k w).trans ((congrArg ((P.crew i).play k) hr).trans (h i k))
 let α(i:Trans j): ℝ:= x.val i.val; suffices ht: ∀ L:List (Trans j), P.flight dp L α w=w from ht X; intro L; induction L with| nil=> rfl|cons i L ih=>rw[P.fly_step,ContinuousLinearMap.comp_apply,ih]; exact hl ..
lemma follows_heat (t:w∈ S.ground): w₀∈ (V).ground:= (OS.Semigroup.fixed _ _).2 (fun i=> (P.prism_early dp S q _ _).symm.trans (congrArg Y ((S.fixed _).1 t i))) -- p.dp field?
lemma follows_norm (p: ‖w‖=1) : ‖w₀‖=1:= (coins P (Y w)).symm.trans ((congrArg norm (P.rebuilt w (P.follows_mem w h))).trans p)
variable (v:∀ x:A,P.Follows x→(∀ t:ℝ,S.edge t x=x)→ ∃ c:ℂ,c • w=x)
include v
lemma fellows (x:T₀)(p:∀ i: OS.Cross j,(τ) i x=x)(e:∀ i:ℝ,(V).edge i x=x): ∃ c:ℂ,c • w₀=x:=by
 have ht(t:ℝ): R ((V).edge t x)= S.edge t (R x):=by simpa only [balcony_floor] using P.pointH_full dp S q t (by simp) x
 have hx:P.Follows (R x):=fun a i=> (P.spotR dp S q a i x).symm.trans (congrArg R (p _)); obtain ⟨c,u₁⟩:= v (R x) hx fun i=> (ht i).symm.trans (congrArg R (e _)); exact ⟨c,(congrArg (fun k=>c • k) (descends P w).symm).trans ( (map_smul d c w).symm.trans ((congrArg d u₁).trans (descends_d ..)))⟩ -- v inclusion? appears proof not type; include v
end YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
open YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
#print axioms descends_d
#print axioms pointH_full
#print axioms fellows
#print axioms follows_mem
#print axioms follows_full
#print axioms spotR
#print axioms pointH
