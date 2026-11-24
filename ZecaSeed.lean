import YM.SU5.FiniteGaugeData.Poin.Gust
import ZecaWeld
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder

open Poin
variable {ι:Type}{H:Hilbert}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)(z:H.space)

abbrev Keeps (C:Submodule ℂ H.space)(A:H.Op) := ∀ x∈ C,A x ∈ C
structure Stable (C:Submodule ℂ H.space) : Prop where
 closed : IsClosed (C:Set H.space)
 here : z ∈ C
 heat t : Keeps C (S.E t)
 space u : Keeps C (S.U u)
 invar p : Keeps C (G.dep p)

abbrev Filled :Prop := ∀ C,Stable S G z C → C=⊤
def Cove : Submodule ℂ H.space:= sInf {C| Stable S G z C}

local notation "J"=> Cove S G z
lemma secret : Stable S G z (Cove S G z):=by
 unfold Cove
 refine ⟨?_,Submodule.mem_sInf.mpr (fun _ p=> Stable.here p),?_,?_,?_⟩
 · rw [Submodule.coe_sInf]
   exact isClosed_iInter fun k=>isClosed_iInter fun p=>Stable.closed p
 · exact fun t x p=> Submodule.mem_sInf.mpr fun k v=>Stable.heat v t x (Submodule.mem_sInf.mp p k v)
 · exact fun u x p=> Submodule.mem_sInf.mpr fun k v=>Stable.space v u x (Submodule.mem_sInf.mp p k v)
 exact fun q x p=> Submodule.mem_sInf.mpr fun k v=>Stable.invar v q x (Submodule.mem_sInf.mp p k v)
instance Cove.full:CompleteSpace (Cove S G z):=(secret S G z).closed.completeSpace_coe
abbrev Grotto:Hilbert := ⟨J⟩
abbrev pilgrimV : (Grotto S G z).space:= ⟨z,(secret S G z).here⟩
abbrev restr (p:Submodule ℂ H.space)(A:H.Op)(q: Keeps p A): p→L[ℂ] p:=
 (A.comp p.subtypeL).codRestrict p fun x=> q x.val x.property
lemma appearance (p:Submodule ℂ H.space)[CompleteSpace p](A:H.Op)(q: Keeps p A)
 (g:Keeps p (star A)): star (restr p A q)= restr p (star A) g:=by
 ext1 x; apply ext_inner_right ℂ; intro y
 change inner ℂ ((restr p A q).adjoint x) _ = _
 rw [ContinuousLinearMap.adjoint_inner_left]
 exact (ContinuousLinearMap.adjoint_inner_left A y.val x.val).symm

abbrev springs : OS.Semigroup (Grotto S G z) timeAxis where
 E t:= restr J (S.E t) ((secret S G z).heat t)
 U u:= restr J (S.U u) ((secret S G z).space u)
 eZero:= by ext1 x; exact Subtype.ext (DFunLike.congr_fun S.eZero x.val)
 time:= by intro s t; ext1 x; exact Subtype.ext (DFunLike.congr_fun (S.time s t) x.val)
 shrinks:= by
   intro t; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
   intro x;exact ((S.E t).le_opNorm x.val).trans (mul_le_mul_of_nonneg_right (S.shrinks t) (norm_nonneg _))
 sym t:=by
   let A:=S.E t; let h:= (secret S G z).heat t
   have g: Keeps J (star A):=(show star A=A from S.sym _).symm ▸ h
   exact (appearance J A h g).trans (by ext1 x; exact Subtype.ext (DFunLike.congr_fun (S.sym t) x.val))
 uZero:= by ext1 x;exact Subtype.ext (DFunLike.congr_fun S.uZero x.val)
 space:=by intro s t; ext1 x;exact Subtype.ext (DFunLike.congr_fun (S.space s t) x.val)
 unitary u v:=S.unitary u v.val
 independent := by intro s t;ext1 x; exact Subtype.ext (DFunLike.congr_fun (S.independent s t) x.val)
 continuousE v:= continuous_induced_rng.mpr (S.continuousE v.val)
 continuousU v:= continuous_induced_rng.mpr (S.continuousU v.val)

lemma crystalline :Weld (springs S G z) S (Cove S G z).subtypeL:=⟨fun _ _=>rfl,fun _ _=>rfl⟩

abbrev chapel : Canopy (Grotto S G z) ι where
 P:=G.P
 flash w:=LinearMap.mkContinuous
   (σ:=RingHom.id ℂ)
   {toFun:=fun x=> restr J (G.flash w x) ((secret S G z).invar ⟨w,x⟩)
    map_add':=by intro x y;ext1 t;exact Subtype.ext (DFunLike.congr_fun (map_add (G.flash w) x y) t.val)
    map_smul':=by intro c x;ext1 t; exact Subtype.ext (DFunLike.congr_fun (map_smul (G.flash w) c x) t.val) }
   ‖G.flash w‖ fun x=>by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro t;exact ((G.flash w x).le_opNorm t.val).trans
       (mul_le_mul_of_nonneg_right ((G.flash w).le_opNorm x) (norm_nonneg _))
 duplex w x:=by
    let W:=G.flash w; have h:= (secret S G z).invar ⟨w,x⟩
    have g:Keeps J (star (W x)):=G.duplex w x ▸ ((secret S G z).invar ⟨w,(G.P w).dual x⟩)
    refine (Eq.trans ?_ (appearance J (W x) h g).symm)
    ext1 t;exact Subtype.ext (DFunLike.congr_fun (G.duplex w x) t.val)

lemma pilgrims:Filled (springs S G z) (chapel S G z) (pilgrimV S G z):=by
 intro V h; let D:=V.map (J).subtype
 have A:Stable S G z D:= by
   refine
    {closed:=(secret S G z).closed.isClosedEmbedding_subtypeVal.isClosedMap _ h.closed
     here:=⟨_,h.here,rfl⟩
     heat _:=?_
     space _:=?_
     invar _:=?_}
   · rename_i t; exact fun y ⟨x,p,k⟩=>⟨_,h.heat t _ p,by rw [←k];rfl⟩
   · rename_i t; exact fun y ⟨x,p,k⟩=>⟨_,h.space t _ p,by rw [←k];rfl⟩
   rename_i t; exact fun y ⟨x,p,k⟩=>⟨_,h.invar t _ p,by rw [←k];rfl⟩
 apply eq_top_iff.mpr;intro x _
 obtain ⟨y,p,k⟩:= (show x.val∈D from (Submodule.mem_sInf.mp x.property D A))
 exact show x∈V from (show y=x from Subtype.ext k) ▸ p
